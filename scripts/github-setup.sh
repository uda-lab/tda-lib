#!/usr/bin/env bash
# Idempotent GitHub bootstrap for a repository created from this template:
#   - the labels the workflow skills key on (hard stops, execution authorisation, priority);
#   - the `develop` and `main` rulesets: PR required, branch-specific merge methods, required status check `check`,
#     no deletion / force push (needs admin on the repo — the creator of an org repo has it;
#     otherwise this step reports and the owner runs it);
#   - squash topics and merge-commit propagation on develop; merge commits on main;
#     retain both long-lived branches.
# This is a broad bootstrap, not a targeted live-repair command. Existing rulesets are
# validated, not rewritten; labels/repository defaults and missing rulesets are broader
# mutations. Apply only the fields authorised for the current task, not this whole script.
# Pass the repo as owner/name, or run inside the clone.
set -euo pipefail

REPO="${1:-$(gh repo view --json nameWithOwner --jq .nameWithOwner)}"

echo "==> labels on $REPO"
while IFS='|' read -r name color desc; do
  gh label create "$name" --repo "$REPO" --color "$color" --description "$desc" --force >/dev/null
  echo "    $name"
done <<'EOF'
agent:ready|0E8A16|Execution authorised: owner/authorised maintainer audited scope and acceptance criteria
needs-decision|B60205|Hard stop: unresolved decision on governing Issue
blocked|B60205|Hard stop: cannot proceed until the blocker is cleared
do-not-merge|B60205|Hard stop: this PR must not be merged
priority:P0|D93F0B|Highest priority
priority:P1|FBCA04|Normal priority
priority:P2|C2E0C6|Low priority
formalization|5319E7|Source-anchored mathematical target
infrastructure|0052CC|Tooling, CI, hooks, repository maintenance
EOF

echo "==> merge settings"
gh api -X PATCH "repos/$REPO" -F allow_squash_merge=true -F allow_merge_commit=true \
  -F allow_rebase_merge=false -F delete_branch_on_merge=false >/dev/null && echo "    squash topics, merge-commit propagation/releases, retain long-lived branches"

for branch in develop main; do
methods='["squash","merge"]'
if [ "$branch" = main ]; then methods='["merge"]'; fi
echo "==> ruleset $branch"
existing="$(gh api "repos/$REPO/rulesets" --jq ".[] | select(.name == \"$branch\") | .id" 2>/dev/null | head -1)"
if [ -n "$existing" ]; then
  # An existing ruleset is only accepted if it actually enforces the contract; otherwise the
  # setup fails with the explicit owner action rather than reporting a protected repository.
  problems="$(gh api "repos/$REPO/rulesets/$existing" --jq '
    "refs/heads/'"$branch"'" as $ref |
    '"$methods"' as $methods |
    [ (if .enforcement != "active" then "enforcement is \(.enforcement), not active" else empty end),
      (if (.conditions.ref_name.include | index($ref)) == null then "does not target the protected branch" else empty end),
      (if ([.rules[] | select(.type == "pull_request")] | length) == 0 then "no pull_request rule (direct pushes allowed)" else empty end),
      (if ([.rules[] | select(.type == "pull_request") | .parameters.allowed_merge_methods | sort] == [($methods | sort)]) then empty else "incorrect allowed merge methods" end),
      (if ([.rules[] | select(.type == "deletion")] | length) == 0 then "no deletion rule" else empty end),
      (if ([.rules[] | select(.type == "non_fast_forward")] | length) == 0 then "no non_fast_forward rule (force pushes allowed)" else empty end),
      (if ([.rules[] | select(.type == "required_status_checks") | .parameters.required_status_checks[]? | select(.context == "check")] | length) == 0 then "status check `check` is not required" else empty end)
    ] | join("; ")')"
  if [ -z "$problems" ]; then
    echo "    exists — verified (active, protected branch, PR required, no force push, check required)"
  else
    echo "    EXISTS BUT DOES NOT ENFORCE THE CONTRACT: $problems" >&2
    echo "    owner action: edit ruleset '$branch' (id $existing) on $REPO to: active; target refs/heads/$branch; PR required; allowed merge methods $methods; no force push/deletion; required status check 'check'" >&2
    exit 1
  fi
else
  if gh api -X POST "repos/$REPO/rulesets" --input - >/dev/null <<EOF
{
  "name": "$branch",
  "target": "branch",
  "enforcement": "active",
  "conditions": {"ref_name": {"include": ["refs/heads/$branch"], "exclude": []}},
  "rules": [
    {"type": "deletion"},
    {"type": "non_fast_forward"},
    {"type": "pull_request", "parameters": {"required_approving_review_count": 0, "dismiss_stale_reviews_on_push": false, "require_code_owner_review": false, "require_last_push_approval": false, "required_review_thread_resolution": false, "allowed_merge_methods": $methods}},
    {"type": "required_status_checks", "parameters": {"strict_required_status_checks_policy": false, "required_status_checks": [{"context": "check"}]}}
  ]
}
EOF
  then echo "    created"
  else echo "    NOT created (admin required) — owner action: create ruleset '$branch' (PR required, methods $methods, required check 'check')" >&2; exit 1; fi
fi

done
echo "GITHUB SETUP OK"
