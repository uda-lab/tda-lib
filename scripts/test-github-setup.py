#!/usr/bin/env python3
"""Exercise setup merge-method validation/creation against a local gh fixture."""

import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
if shutil.which("jq") is None:
    raise SystemExit("jq is required to evaluate the setup script's actual queries")

FAKE_GH = r'''#!/usr/bin/env python3
import json, os, subprocess, sys
from pathlib import Path
a = sys.argv[1:]
root = Path(os.environ["TDA_SETUP_FIXTURE"])
data = json.loads((root / "fixture.json").read_text())
body = sys.stdin.read() if "--input" in a else ""
with (root / "calls.jsonl").open("a") as f:
    f.write(json.dumps({"args": a, "body": body}) + "\n")
if a[:2] == ["label", "create"]:
    sys.exit(0)
if not a or a[0] != "api":
    raise SystemExit("unsupported fake gh invocation")
endpoint = a[1] if not a[1].startswith("-") else a[3]
method = a[a.index("-X") + 1] if "-X" in a else "GET"
if method == "PATCH" and endpoint == "repos/uda-lab/fixture":
    sys.exit(0)
if method == "POST" and endpoint == "repos/uda-lab/fixture/rulesets":
    json.loads(body)
    sys.exit(0)
if method != "GET":
    raise SystemExit("unexpected mutation in fake gh")
if endpoint == "repos/uda-lab/fixture/rulesets":
    value = [{"id": x["id"], "name": x["name"]} for x in data]
else:
    value = next(x for x in data if endpoint == "repos/uda-lab/fixture/rulesets/" + str(x["id"]))
if "--jq" in a:
    result = subprocess.run(["jq", "-r", a[a.index("--jq") + 1]],
        input=json.dumps(value), text=True, capture_output=True)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    sys.exit(result.returncode)
print(json.dumps(value))
'''


def ruleset(branch, methods):
    return {
        "id": 1 if branch == "develop" else 2,
        "name": branch,
        "enforcement": "active",
        "conditions": {"ref_name": {"include": ["refs/heads/" + branch], "exclude": []}},
        "rules": [
            {"type": "deletion"},
            {"type": "non_fast_forward"},
            {"type": "pull_request", "parameters": {"allowed_merge_methods": methods}},
            {"type": "required_status_checks", "parameters": {
                "required_status_checks": [{"context": "check"}]}},
        ],
    }


def run_case(name, fixture, success, expected_error=""):
    with tempfile.TemporaryDirectory(prefix="tda-setup-test-") as directory:
        tmp = Path(directory)
        (tmp / "fixture.json").write_text(json.dumps(fixture))
        fake = tmp / "gh"
        fake.write_text(FAKE_GH)
        fake.chmod(0o755)
        env = os.environ.copy()
        env["PATH"] = str(tmp) + os.pathsep + env["PATH"]
        env["TDA_SETUP_FIXTURE"] = str(tmp)
        result = subprocess.run(["bash", str(ROOT / "scripts/github-setup.sh"), "uda-lab/fixture"],
            cwd=ROOT, env=env, text=True, capture_output=True)
        assert (result.returncode == 0) == success, (name, result.stdout, result.stderr)
        assert expected_error in result.stdout + result.stderr, (name, result.stdout, result.stderr)
        calls = [json.loads(line) for line in (tmp / "calls.jsonl").read_text().splitlines()]
        # The production bootstrap is broad, but this fixture cannot call the real gh.
        # Existing rulesets must never be rewritten to repair a failed validation.
        assert all("PUT" not in x["args"] and "DELETE" not in x["args"] for x in calls)
        created = [json.loads(x["body"]) for x in calls if "POST" in x["args"]]
        if fixture:
            assert not created, (name, created)
        else:
            assert len(created) == 2
            for payload in created:
                pr = next(r for r in payload["rules"] if r["type"] == "pull_request")
                want = ["squash", "merge"] if payload["name"] == "develop" else ["merge"]
                assert pr["parameters"]["allowed_merge_methods"] == want
                assert payload["enforcement"] == "active"
                assert {r["type"] for r in payload["rules"]} == {
                    "deletion", "non_fast_forward", "pull_request", "required_status_checks"}
        print("PASS:", name)


baseline = [ruleset("develop", ["squash", "merge"]), ruleset("main", ["merge"])]
run_case("accept propagation and topic methods", baseline, True)
reordered = copy.deepcopy(baseline)
reordered[0]["rules"][2]["parameters"]["allowed_merge_methods"] = ["merge", "squash"]
run_case("method order is immaterial", reordered, True)
for name, index, methods in [
    ("reject squash-only develop", 0, ["squash"]),
    ("reject rebase on develop", 0, ["squash", "merge", "rebase"]),
    ("reject squash on main", 1, ["squash", "merge"]),
]:
    fixture = copy.deepcopy(baseline)
    fixture[index]["rules"][2]["parameters"]["allowed_merge_methods"] = methods
    run_case(name, fixture, False, "incorrect allowed merge methods")
for rule_type, error in [
    ("deletion", "no deletion rule"),
    ("non_fast_forward", "no non_fast_forward rule"),
    ("pull_request", "no pull_request rule"),
    ("required_status_checks", "status check `check` is not required"),
]:
    fixture = copy.deepcopy(baseline)
    fixture[0]["rules"] = [r for r in fixture[0]["rules"] if r["type"] != rule_type]
    run_case("retain " + rule_type + " protection", fixture, False, error)
run_case("create branch-specific method arrays", [], True)
print("GITHUB SETUP FIXTURES OK — 10 cases, no remote calls")
