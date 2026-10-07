-- Live axiom audit input, consumed by scripts/check-axioms.sh.
-- Run after `lake build`:   lake env lean scripts/print_axioms.lean
--
-- Append one `#print axioms` line for every public theorem a PR claims as a result
-- (scripts/check-axiom-coverage.sh fails the gate when one is missing).
-- APPEND-ONLY: removing or renaming a line is a `needs-decision` change.
import TDA

-- Permanent smoke test of the audit path (TDA/Basic.lean). Never remove.
#print axioms TDA.placeholder_add_zero
