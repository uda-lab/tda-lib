-- TDA: library root. Every library module is imported here so that
-- `import TDA` (as used by scripts/print_axioms.lean and the coverage guard)
-- reaches all of them. A module missing here fails scripts/check-axiom-coverage.sh.
import TDA.Basic
import TDA.Filtration.Basic
import TDA.Persistence.Basic
import TDA.Simplicial.Bridge
