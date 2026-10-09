-- TDA: library root. Every library module is imported here so that
-- `import TDA` (as used by scripts/print_axioms.lean and the coverage guard)
-- reaches all of them. A module missing here fails scripts/check-axiom-coverage.sh.
import TDA.Basic
import TDA.Filtration.Basic
import TDA.Persistence.Basic
import TDA.Persistence.Reduction.Pivot
import TDA.Persistence.Reduction.PivotExamples
import TDA.Reeb.Components
import TDA.Reeb.ComponentsCover
import TDA.Reeb.ComponentsCoverExamples
import TDA.Reeb.ComponentsExamples
import TDA.Reeb.Interval
import TDA.Reeb.IntervalExamples
import TDA.Reeb.Quotient
import TDA.Simplicial.Bridge
import TDA.Simplicial.Boundary
import TDA.Topology.PathCover
import TDA.Topology.PathCoverExamples
