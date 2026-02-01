import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Basic
import Gibbs.Consensus.Basic

/-!
# Adversary model

An adversary is a bounded perturbation of the execution. It can apply any
transformation from its `allowed` set, subject to a corruption `budget` that
limits how many processes or messages it may alter. The *adversary ball*
`B_A(ω)` around an execution `ω` is the set of all executions the adversary
can steer the system into, the analogue of a noise ball in coding theory.

Safety reduces to showing that no execution in the adversary ball crosses into
a bad macrostate. The adversary ball must stay inside the basin of attraction
of the correct ordered phase.
-/

namespace Gibbs.Consensus

open scoped ENNReal

/-! ## Adversary Classes -/

/-- An adversary class is a set of execution transformations plus a budget. -/
structure AdversaryClass (Exec : Type) where
  /-- Allowed transformations. -/
  allowed : Set (Exec → Exec)
  /-- Corruption budget (for documentation and later constraints). -/
  budget : ℝ≥0∞

/-- The adversary ball around an execution. -/
def adversaryBall {Exec : Type} (A : AdversaryClass Exec) (ω : Exec) : Set Exec := by
  -- A point is reachable if some allowed transform maps to it.
  exact { ω' | ∃ T ∈ A.allowed, ω' = T ω }

end Gibbs.Consensus
