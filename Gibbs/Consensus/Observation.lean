import Mathlib.Data.Set.Basic
import Gibbs.Consensus.Basic

/-!
# Observations and indistinguishability

Each process observes only a local projection of the global execution, called
its "view". Two executions are *indistinguishable* to an honest set `H` when every
process in `H` sees exactly the same local history. This is the information-
theoretic core of consensus impossibility: an adversary that can produce two
executions indistinguishable to `H` forces honest processes into identical
behavior on both, even if the executions lead to different "correct" outcomes.
-/

namespace Gibbs.Consensus

/-! ## Observations and Indistinguishability -/

/-- Observation function returning a per-process local view. -/
abbrev Observation {N : ℕ} {S : Type} {T : ℕ} (View : Process N → Type) :
    Type := by
  -- This is just a type alias to avoid rewriting the full type.
  exact ∀ i, Execution N S T → View i

/-- Indistinguishability on a set of honest processes. -/
def Indistinguishable {N : ℕ} {S : Type} {T : ℕ}
    {View : Process N → Type}
    (Obs : ∀ i, Execution N S T → View i)
    (H : Set (Process N)) (ω ω' : Execution N S T) : Prop := by
  -- Two executions are indistinguishable if every honest view agrees.
  exact ∀ i ∈ H, Obs i ω = Obs i ω'

end Gibbs.Consensus
