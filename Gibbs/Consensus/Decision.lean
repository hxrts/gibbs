import Mathlib.Data.Set.Basic
import Gibbs.Consensus.Observation

/-!
# Decisions and macrostates

A *decision macrostate* is the coarse-grained observable of consensus. It is the
vector of values that honest processes have decided on (or `none` if undecided).
This is the order-parameter-level description. Many different microscopic
executions can produce the same macrostate, and the physics of consensus is about
which macrostates dominate the partition function.

Agreement means all decided values coincide (ordered phase). Disagreement means
at least two differ (disordered / unsafe phase).
-/

namespace Gibbs.Consensus

/-! ## Decisions and Macrostates -/

/-- A decision output with `none` representing "undecided". -/
abbrev DecisionOut (D : Type) : Type := Option D

/-- A decision function mapping local views to outputs. -/
abbrev DecisionFn {N : ℕ} {View : Process N → Type} (D : Type) : Type :=
  ∀ i, View i → DecisionOut D

/-- The decision vector induced by an execution. -/
def decisionVector {N : ℕ} {S : Type} {T : ℕ} {D : Type}
    {View : Process N → Type} (Obs : ∀ i, Execution N S T → View i)
    (Dec : DecisionFn (N := N) (View := View) D) (ω : Execution N S T) :
    Process N → DecisionOut D := by
  -- Each process decides based on its local view of the execution.
  exact fun i => Dec i (Obs i ω)

/-- Decision macrostates indexed by the honest set `H`. -/
def DecisionMacrostate {N : ℕ} (H : Set (Process N)) (D : Type) : Type := by
  -- Use a subtype to restrict indices to honest processes.
  exact { i : Process N // i ∈ H } → DecisionOut D

/-- The macrostate induced by an execution on honest processes. -/
def macrostateOf {N : ℕ} {S : Type} {T : ℕ} {D : Type}
    {View : Process N → Type} (Obs : ∀ i, Execution N S T → View i)
    (Dec : DecisionFn (N := N) (View := View) D)
    (H : Set (Process N)) (ω : Execution N S T) : DecisionMacrostate H D := by
  -- Restrict the decision vector to honest indices.
  exact fun i => Dec i.1 (Obs i.1 ω)

/-- Agreement means no two decided values disagree. -/
def Agreement {N : ℕ} {H : Set (Process N)} {D : Type}
    (M : DecisionMacrostate (N := N) H D) : Prop := by
  -- Only compare positions that have actually decided.
  exact ∀ i j d d', M i = some d → M j = some d' → d = d'

/-- Disagreement means some two decided values differ. -/
def Disagreement {N : ℕ} {H : Set (Process N)} {D : Type}
    (M : DecisionMacrostate (N := N) H D) : Prop := by
  -- Witness two conflicting decided values.
  exact ∃ i j d d', M i = some d ∧ M j = some d' ∧ d ≠ d'

end Gibbs.Consensus
