import Mathlib.Data.Set.Basic

/-!
# Safety and liveness monotonicity

Safety and liveness have opposite monotonicity in the execution set, which
is why randomness helps liveness but cannot help safety.

Safety is a universal property: "for all executions in `Ω`, no bad macrostate
is realized." Enlarging `Ω` (adding more possible executions) can only break
safety, never establish it. Safety is monotone *downward* under set inclusion.

Liveness is an existential property: "some execution in `Ω` realizes a good
macrostate." Enlarging `Ω` can only help liveness. Liveness is monotone
*upward* under set inclusion.

This asymmetry is why BFT protocols separate the two concerns: quorum
structure (which restricts `Ω`) enforces safety, while randomness (which
enriches `Ω`) enables liveness.
-/

namespace Gibbs.Consensus

/-! ## Safety and Liveness over Execution Sets -/

/-- Safety over an execution set `Ω`: no bad macrostate is realized. -/
def IsSafeOn {Exec M : Type} (dec : Exec → M) (Bad : Set M) (Ω : Set Exec) : Prop :=
  ∀ ω ∈ Ω, dec ω ∉ Bad

/-- Liveness over an execution set `Ω`: some good macrostate is realized. -/
def IsLiveOn {Exec M : Type} (dec : Exec → M) (Good : Set M) (Ω : Set Exec) : Prop :=
  ∃ ω ∈ Ω, dec ω ∈ Good

/-- Safety is monotone downward under execution-set inclusion. -/
theorem safety_mono {Exec M : Type} {dec : Exec → M} {Bad : Set M}
    {Ω Ω' : Set Exec} (hΩ : Ω ⊆ Ω') :
    IsSafeOn dec Bad Ω' → IsSafeOn dec Bad Ω := by
  intro hs ω hω
  exact hs ω (hΩ hω)

/-- Liveness is monotone upward under execution-set inclusion. -/
theorem liveness_mono {Exec M : Type} {dec : Exec → M} {Good : Set M}
    {Ω Ω' : Set Exec} (hΩ : Ω ⊆ Ω') :
    IsLiveOn dec Good Ω → IsLiveOn dec Good Ω' := by
  intro hl
  rcases hl with ⟨ω, hω, hgood⟩
  exact ⟨ω, hΩ hω, hgood⟩

end Gibbs.Consensus
