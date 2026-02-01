import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Basic
import Gibbs.Hamiltonian.EnergyDistance

/-!
# Interactive distance between macrostates

The central quantity unifying coding theory and consensus. The *interactive
distance* `Δ_H(M, M')` between two decision macrostates is the minimum
execution-level distance over all pairs of executions realizing those
macrostates. This is the consensus analogue of code distance `d_min`. Just as
a code can correct `t` errors when `d_min > 2t`, a consensus protocol is safe
against `f` corruptions when the interactive distance from good to bad
macrostates exceeds `f`.

When two macrostates overlap (some execution maps to both), the interactive
distance is zero. This is the information-theoretic signature of FLP-style
impossibility: the adversary can push the system from one macrostate to the
other at zero cost.
-/

namespace Gibbs.Consensus

open scoped ENNReal

noncomputable section

/-! ## Interactive Distance Between Macrostates -/

/-- Executions that realize a given macrostate. -/
def macrostateSet {Exec M : Type} (dec : Exec → M) (m : M) : Set Exec := by
  -- An execution realizes a macrostate if the decoder outputs that macrostate.
  exact { ω | dec ω = m }

/-- Interactive distance between macrostates, using a supplied execution distance. -/
def interactiveDistance {Exec M : Type} (d : Exec → Exec → ℝ≥0∞)
    (dec : Exec → M) (m m' : M) : ℝ≥0∞ := by
  -- Take the infimum over all executions realizing `m` and `m'`.
  exact sInf { r | ∃ ω ∈ macrostateSet dec m, ∃ ω' ∈ macrostateSet dec m', r = d ω ω' }

/-! ## Lower Bounds and Degeneracy -/

/-- A uniform lower bound on cross-macrostate distances lifts to the infimum. -/
theorem interactiveDistance_lower_bound {Exec M : Type} (d : Exec → Exec → ℝ≥0∞)
    (dec : Exec → M) {m m' : M} {r : ℝ≥0∞}
    (h : ∀ ω ∈ macrostateSet dec m, ∀ ω' ∈ macrostateSet dec m', r ≤ d ω ω') :
    r ≤ interactiveDistance d dec m m' := by
  refine le_sInf ?_
  intro s hs
  rcases hs with ⟨ω, hω, ω', hω', rfl⟩
  exact h ω hω ω' hω'

/-- Overlapping macrostates force zero interactive distance. -/
theorem interactiveDistance_eq_zero_of_overlap {Exec M : Type} [Gibbs.Hamiltonian.EnergyDistance Exec]
    (dec : Exec → M) {m m' : M}
    (h : ∃ ω, dec ω = m ∧ dec ω = m') :
    interactiveDistance Gibbs.Hamiltonian.EnergyDistance.dist dec m m' = 0 := by
  rcases h with ⟨ω, hm, hm'⟩
  apply le_antisymm
  ·
    apply sInf_le
    refine ⟨ω, ?_, ω, ?_, ?_⟩
    · simp [macrostateSet, hm]
    · simp [macrostateSet, hm']
    · simp [Gibbs.Hamiltonian.EnergyDistance.dist_self]
  · exact bot_le

end

end Gibbs.Consensus
