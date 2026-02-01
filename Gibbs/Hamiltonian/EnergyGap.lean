import Mathlib.Data.ENNReal.Basic
import Gibbs.Hamiltonian.EnergyDistance

/-!
# Energy Gap

The energy gap between two sets of states is the infimum of pairwise distances
across the sets. A positive gap means every path from one set to the other must
cross a nontrivial energy barrier. In physics this distinguishes ordered from
disordered phases. In consensus it separates safe (agreement) from unsafe
(disagreement) executions, with the gap quantifying finality strength.
-/

namespace Gibbs.Hamiltonian

open scoped ENNReal

noncomputable section

/-! ## Energy Gaps -/

/-- The energy gap between two sets, defined as the infimum of pairwise distances. -/
def energyGap {α : Type} [EnergyDistance α] (A B : Set α) : ℝ≥0∞ := by
  -- Use the infimum of all cross-set distances (empty set gives `∞`).
  exact sInf { r | ∃ a ∈ A, ∃ b ∈ B, r = EnergyDistance.dist a b }

/-- The gap is bounded above by any witnessed cross-set distance. -/
theorem energyGap_le_dist {α : Type} [EnergyDistance α]
    {A B : Set α} {a b : α} (ha : a ∈ A) (hb : b ∈ B) :
    energyGap A B ≤ EnergyDistance.dist a b := by
  -- Apply the `sInf_le` lemma to the specific witness pair.
  apply sInf_le
  exact ⟨a, ha, b, hb, rfl⟩

/-- A set pair is gapped if its energy gap is positive. -/
def HasEnergyGap {α : Type} [EnergyDistance α] (A B : Set α) : Prop := by
  -- Positivity in `ℝ≥0∞` captures a nontrivial barrier.
  exact 0 < energyGap A B

end

end Gibbs.Hamiltonian
