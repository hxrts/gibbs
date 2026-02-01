import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Basic
import Gibbs.Hamiltonian.EnergyDistance
import Gibbs.Hamiltonian.EnergyGap
import Gibbs.Consensus.TranscriptDistance

/-!
# Coding distance and unique decoding

Connects classical coding theory to the energy-gap framework. The minimum
distance `d_min` of a code is the smallest pairwise distance between distinct
codewords. The key result is that unique decoding succeeds when the error
radius satisfies `2t < d_min`, proved via the triangle inequality: two
distinct codewords cannot both be within radius `t` of the same received word.

Hamming distance is registered as an `EnergyDistance` instance, so all
energy-gap machinery from the Hamiltonian layer applies directly to codes.
The singleton-gap lemma shows that the energy gap between two single-codeword
sets equals their Hamming distance, confirming that "distance = gap" at the
most basic level.
-/

namespace Gibbs.Consensus

open scoped ENNReal

noncomputable section

open Gibbs.Hamiltonian

/-! ## Hamming Energy Distance -/

/-- Hamming distance as an energy-distance on finite functions. -/
instance hammingEnergyDistance {ι α : Type} [Fintype ι] [DecidableEq α] :
    EnergyDistance (ι → α) := by
  refine
    { dist := hammingDistance
      dist_self := hammingDistance_self
      dist_comm := hammingDistance_comm
      dist_triangle := hammingDistance_triangle }

/-! ## Minimum Distance -/

/-- Minimum distance of a code as an infimum over distinct codeword pairs. -/
def minimumDistance {α : Type} [EnergyDistance α] (C : Set α) : ℝ≥0∞ := by
  exact sInf { r | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ r = EnergyDistance.dist x y }

/-- Minimum distance is bounded above by any distinct pair distance. -/
theorem minimumDistance_le_dist {α : Type} [EnergyDistance α] {C : Set α}
    {x y : α} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    minimumDistance C ≤ EnergyDistance.dist x y := by
  apply sInf_le
  exact ⟨x, hx, y, hy, hxy, rfl⟩

/-- Unique-decoding condition: `t + t < d_min` forbids two close codewords. -/
theorem unique_decoding_of_minDistance {α : Type} [EnergyDistance α]
    {C : Set α} {t : ℝ≥0∞} {w x y : α}
    (hx : x ∈ C) (hy : y ∈ C)
    (hxw : EnergyDistance.dist x w ≤ t)
    (hyw : EnergyDistance.dist y w ≤ t)
    (hgap : t + t < minimumDistance C) :
    x = y := by
  by_contra hxy
  have hmin : minimumDistance C ≤ EnergyDistance.dist x y :=
    minimumDistance_le_dist hx hy hxy
  have htri : EnergyDistance.dist x y ≤ t + t := by
    have hxyw : EnergyDistance.dist x y ≤
        EnergyDistance.dist x w + EnergyDistance.dist w y :=
      EnergyDistance.dist_triangle x w y
    calc
      EnergyDistance.dist x y
          ≤ EnergyDistance.dist x w + EnergyDistance.dist w y := hxyw
      _ = EnergyDistance.dist x w + EnergyDistance.dist y w := by
          simp [EnergyDistance.dist_comm]
      _ ≤ t + t := by
          exact add_le_add hxw hyw
  have hle : minimumDistance C ≤ t + t := le_trans hmin htri
  exact (not_lt_of_ge hle) hgap

/-! ## Distance Equals Gap for Singletons -/

/-- The energy gap between singletons equals the point distance. -/
theorem energyGap_singleton_eq_dist {α : Type} [EnergyDistance α] (x y : α) :
    energyGap ({x} : Set α) ({y} : Set α) = EnergyDistance.dist x y := by
  apply le_antisymm
  · exact energyGap_le_dist (A := {x}) (B := {y}) (by simp) (by simp)
  ·
    refine le_sInf ?_
    intro r hr
    rcases hr with ⟨a, ha, b, hb, rfl⟩
    simp [Set.mem_singleton_iff] at ha hb
    simp [ha, hb]

end

end Gibbs.Consensus
