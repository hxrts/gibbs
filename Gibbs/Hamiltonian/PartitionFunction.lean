import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-
The Problem. We need a finite-state partition function and free energy
that are application-agnostic and can be specialized later (e.g. to consensus).

Solution Structure.
1. Define a finite-state partition function using a plain sum.
2. Define free energy from the partition function.
3. Record basic nonnegativity for later use.
-/

namespace Gibbs.Hamiltonian.PartitionFunction

noncomputable section

open scoped BigOperators

variable {α : Type} [Fintype α]

/-! ## Finite-State Partition Function -/

/-- Finite-state partition function for energy `H` at inverse temperature `β`. -/
def partitionFunction (H : α → ℝ) (β : ℝ) : ℝ := by
  -- Sum the unnormalized Boltzmann weights over the finite state space.
  exact ∑ x, Real.exp (-β * H x)

/-- Free energy associated with the finite-state partition function. -/
def freeEnergy (H : α → ℝ) (β : ℝ) : ℝ := by
  -- Use the standard thermodynamic definition `F = -(1/β) * log Z`.
  exact - (1 / β) * Real.log (partitionFunction H β)

/-- The finite-state partition function is nonnegative. -/
theorem partitionFunction_nonneg (H : α → ℝ) (β : ℝ) :
    0 ≤ partitionFunction H β := by
  -- Each Boltzmann weight is nonnegative, and sums preserve nonnegativity.
  refine Finset.sum_nonneg ?_ 
  intro x hx
  exact Real.exp_nonneg _

/-! ## Free-Energy Bounds -/

variable [Nonempty α]

/-- The energy image of a finite state space is nonempty. -/
lemma energyImage_nonempty (H : α → ℝ) : (Finset.univ.image H).Nonempty := by
  classical
  exact (Finset.image_nonempty).2 (Finset.univ_nonempty)

/-- The minimum energy value over a finite state space. -/
def minEnergy (H : α → ℝ) : ℝ := by
  classical
  exact (Finset.univ.image H).min' (energyImage_nonempty H)
/-- The minimum energy is attained by some state. -/
theorem minEnergy_mem (H : α → ℝ) :
    ∃ x, H x = minEnergy H := by
  classical
  have hmem : minEnergy H ∈ Finset.univ.image H := by
    simpa [minEnergy, energyImage_nonempty] using
      (Finset.min'_mem (Finset.univ.image H) (energyImage_nonempty H))
  rcases Finset.mem_image.mp hmem with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

/-- The minimum energy is a lower bound for all states. -/
theorem minEnergy_le (H : α → ℝ) (x : α) :
    minEnergy H ≤ H x := by
  classical
  have hx : H x ∈ Finset.univ.image H := by
    exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩
  have hmin : (Finset.univ.image H).min' (energyImage_nonempty H) ≤ H x := by
    exact Finset.min'_le (s := Finset.univ.image H) (x := H x) hx
  simpa [minEnergy, energyImage_nonempty] using hmin

/-- Upper bound on the partition function via the minimum energy. -/
theorem partitionFunction_le_card_mul_exp_min (H : α → ℝ) (β : ℝ) (hβ : 0 < β) :
    partitionFunction H β ≤ (Fintype.card α : ℝ) * Real.exp (-β * minEnergy H) := by
  classical
  have hterm : ∀ x, Real.exp (-β * H x) ≤ Real.exp (-β * minEnergy H) := by
    intro x
    have hmin : minEnergy H ≤ H x := minEnergy_le H x
    have hneg : -β * H x ≤ -β * minEnergy H := by
      exact mul_le_mul_of_nonpos_left hmin (by linarith : -β ≤ 0)
    exact Real.exp_le_exp.mpr hneg
  calc
    partitionFunction H β
        = ∑ x, Real.exp (-β * H x) := rfl
    _ ≤ ∑ _x, Real.exp (-β * minEnergy H) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact hterm x
    _ = (Fintype.card α : ℝ) * Real.exp (-β * minEnergy H) := by
        simp

/-- Lower bound on the partition function via the minimum energy. -/
theorem exp_min_le_partitionFunction (H : α → ℝ) (β : ℝ) :
    Real.exp (-β * minEnergy H) ≤ partitionFunction H β := by
  classical
  rcases minEnergy_mem H with ⟨x, hx⟩
  have hx' : Real.exp (-β * minEnergy H) = Real.exp (-β * H x) := by
    simp [hx]
  calc
    Real.exp (-β * minEnergy H)
        = Real.exp (-β * H x) := hx'
    _ ≤ ∑ y, Real.exp (-β * H y) := by
      have hxmem : x ∈ (Finset.univ : Finset α) := by simp
      exact Finset.single_le_sum (f := fun y => Real.exp (-β * H y))
        (fun _ _ => Real.exp_nonneg _) hxmem
    _ = partitionFunction H β := rfl

/-! ## Log Bounds -/

/-- Log-partition upper bound using the minimum energy and state count. -/
theorem log_partitionFunction_le_card_exp (H : α → ℝ) (β : ℝ) (hβ : 0 < β) :
    Real.log (partitionFunction H β) ≤
      Real.log (Fintype.card α) + (-β * minEnergy H) := by
  have hpos : 0 < partitionFunction H β := by
    have hle := exp_min_le_partitionFunction H β
    exact lt_of_lt_of_le (Real.exp_pos _) hle
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr (by infer_instance))
  have hupper :
      Real.log (partitionFunction H β) ≤
        Real.log ((Fintype.card α : ℝ) * Real.exp (-β * minEnergy H)) := by
    refine Real.log_le_log hpos ?_
    exact partitionFunction_le_card_mul_exp_min H β hβ
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  calc
    Real.log (partitionFunction H β)
        ≤ Real.log ((Fintype.card α : ℝ) * Real.exp (-β * minEnergy H)) := hupper
    _ = Real.log (Fintype.card α) + Real.log (Real.exp (-β * minEnergy H)) := by
        simp [Real.log_mul, hcard_ne]
    _ = Real.log (Fintype.card α) + (-β * minEnergy H) := by
        simp

/-- Free energy is bounded above by the minimum energy. -/
theorem freeEnergy_le_minEnergy (H : α → ℝ) (β : ℝ) (hβ : 0 < β) :
    freeEnergy H β ≤ minEnergy H := by
  have hpos : 0 < partitionFunction H β := by
    have hle := exp_min_le_partitionFunction H β
    exact lt_of_lt_of_le (Real.exp_pos _) hle
  have hlog :
      Real.log (partitionFunction H β) ≥ -β * minEnergy H := by
    have hle := exp_min_le_partitionFunction H β
    have hpos' : 0 < Real.exp (-β * minEnergy H) := Real.exp_pos _
    have hlog' : Real.log (Real.exp (-β * minEnergy H)) ≤
        Real.log (partitionFunction H β) :=
      (Real.log_le_log hpos' hle)
    simpa using hlog'
  have hmul : - (1 / β) * Real.log (partitionFunction H β) ≤ minEnergy H := by
    have hcoef : -(1 / β) ≤ 0 := by
      exact neg_nonpos.mpr (one_div_nonneg.mpr (le_of_lt hβ))
    have hneg : -(1 / β) * Real.log (partitionFunction H β) ≤
        - (1 / β) * (-β * minEnergy H) := by
      exact mul_le_mul_of_nonpos_left hlog hcoef
    have hcalc : -(1 / β) * (-β * minEnergy H) = minEnergy H := by
      have hβne : β ≠ 0 := by linarith
      field_simp [hβne]
    calc
      - (1 / β) * Real.log (partitionFunction H β)
          ≤ - (1 / β) * (-β * minEnergy H) := hneg
      _ = minEnergy H := hcalc
  exact hmul

/-- Free energy is within `(log |Ω|)/β` of the minimum energy. -/
theorem minEnergy_le_freeEnergy_add (H : α → ℝ) (β : ℝ) (hβ : 0 < β) :
    minEnergy H - (Real.log (Fintype.card α)) / β ≤ freeEnergy H β := by
  have hlog : Real.log (partitionFunction H β) ≤
      Real.log (Fintype.card α) + (-β * minEnergy H) :=
    log_partitionFunction_le_card_exp H β hβ
  have hmul :
      minEnergy H - (Real.log (Fintype.card α)) / β ≤
        - (1 / β) * Real.log (partitionFunction H β) := by
    have hcoef : -(1 / β) ≤ 0 := by
      exact neg_nonpos.mpr (one_div_nonneg.mpr (le_of_lt hβ))
    have hneg :
        - (1 / β) * Real.log (partitionFunction H β) ≥
          - (1 / β) * (Real.log (Fintype.card α) + (-β * minEnergy H)) := by
      exact mul_le_mul_of_nonpos_left hlog hcoef
    have hcalc :
        - (1 / β) * (Real.log (Fintype.card α) + (-β * minEnergy H)) =
          minEnergy H - (Real.log (Fintype.card α)) / β := by
      have hβne : β ≠ 0 := by linarith
      field_simp [hβne]
      ring
    calc
      minEnergy H - (Real.log (Fintype.card α)) / β
          = - (1 / β) * (Real.log (Fintype.card α) + (-β * minEnergy H)) := by
              symm
              exact hcalc
      _ ≤ - (1 / β) * Real.log (partitionFunction H β) := by
              exact hneg
  simpa [freeEnergy] using hmul

end

end Gibbs.Hamiltonian.PartitionFunction
