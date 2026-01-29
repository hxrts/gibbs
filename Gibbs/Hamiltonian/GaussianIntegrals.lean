import Gibbs.Hamiltonian.Basic
import Mathlib

/-!
Gaussian integrals over configuration space.

These lemmas are intended as building blocks for equipartition-style results.
-/

namespace Gibbs.Hamiltonian

noncomputable section

open scoped BigOperators
open MeasureTheory

variable {n : ℕ}

/-!
## Gaussian integral over Euclidean configuration space
-/

lemma integral_gaussian_pi (a : ℝ) :
    ∫ x : Fin n → ℝ, Real.exp (-(a * ∑ i : Fin n, (x i) ^ 2)) =
      (Real.sqrt (Real.pi / a)) ^ n := by
  classical
  -- Rewrite the Gaussian in product form over coordinates.
  have h_exp :
      (fun x : Fin n → ℝ => Real.exp (-(a * ∑ i : Fin n, (x i) ^ 2))) =
        (fun x : Fin n → ℝ => ∏ i : Fin n, Real.exp (-(a * (x i) ^ 2))) := by
    funext x
    have h_sum : a * ∑ i : Fin n, (x i) ^ 2 = ∑ i : Fin n, a * (x i) ^ 2 := by
      simpa using
        (Finset.mul_sum (s := Finset.univ) (f := fun i : Fin n => (x i) ^ 2) (a := a))
    have h_sum_neg :
        -(a * ∑ i : Fin n, (x i) ^ 2) = ∑ i : Fin n, -(a * (x i) ^ 2) := by
      calc
        -(a * ∑ i : Fin n, (x i) ^ 2)
            = (-1 : ℝ) * (a * ∑ i : Fin n, (x i) ^ 2) := by ring
        _ = (-1 : ℝ) * ∑ i : Fin n, a * (x i) ^ 2 := by
              simp [h_sum]
        _ = ∑ i : Fin n, (-1 : ℝ) * (a * (x i) ^ 2) := by
              simp [Finset.mul_sum]
        _ = ∑ i : Fin n, -(a * (x i) ^ 2) := by
              simp [neg_mul]
    calc
      Real.exp (-(a * ∑ i : Fin n, (x i) ^ 2))
          = Real.exp (∑ i : Fin n, -(a * (x i) ^ 2)) := by
              rw [h_sum_neg]
      _ = ∏ i : Fin n, Real.exp (-(a * (x i) ^ 2)) := by
            exact (Real.exp_sum (s := Finset.univ) (f := fun i : Fin n => -(a * (x i) ^ 2)))
  -- Apply the product integral formula and the 1D Gaussian integral.
  have h_prod :
      ∫ x : Fin n → ℝ, ∏ i : Fin n, Real.exp (-(a * (x i) ^ 2)) =
        (∫ x : ℝ, Real.exp (-(a * x ^ 2))) ^ n := by
    simpa using
      (MeasureTheory.integral_fintype_prod_volume_eq_pow (ι := Fin n) (E := ℝ)
        (f := fun x : ℝ => Real.exp (-(a * x ^ 2))))
  calc
    ∫ x : Fin n → ℝ, Real.exp (-(a * ∑ i : Fin n, (x i) ^ 2))
        = ∫ x : Fin n → ℝ, ∏ i : Fin n, Real.exp (-(a * (x i) ^ 2)) := by
            simp [h_exp]
    _ = (∫ x : ℝ, Real.exp (-(a * x ^ 2))) ^ n := h_prod
    _ = (Real.sqrt (Real.pi / a)) ^ n := by
            have h_gauss :
                ∫ x : ℝ, Real.exp (-(a * x ^ 2)) = Real.sqrt (Real.pi / a) := by
              calc
                ∫ x : ℝ, Real.exp (-(a * x ^ 2)) =
                    ∫ x : ℝ, Real.exp (-a * x ^ 2) := by
                      simp [neg_mul]
                _ = Real.sqrt (Real.pi / a) := integral_gaussian a
            rw [h_gauss]

lemma integral_gaussian_config (a : ℝ) :
    ∫ x : Config n, Real.exp (-(a * ‖x‖ ^ 2)) =
      (Real.sqrt (Real.pi / a)) ^ n := by
  classical
  have h_norm_sq : ∀ x : Config n, ‖x‖ ^ 2 = ∑ i : Fin n, (x.ofLp i) ^ 2 := by
    intro x
    simpa [Real.norm_eq_abs, abs_sq] using (EuclideanSpace.norm_sq_eq (x := x))
  have h_rewrite :
      (fun x : Config n => Real.exp (-(a * ‖x‖ ^ 2))) =
        (fun x : Config n => Real.exp (-(a * ∑ i : Fin n, (x.ofLp i) ^ 2))) := by
    funext x
    simp [h_norm_sq x]
  have h_mp :
      MeasurePreserving ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm) := by
    simpa using (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin n))
  have h_int :
      ∫ x : Config n, Real.exp (-(a * ∑ i : Fin n, (x.ofLp i) ^ 2)) =
        ∫ y : Fin n → ℝ, Real.exp (-(a * ∑ i : Fin n, (y i) ^ 2)) := by
    simpa using
      (MeasurePreserving.integral_comp'
        (μ := volume) (ν := volume) h_mp
        (g := fun y : Fin n → ℝ => Real.exp (-(a * ∑ i : Fin n, (y i) ^ 2))))
  calc
    ∫ x : Config n, Real.exp (-(a * ‖x‖ ^ 2))
        = ∫ x : Config n, Real.exp (-(a * ∑ i : Fin n, (x.ofLp i) ^ 2)) := by
            simp [h_rewrite]
    _ = ∫ y : Fin n → ℝ, Real.exp (-(a * ∑ i : Fin n, (y i) ^ 2)) := h_int
    _ = (Real.sqrt (Real.pi / a)) ^ n := integral_gaussian_pi (n := n) a

end

end Gibbs.Hamiltonian
