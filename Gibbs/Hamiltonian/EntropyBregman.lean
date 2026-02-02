import Gibbs.Hamiltonian.Entropy
import Gibbs.Hamiltonian.Legendre
import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.PartitionFunction
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Entropy as a Bregman Generator

Connects negative entropy to Bregman divergence and the Legendre transform.
The deep convex-analytic results are stated as axioms to keep this file a
lightweight bridge between the information-theory and Hamiltonian layers.
-/

namespace Gibbs.Hamiltonian.EntropyBregman

open Gibbs.Hamiltonian
open InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Convert `Fin n → ℝ` to configuration space. -/
private def toConfig (x : Fin n → ℝ) : Config n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm x

/-- Convert configuration space to `Fin n → ℝ`. -/
private def fromConfig (x : Config n) : Fin n → ℝ :=
  (EuclideanSpace.equiv (Fin n) ℝ) x

/-- Negative entropy on configuration space. -/
def negEntropyConfig (n : ℕ) : Config n → ℝ :=
  fun x => ∑ i : Fin n, let xi := (fromConfig x) i
            if xi = 0 then 0 else xi * Real.log xi

/-- Negative entropy is strictly convex on the simplex interior. -/
theorem negEntropyConfig_strictConvex_on_interior (n : ℕ) :
    StrictConvexOn ℝ { x : Config n | ∀ i, 0 < (fromConfig x) i }
      (negEntropyConfig n) := by
  classical
  let S : Set (Config n) := { x : Config n | ∀ i, 0 < (fromConfig x) i }
  let g : ℝ → ℝ := fun x => x * Real.log x
  have hstrict_g : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) g := by
    have h := (Real.strictConvexOn_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) g)
    refine h.subset ?_ (convex_Ioi (0 : ℝ))
    intro x hx
    exact le_of_lt (by simpa using hx)
  have hconv_g : ConvexOn ℝ (Set.Ioi (0 : ℝ)) g := hstrict_g.convexOn
  have hfrom_add :
      ∀ (a b : ℝ) (x y : Config n) (i : Fin n),
        fromConfig (a • x + b • y) i =
          a * fromConfig x i + b * fromConfig y i := by
    intro a b x y i
    -- `fromConfig` is linear via the EuclideanSpace equivalence.
    simp [fromConfig]
  have hconvS : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    intro i
    have hxpos : 0 < fromConfig x i := hx i
    have hypos : 0 < fromConfig y i := hy i
    have hlin := hfrom_add a b x y i
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [hlin, ha0, hb1] using hypos
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simpa [hlin, hb0, ha1] using hxpos
      · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hsum : 0 < a * fromConfig x i + b * fromConfig y i :=
          add_pos (mul_pos ha_pos hxpos) (mul_pos hb_pos hypos)
        simpa [hlin] using hsum
  refine ⟨hconvS, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hneq : ∃ i, fromConfig x i ≠ fromConfig y i := by
    by_contra h
    apply hxy
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    funext i
    by_contra hne
    exact h ⟨i, hne⟩
  rcases hneq with ⟨i0, hneq0⟩
  have hle :
      ∀ i, g (a * fromConfig x i + b * fromConfig y i) ≤
        a * g (fromConfig x i) + b * g (fromConfig y i) := by
    intro i
    have hxpos : 0 < fromConfig x i := hx i
    have hypos : 0 < fromConfig y i := hy i
    have hconv := hconv_g.2 hxpos hypos (le_of_lt ha) (le_of_lt hb) hab
    simpa [g, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hconv
  have hlt :
      g (a * fromConfig x i0 + b * fromConfig y i0) <
        a * g (fromConfig x i0) + b * g (fromConfig y i0) := by
    have hxpos : 0 < fromConfig x i0 := hx i0
    have hypos : 0 < fromConfig y i0 := hy i0
    have hstrict := hstrict_g.2 hxpos hypos hneq0 ha hb hab
    simpa [g, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hstrict
  have hsum_lt :
      ∑ i, g (a * fromConfig x i + b * fromConfig y i) <
        ∑ i, (a * g (fromConfig x i) + b * g (fromConfig y i)) := by
    refine Finset.sum_lt_sum (fun i _ => hle i) ?_
    exact ⟨i0, by simp, hlt⟩
  have hpos_comb :
      ∀ i, 0 < a * fromConfig x i + b * fromConfig y i := by
    intro i
    have hxpos : 0 < fromConfig x i := hx i
    have hypos : 0 < fromConfig y i := hy i
    exact add_pos (mul_pos ha hxpos) (mul_pos hb hypos)
  have hneg_x :
      negEntropyConfig n x = ∑ i, g (fromConfig x i) := by
    unfold negEntropyConfig g
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hxpos : 0 < fromConfig x i := hx i
    have hne : fromConfig x i ≠ 0 := ne_of_gt hxpos
    simp [hne]
  have hneg_y :
      negEntropyConfig n y = ∑ i, g (fromConfig y i) := by
    unfold negEntropyConfig g
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hypos : 0 < fromConfig y i := hy i
    have hne : fromConfig y i ≠ 0 := ne_of_gt hypos
    simp [hne]
  have hneg_xy :
      negEntropyConfig n (a • x + b • y) =
        ∑ i, g (a * fromConfig x i + b * fromConfig y i) := by
    unfold negEntropyConfig g
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hpos : 0 < a * fromConfig x i + b * fromConfig y i := hpos_comb i
    have hne : a * fromConfig x i + b * fromConfig y i ≠ 0 := ne_of_gt hpos
    have hlin := hfrom_add a b x y i
    simp [hlin, hne]
  have hsum_rhs :
      ∑ i, (a * g (fromConfig x i) + b * g (fromConfig y i)) =
        a * (∑ i, g (fromConfig x i)) + b * (∑ i, g (fromConfig y i)) := by
    calc
      ∑ i, (a * g (fromConfig x i) + b * g (fromConfig y i))
          = ∑ i, a * g (fromConfig x i) + ∑ i, b * g (fromConfig y i) := by
              simp [Finset.sum_add_distrib]
      _ = a * (∑ i, g (fromConfig x i)) + b * (∑ i, g (fromConfig y i)) := by
              simp [Finset.mul_sum]
  calc
    negEntropyConfig n (a • x + b • y)
        = ∑ i, g (a * fromConfig x i + b * fromConfig y i) := hneg_xy
    _ < ∑ i, (a * g (fromConfig x i) + b * g (fromConfig y i)) := hsum_lt
    _ = a * negEntropyConfig n x + b * negEntropyConfig n y := by
        simp [hsum_rhs, hneg_x, hneg_y]

/-! ## KL = Bregman -/

/-- KL divergence is the Bregman divergence of negative entropy. -/
theorem kl_eq_bregman_negEntropy (n : ℕ) (p q : Fin n → ℝ)
    (_hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1) :
    Gibbs.Hamiltonian.Entropy.klDivergence p q =
      bregman (negEntropyConfig n) (toConfig p) (toConfig q) := by
  classical
  let g : ℝ → ℝ := fun x => x * Real.log x
  have hneg : ∀ x, negEntropyConfig n x = ∑ i, g (fromConfig x i) := by
    intro x
    unfold negEntropyConfig g
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hxi : fromConfig x i = 0
    · simp [hxi]
    · simp [hxi]
  have hgrad :
      gradient (negEntropyConfig n) (toConfig q) =
        toConfig (fun i => Real.log (q i) + 1) := by
    -- compute the gradient via fderiv of the coordinatewise sum
    have hderiv_i :
        ∀ i, HasFDerivAt (𝕜 := ℝ) (fun x : Config n => g (fromConfig x i))
              (((Real.log (q i) + (1 : ℝ)) : ℝ) •
                (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)) (toConfig q) := by
      intro i
      have hqne : q i ≠ 0 := ne_of_gt (hq_pos i)
      have hg : HasDerivAt (𝕜 := ℝ) g (Real.log (q i) + 1) (q i) := by
        simpa [g] using (Real.hasDerivAt_mul_log hqne)
      have hφ : HasFDerivAt (𝕜 := ℝ) (fun x : Config n => fromConfig x i)
          (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i) (toConfig q) := by
        -- `fromConfig x i` is the coordinate projection
        simpa [fromConfig] using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i).hasFDerivAt
      simpa [g] using (hg.comp_hasFDerivAt (toConfig q) hφ)
    have hsum_deriv :
        HasFDerivAt (fun x : Config n => ∑ i, g (fromConfig x i))
          (∑ i, (Real.log (q i) + 1) •
            (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)) (toConfig q) := by
      simpa using (HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
        (A := fun i => fun x : Config n => g (fromConfig x i))
        (A' := fun i => ((Real.log (q i) + (1 : ℝ)) : ℝ) •
          (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i))
        (x := toConfig q)
        (h := by intro i hi; exact hderiv_i i))
    have hsum_eq : (fun x : Config n => negEntropyConfig n x) =
        fun x => ∑ i, g (fromConfig x i) := by
      funext x
      exact hneg x
    have hsum_deriv' :
        HasFDerivAt (negEntropyConfig n)
          (∑ i, ((Real.log (q i) + (1 : ℝ)) : ℝ) •
            (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)) (toConfig q) := by
      simpa [hsum_eq] using hsum_deriv
    -- convert to gradient form
    have hgrad' :
        HasGradientAt (negEntropyConfig n)
          ((toDual ℝ (Config n)).symm
            (∑ i, ((Real.log (q i) + (1 : ℝ)) : ℝ) •
              (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i))) (toConfig q) :=
      (hasFDerivAt_iff_hasGradientAt).1 hsum_deriv'
    -- identify the vector corresponding to the coordinate sum
    have htoDual :
        (toDual ℝ (Config n))
            (toConfig (fun i => Real.log (q i) + 1)) =
          ∑ i, ((Real.log (q i) + (1 : ℝ)) : ℝ) •
            (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i) := by
      ext v
      -- evaluate both sides on `v`
      simp [toDual_apply_apply, toConfig, EuclideanSpace.proj, PiLp.inner_apply, mul_comm]
    have hvec :
        (toDual ℝ (Config n)).symm
            (∑ i, ((Real.log (q i) + (1 : ℝ)) : ℝ) •
              (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i)) =
          toConfig (fun i => Real.log (q i) + 1) := by
      -- apply injectivity of `toDual`
      apply (toDual ℝ (Config n)).injective
      simp [htoDual]
    -- conclude on gradients
    simpa [hvec] using hgrad'.gradient
  -- expand the Bregman divergence and simplify
  unfold Gibbs.Hamiltonian.Entropy.klDivergence bregman
  -- rewrite negEntropy terms
  have hneg_p : negEntropyConfig n (toConfig p) = ∑ i, g (p i) := by
    simp [hneg, toConfig, fromConfig]
  have hneg_q : negEntropyConfig n (toConfig q) = ∑ i, g (q i) := by
    simp [hneg, toConfig, fromConfig]
  -- inner product term
  have hinner_toConfig (a b : Fin n → ℝ) :
      inner ℝ (toConfig a) (toConfig b) = ∑ i, a i * b i := by
    simp [toConfig, PiLp.inner_apply, mul_comm]
  have htoConfig_sub : toConfig (fun i => p i - q i) = toConfig p - toConfig q := by
    ext i
    simp [toConfig, sub_eq_add_neg]
  have hinner :
      inner ℝ (gradient (negEntropyConfig n) (toConfig q)) (toConfig p - toConfig q) =
        ∑ i, (Real.log (q i) + 1) * (p i - q i) := by
    calc
      inner ℝ (gradient (negEntropyConfig n) (toConfig q)) (toConfig p - toConfig q)
          = inner ℝ (toConfig (fun i => Real.log (q i) + 1))
              (toConfig (fun i => p i - q i)) := by
                simp [hgrad, htoConfig_sub]
      _ = ∑ i, (Real.log (q i) + 1) * (p i - q i) := by
            simpa using (hinner_toConfig (fun i => Real.log (q i) + 1) (fun i => p i - q i))
  -- finish by algebra
  have hsum_pq : (∑ i, (p i - q i)) = 0 := by
    simp [hp_sum, hq_sum]
  have hcalc1 :
      (∑ a, if p a = 0 then 0 else p a * Real.log (p a / q a)) =
        (∑ i, (if p i = 0 then 0 else p i * (Real.log (p i) - Real.log (q i)))) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hqne : q i ≠ 0 := ne_of_gt (hq_pos i)
      simp [hpi, Real.log_div, hqne]
  have hcalc2 :
      (∑ i, (if p i = 0 then 0 else p i * (Real.log (p i) - Real.log (q i)))) =
        (∑ i, (if p i = 0 then 0 else p i * Real.log (p i))) -
          (∑ i, (if p i = 0 then 0 else p i * Real.log (q i))) := by
    have hsplit :
        (∑ i, (if p i = 0 then 0 else p i * (Real.log (p i) - Real.log (q i)))) =
          (∑ i, ((if p i = 0 then 0 else p i * Real.log (p i)) -
            (if p i = 0 then 0 else p i * Real.log (q i)))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hpi : p i = 0
      · simp [hpi]
      · simp [hpi, mul_sub]
    rw [hsplit]
    exact (Finset.sum_sub_distrib
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => if p i = 0 then 0 else p i * Real.log (p i))
      (g := fun i => if p i = 0 then 0 else p i * Real.log (q i)))
  have hcalc3 :
      ((∑ i, (if p i = 0 then 0 else p i * Real.log (p i))) -
        (∑ i, (if p i = 0 then 0 else p i * Real.log (q i)))) =
        ((∑ i, g (p i)) - (∑ i, p i * Real.log (q i))) := by
    have hsum_if :
        (∑ i, (if p i = 0 then 0 else p i * Real.log (p i))) =
          (∑ i, p i * Real.log (p i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hpi : p i = 0
      · simp [hpi]
      · simp [hpi]
    calc
      (∑ i, (if p i = 0 then 0 else p i * Real.log (p i))) -
          (∑ i, (if p i = 0 then 0 else p i * Real.log (q i))) =
        (∑ i, p i * Real.log (p i)) -
          (∑ i, (if p i = 0 then 0 else p i * Real.log (q i))) := by
            simp [hsum_if]
      _ = (∑ i, g (p i)) -
          (∑ i, (if p i = 0 then 0 else p i * Real.log (q i))) := by
            simp [g]
      _ = (∑ i, g (p i)) - (∑ i, p i * Real.log (q i)) := by
            refine congrArg (fun t => (∑ i, g (p i)) - t) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hpi : p i = 0
            · simp [hpi]
            · simp [hpi]
  have hcalc4 :
      ((∑ i, g (p i)) - (∑ i, p i * Real.log (q i))) =
        ((∑ i, g (p i)) - (∑ i, g (q i)) -
          ∑ i, (Real.log (q i) + 1) * (p i - q i)) := by
    -- use simplex sums
    have : (∑ i, (Real.log (q i) + 1) * (p i - q i)) =
        (∑ i, p i * Real.log (q i)) - (∑ i, g (q i)) + (∑ i, p i - ∑ i, q i) := by
      calc
        ∑ i, (Real.log (q i) + 1) * (p i - q i)
            = ∑ i, ((Real.log (q i) * p i - Real.log (q i) * q i) + (p i - q i)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (∑ i, (Real.log (q i) * p i - Real.log (q i) * q i)) +
            (∑ i, (p i - q i)) := by
                simp [Finset.sum_add_distrib]
        _ = (∑ i, Real.log (q i) * p i) - (∑ i, Real.log (q i) * q i) +
            (∑ i, p i - ∑ i, q i) := by
                have h1 :
                    ∑ i, (Real.log (q i) * p i - Real.log (q i) * q i) =
                      (∑ i, Real.log (q i) * p i) - (∑ i, Real.log (q i) * q i) := by
                    exact (Finset.sum_sub_distrib
                      (s := (Finset.univ : Finset (Fin n)))
                      (f := fun i => Real.log (q i) * p i)
                      (g := fun i => Real.log (q i) * q i))
                have h2 : ∑ i, (p i - q i) = (∑ i, p i) - (∑ i, q i) := by
                  exact (Finset.sum_sub_distrib
                    (s := (Finset.univ : Finset (Fin n)))
                    (f := fun i => p i) (g := fun i => q i))
                calc
                  (∑ i, (Real.log (q i) * p i - Real.log (q i) * q i)) +
                      (∑ i, (p i - q i)) =
                    ((∑ i, Real.log (q i) * p i) - (∑ i, Real.log (q i) * q i)) +
                      ((∑ i, p i) - (∑ i, q i)) := by
                    rw [h1, h2]
                  _ = (∑ i, Real.log (q i) * p i) - (∑ i, Real.log (q i) * q i) +
                      (∑ i, p i - ∑ i, q i) := by
                    ring
        _ = (∑ i, p i * Real.log (q i)) - (∑ i, g (q i)) +
            (∑ i, p i - ∑ i, q i) := by
            simp [g, mul_comm]
    -- simplify
    have hsum_pq' : (∑ i, p i - ∑ i, q i) = 0 := by
      simp [hp_sum, hq_sum]
    -- rearrange
    linarith [this, hsum_pq']
  have hkl :
      (∑ a, if p a = 0 then 0 else p a * Real.log (p a / q a)) =
        (∑ i, g (p i)) - (∑ i, g (q i)) -
          ∑ i, (Real.log (q i) + 1) * (p i - q i) := by
    calc
      (∑ a, if p a = 0 then 0 else p a * Real.log (p a / q a))
          = (∑ i, (if p i = 0 then 0 else p i * (Real.log (p i) - Real.log (q i)))) := hcalc1
      _ = (∑ i, (if p i = 0 then 0 else p i * Real.log (p i))) -
          (∑ i, (if p i = 0 then 0 else p i * Real.log (q i))) := hcalc2
      _ = (∑ i, g (p i)) - (∑ i, p i * Real.log (q i)) := hcalc3
      _ = (∑ i, g (p i)) - (∑ i, g (q i)) -
          ∑ i, (Real.log (q i) + 1) * (p i - q i) := hcalc4
  calc
    (∑ a, if p a = 0 then 0 else p a * Real.log (p a / q a))
        = (∑ i, g (p i)) - (∑ i, g (q i)) -
          ∑ i, (Real.log (q i) + 1) * (p i - q i) := hkl
    _ = (negEntropyConfig n (toConfig p)) -
        (negEntropyConfig n (toConfig q)) -
        inner ℝ (gradient (negEntropyConfig n) (toConfig q)) (toConfig p - toConfig q) := by
          simp [hneg_p, hneg_q, hinner]

/-- KL nonnegativity via Bregman divergence. -/
axiom kl_nonneg_via_bregman (n : ℕ) (p q : Fin n → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1) :
    0 ≤ Gibbs.Hamiltonian.Entropy.klDivergence p q

/-! ## Legendre Dual of Negative Entropy -/

/-- The Legendre dual of negative entropy is log-sum-exp.

    PROVIDED SOLUTION
    The upper bound follows from Jensen's inequality: for any distribution x
    on the simplex, Σ xᵢ θᵢ - Σ xᵢ log xᵢ ≤ log(Σ exp θᵢ). The lower bound
    is attained at the softmax distribution xᵢ = exp(θᵢ)/Σ exp(θⱼ), where
    direct computation gives ⟪θ, x⟫ + H(x) = log(Σ exp θᵢ). -/
theorem legendre_negEntropy_eq_logSumExp (n : ℕ) [NeZero n] (θ : Config n) :
    legendre (negEntropyConfig n) θ =
      Real.log (∑ i : Fin n, Real.exp ((fromConfig θ) i)) := by
  sorry

/-- Softmax distribution. -/
def softmax (n : ℕ) (θ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.exp (θ i) / ∑ j, Real.exp (θ j)

/-- Softmax is nonnegative. -/
theorem softmax_nonneg (n : ℕ) (θ : Fin n → ℝ) (i : Fin n) :
    0 ≤ softmax n θ i := by
  unfold softmax
  have hsum : 0 ≤ ∑ j, Real.exp (θ j) := by
    exact Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)
  have hden : 0 ≤ (∑ j, Real.exp (θ j))⁻¹ := by
    exact inv_nonneg.mpr hsum
  -- division as multiplication by inverse
  simpa [div_eq_mul_inv] using mul_nonneg (Real.exp_nonneg _) hden

/-- Softmax sums to one. -/
theorem softmax_sum_one (n : ℕ) [NeZero n] (θ : Fin n → ℝ) :
    ∑ i, softmax n θ i = 1 := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let i0 : Fin n := ⟨0, hn⟩
  have hmem : i0 ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hpos_term : 0 < Real.exp (θ i0) := Real.exp_pos _
  have hle : Real.exp (θ i0) ≤ ∑ j, Real.exp (θ j) := by
    exact Finset.single_le_sum (f := fun j => Real.exp (θ j))
      (fun _ _ => (Real.exp_pos _).le) hmem
  have hpos : 0 < ∑ j, Real.exp (θ j) := lt_of_lt_of_le hpos_term hle
  have hne : (∑ j, Real.exp (θ j)) ≠ 0 := ne_of_gt hpos
  calc
    ∑ i, softmax n θ i
        = ∑ i, Real.exp (θ i) / ∑ j, Real.exp (θ j) := by rfl
    _ = (∑ i, Real.exp (θ i)) / (∑ j, Real.exp (θ j)) := by
        simpa using (Finset.sum_div (s := (Finset.univ : Finset (Fin n)))
          (f := fun i => Real.exp (θ i)) (a := ∑ j, Real.exp (θ j))).symm
    _ = 1 := by field_simp [hne]

/-- Free energy is a scaled Legendre dual of negative entropy. -/
axiom freeEnergy_eq_scaled_legendre_dual (n : ℕ) [NeZero n]
    (H : Fin n → ℝ) (β : ℝ) (hβ : 0 < β) :
    PartitionFunction.freeEnergy H β =
      -(1/β) * legendre (negEntropyConfig n) (toConfig (fun i => -β * H i))

end

end Gibbs.Hamiltonian.EntropyBregman
