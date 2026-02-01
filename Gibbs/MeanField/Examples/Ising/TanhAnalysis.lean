import Gibbs.MeanField.Projection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Analytic Properties of tanh

The mean-field Ising model depends on tanh being 1-Lipschitz (ensuring the
drift is Lipschitz) and strictly sublinear (tanh(x) < x for x > 0, which
forces the unique-equilibrium result in the paramagnetic phase). This file
proves these properties from the derivative bound d/dx tanh(x) = 1/cosh(x)^2
le 1, using the mean value theorem for the Lipschitz bound and a monotonicity
argument for strict sublinearity.
-/

namespace Gibbs.MeanField.Examples

open scoped Classical

noncomputable section

/-! ## Derivative of sinh/cosh -/

/-- sinh/cosh is differentiable everywhere. -/
private theorem differentiable_sinh_div_cosh :
    Differentiable ℝ (fun x => Real.sinh x / Real.cosh x) := by
  -- cosh is never zero, so the quotient is differentiable
  intro x
  exact Real.differentiable_sinh.differentiableAt.div
    Real.differentiable_cosh.differentiableAt (ne_of_gt (Real.cosh_pos x))

/-- Derivative of sinh/cosh is 1/cosh². -/
private theorem deriv_sinh_div_cosh (x : ℝ) :
    deriv (fun y => Real.sinh y / Real.cosh y) x = 1 / (Real.cosh x) ^ 2 := by
  -- Apply quotient rule and simplify via cosh² - sinh² = 1
  have hcosh_ne : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hsinh_diff := Real.differentiable_sinh.differentiableAt (x := x)
  have hcosh_diff := Real.differentiable_cosh.differentiableAt (x := x)
  rw [deriv_fun_div hsinh_diff hcosh_diff hcosh_ne]
  simp only [Real.deriv_sinh, Real.deriv_cosh]
  -- Use cosh² - sinh² = 1 to simplify
  have hid : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  field_simp
  linarith [hid]

/-- |deriv(sinh/cosh) x| ≤ 1 since 1/cosh² ≤ 1. -/
private theorem abs_deriv_sinh_div_cosh_le_one (x : ℝ) :
    |deriv (fun y => Real.sinh y / Real.cosh y) x| ≤ 1 := by
  rw [deriv_sinh_div_cosh]
  have hcosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hcosh_sq_pos : 0 < (Real.cosh x) ^ 2 := sq_pos_of_pos hcosh_pos
  rw [abs_of_pos (div_pos one_pos hcosh_sq_pos), div_le_one hcosh_sq_pos]
  -- 1 ≤ cosh² since cosh ≥ 1
  calc 1 = 1 ^ 2 := by ring
    _ ≤ (Real.cosh x) ^ 2 := sq_le_sq' (by linarith [Real.one_le_cosh x])
                                        (Real.one_le_cosh x)

/-! ## Lipschitz property -/

/-- Key inequality: |tanh x - tanh y| ≤ |x - y| (tanh is 1-Lipschitz). -/
theorem Real.abs_tanh_sub_tanh_le (x y : ℝ) :
    |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  -- Rewrite tanh as sinh/cosh and apply MVT
  have heq : ∀ z, Real.tanh z = Real.sinh z / Real.cosh z := Real.tanh_eq_sinh_div_cosh
  rw [heq x, heq y]
  have hdiff : ∀ z ∈ Set.univ, DifferentiableAt ℝ (fun t => Real.sinh t / Real.cosh t) z :=
    fun z _ => differentiable_sinh_div_cosh z
  have hbound : ∀ z ∈ Set.univ, ‖deriv (fun t => Real.sinh t / Real.cosh t) z‖ ≤ 1 :=
    fun z _ => by rw [Real.norm_eq_abs]; exact abs_deriv_sinh_div_cosh_le_one z
  -- MVT gives |f(y) - f(x)| ≤ 1 * |y - x|
  have hmvt := convex_univ.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (Set.mem_univ x) (Set.mem_univ y)
  simp only [Real.norm_eq_abs, one_mul] at hmvt
  -- Swap argument order to match goal
  calc |Real.sinh x / Real.cosh x - Real.sinh y / Real.cosh y|
      = |Real.sinh y / Real.cosh y - Real.sinh x / Real.cosh x| := abs_sub_comm _ _
    _ ≤ |y - x| := hmvt
    _ = |x - y| := abs_sub_comm _ _

/-! ## Strict sub-linearity -/

/-- tanh(x) < 1 for all x. -/
theorem tanh_lt_one (x : ℝ) : Real.tanh x < 1 := by
  -- sinh < cosh since exp(-x) > 0
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos x)]
  rw [Real.sinh_eq x, Real.cosh_eq x]
  linarith [Real.exp_pos (-x)]

/-- Auxiliary function for tanh_lt_self: g(t) = (t+1)exp(-t) - (1-t)exp(t).
    We show g(0)=0 and g is strictly increasing on ℝ⁺. -/
private def tanh_aux (t : ℝ) : ℝ := (t + 1) * Real.exp (-t) - (1 - t) * Real.exp t

/-- g(0) = 0 -/
private theorem tanh_aux_zero : tanh_aux 0 = 0 := by simp [tanh_aux]

/-- g has derivative 2t·sinh(t) at every point. -/
private theorem tanh_aux_hasDerivAt (t : ℝ) :
    HasDerivAt tanh_aux (2 * t * Real.sinh t) t := by
  -- Compute derivatives of each factor using product rule
  have h1 : HasDerivAt (fun t => t + 1) 1 t := (hasDerivAt_id t).add_const 1
  have h2 : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := by
    convert HasDerivAt.comp t (Real.hasDerivAt_exp (-t)) (hasDerivAt_neg t) using 1; ring
  have h3 := h1.mul h2
  have h4 : HasDerivAt (fun t => 1 - t) (-1) t := by
    convert (hasDerivAt_const t 1).sub (hasDerivAt_id t) using 1; ring
  have h5 := h4.mul (Real.hasDerivAt_exp t)
  -- Combine and simplify to 2t·sinh(t)
  convert h3.sub h5 using 1
  rw [Real.sinh_eq t]; field_simp; ring

/-- g is strictly increasing on [0, x] for x > 0 (since g'(t) > 0 for t > 0). -/
private theorem tanh_aux_strictMono_on {x : ℝ} (_hx : 0 < x) :
    StrictMonoOn tanh_aux (Set.Icc 0 x) := by
  -- g is continuous and g'(t) > 0 on (0, x)
  have hcont : ContinuousOn tanh_aux (Set.Icc 0 x) := by
    apply ContinuousOn.sub
    · exact (continuous_add_right 1).continuousOn.mul
        (Real.continuous_exp.comp continuous_neg).continuousOn
    · exact (continuous_const.sub continuous_id).continuousOn.mul
        Real.continuous_exp.continuousOn
  have hderiv_pos : ∀ t ∈ interior (Set.Icc 0 x), 0 < deriv tanh_aux t := by
    intro t ht; rw [interior_Icc] at ht
    rw [(tanh_aux_hasDerivAt t).deriv]
    -- 2t·sinh(t) > 0 when t > 0
    exact mul_pos (by linarith [ht.1]) (Real.sinh_pos_iff.mpr ht.1)
  exact strictMonoOn_of_deriv_pos (convex_Icc 0 x) hcont hderiv_pos

/-- Strict inequality: tanh(x) < x for x > 0.
    Proof: For x ≥ 1, tanh < 1 ≤ x. For 0 < x < 1, use g(x) > g(0) = 0
    where g(t) = (t+1)exp(-t) - (1-t)exp(t). -/
theorem Real.tanh_lt_self (x : ℝ) (hx : 0 < x) : Real.tanh x < x := by
  -- Large x: tanh < 1 ≤ x
  by_cases hx1 : x ≥ 1
  · linarith [tanh_lt_one x]
  · -- Small x: use auxiliary function g
    push_neg at hx1
    -- g(x) > g(0) = 0 by strict monotonicity
    have hgx_pos : tanh_aux x > 0 := by
      have hmono := tanh_aux_strictMono_on hx
      have hgx := hmono (Set.left_mem_Icc.mpr (le_of_lt hx)) (Set.right_mem_Icc.mpr (le_of_lt hx)) hx
      rw [tanh_aux_zero] at hgx; exact hgx
    -- g(x) > 0 means (x+1)exp(-x) > (1-x)exp(x), which gives tanh(x) < x
    have hsum_pos : 0 < Real.exp x + Real.exp (-x) := by positivity
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq x, Real.cosh_eq x]
    have h : (Real.exp x - Real.exp (-x)) / 2 / ((Real.exp x + Real.exp (-x)) / 2)
        = (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x)) := by field_simp
    rw [h, div_lt_iff₀ hsum_pos]
    -- Expand and use g(x) > 0
    simp only [tanh_aux, sub_pos] at hgx_pos
    ring_nf; linarith [hgx_pos]

/-- x < tanh(x) for x < 0 (by oddness of tanh). -/
theorem Real.self_lt_tanh (x : ℝ) (hx : x < 0) : x < Real.tanh x := by
  have := Real.tanh_lt_self (-x) (neg_pos.mpr hx)
  simp only [Real.tanh_neg] at this; linarith

/-- |tanh(x)| < |x| for x ≠ 0. -/
theorem Real.abs_tanh_lt_abs (x : ℝ) (hx : x ≠ 0) : |Real.tanh x| < |x| := by
  rcases hx.lt_or_gt with hneg | hpos
  · -- x < 0: use self_lt_tanh and sign analysis
    have h := Real.self_lt_tanh x hneg
    have htanh_neg : Real.tanh x < 0 := by
      have hsinh_pos : 0 < Real.sinh (-x) := Real.sinh_pos_iff.mpr (neg_pos.mpr hneg)
      have hpos_tanh : 0 < Real.tanh (-x) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_pos hsinh_pos (Real.cosh_pos (-x))
      simp only [Real.tanh_neg] at hpos_tanh; linarith
    rw [abs_of_neg htanh_neg, abs_of_neg hneg]; linarith
  · -- x > 0: direct from tanh_lt_self
    have h := Real.tanh_lt_self x hpos
    have htanh_pos : 0 < Real.tanh x := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr hpos) (Real.cosh_pos x)
    rw [abs_of_pos htanh_pos, abs_of_pos hpos]; exact h

/-! ## Derivative and continuity of tanh -/

/-- Derivative of tanh at a point: tanh'(x) = 1/cosh²(x). -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / (Real.cosh x) ^ 2) x := by
  -- Rewrite tanh as sinh/cosh and apply quotient rule
  have hcosh_ne : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have heq : Real.tanh = fun y => Real.sinh y / Real.cosh y := funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  have h := (Real.differentiable_sinh x).hasDerivAt.div
    (Real.differentiable_cosh x).hasDerivAt hcosh_ne
  simp only [Real.deriv_sinh, Real.deriv_cosh] at h
  convert h using 1
  -- Simplify via cosh² - sinh² = 1
  have hid : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  field_simp; linarith [hid]

/-- tanh is continuous (derived from sinh and cosh). -/
theorem continuous_tanh : Continuous Real.tanh := by
  have heq : Real.tanh = fun y => Real.sinh y / Real.cosh y := funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Continuous.div Real.continuous_sinh Real.continuous_cosh
    (fun x => ne_of_gt (Real.cosh_pos x))

end

end Gibbs.MeanField.Examples
