import Gibbs.Hamiltonian.Examples.GradientDescent

/-
The Problem. Provide a full proof of existence and uniqueness of minimizers
for strongly convex objectives in the heavy-ball setup.

This file mirrors the reference proof structure in `work/ball.lean`, but is
kept separate so the main example remains lightweight.
-/

namespace Gibbs.Hamiltonian.Examples

open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ## Unique Minimizer for Strongly Convex Objectives -/

theorem exists_unique_minimizer_proof (f : Config n → ℝ) (m : ℝ)
    (hf : StronglyConvex f m) (hcont : Continuous f) :
    ∃! x, ∀ y, f x ≤ f y := by
  classical
  -- Step 1: Strong convexity implies strict convexity.
  have h_strict_convex : StrictConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ hxy a b ha hb hab
    -- Use strong convexity at the convex combination.
    have hx := hf.lower_bound (a • x + b • y) x
    have hy := hf.lower_bound (a • x + b • y) y
    -- Follow the reference proof structure from `work/ball.lean`.
    simp_all +decide [← eq_sub_iff_add_eq']
    have h_simplify :
        m / 2 * (‖x - (a • x + (1 - a) • y)‖ ^ 2 * a +
          ‖y - (a • x + (1 - a) • y)‖ ^ 2 * (1 - a)) > 0 := by
      refine
        mul_pos (half_pos hf.m_pos)
          (add_pos_of_nonneg_of_pos
            (mul_nonneg (sq_nonneg _) ha.le)
            (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr ?_)) (sub_pos.mpr hb)))
      · intro h
        have h' : y = a • x + (1 - a) • y := by
          simpa [sub_eq_zero] using h
        have h'' : a • y = a • x := by
          have h'' := congrArg (fun v => v - (1 - a) • y) h'
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul] using h''
        have ha' : (a : ℝ) ≠ 0 := ne_of_gt ha
        have hxy' : y = x := by
          have h''' := congrArg (fun v => (1 / a) • v) h''
          -- Cancel the nonzero scalar `a`.
          simpa [smul_smul, ha', mul_comm, mul_left_comm, mul_assoc] using h'''
        exact hxy hxy'.symm
    norm_num [inner_sub_left, inner_sub_right] at *
    norm_num [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right] at *
    nlinarith

  -- Step 2: Coercivity (quadratic growth) with explicit radius.
  have h_coercive :
      ∀ R > 0, ∃ r > 0, ∀ x : Config n, r ≤ ‖x‖ → f x ≥ f 0 + R := by
    intro R hR_pos
    let b : ℝ := ‖gradient f 0‖
    let r : ℝ := max (4 * b / m) (max (4 * R / m) 1)
    have hr_pos : 0 < r := by
      have h1 : (1 : ℝ) ≤ r := by
        have h1' : (1 : ℝ) ≤ max (4 * R / m) 1 := le_max_right _ _
        have h1'' : max (4 * R / m) 1 ≤ r := le_max_right _ _
        exact le_trans h1' h1''
      exact lt_of_lt_of_le (by norm_num) h1
    refine ⟨r, hr_pos, ?_⟩
    intro x hx
    set t : ℝ := ‖x‖ with ht
    have ht_nonneg : 0 ≤ t := by
      simp [ht]
    have ht_ge_r : r ≤ t := by simpa [ht] using hx
    have ht_ge_b : 4 * b / m ≤ t := by
      have h1 : 4 * b / m ≤ r := le_max_left _ _
      exact le_trans h1 ht_ge_r
    have ht_ge_R : 4 * R / m ≤ t := by
      have h1 : 4 * R / m ≤ max (4 * R / m) 1 := le_max_left _ _
      have h2 : max (4 * R / m) 1 ≤ r := le_max_right _ _
      exact le_trans (le_trans h1 h2) ht_ge_r
    have ht_ge_one : (1 : ℝ) ≤ t := by
      have h1 : (1 : ℝ) ≤ max (4 * R / m) 1 := le_max_right _ _
      have h2 : max (4 * R / m) 1 ≤ r := le_max_right _ _
      exact le_trans (le_trans h1 h2) ht_ge_r
    have hbt : b * t ≤ (m / 4) * t ^ 2 := by
      have hm_nonneg : 0 ≤ m := le_of_lt hf.m_pos
      have ht_nonneg' : 0 ≤ t / 4 := by nlinarith [ht_nonneg]
      have h1 : m * (4 * b / m) ≤ m * t := by
        exact mul_le_mul_of_nonneg_left ht_ge_b hm_nonneg
      have h1' : 4 * b ≤ m * t := by
        have hm_ne : m ≠ 0 := ne_of_gt hf.m_pos
        have h1' := h1
        field_simp [hm_ne] at h1'
        simpa [mul_comm, mul_left_comm, mul_assoc] using h1'
      have hmul : (t / 4) * (4 * b) ≤ (t / 4) * (m * t) := by
        exact mul_le_mul_of_nonneg_left h1' ht_nonneg'
      -- Simplify to obtain b * t ≤ (m/4) * t^2.
      have hm_ne : m ≠ 0 := ne_of_gt hf.m_pos
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hm_ne, ht, pow_two] using hmul
    have hRt : R ≤ (m / 4) * t ^ 2 := by
      have hm_nonneg : 0 ≤ m := le_of_lt hf.m_pos
      have ht_sq_ge : t ≤ t ^ 2 := by nlinarith [ht_ge_one]
      have h1 : m * t ≤ m * t ^ 2 := by
        exact mul_le_mul_of_nonneg_left ht_sq_ge hm_nonneg
      have h2 : 4 * R ≤ m * t := by
        have hm_nonneg' : 0 ≤ m := le_of_lt hf.m_pos
        have h2' : m * (4 * R / m) ≤ m * t := by
          exact mul_le_mul_of_nonneg_left ht_ge_R hm_nonneg'
        have hm_ne : m ≠ 0 := ne_of_gt hf.m_pos
        have h2'' := h2'
        field_simp [hm_ne] at h2''
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2''
      have h3 : 4 * R ≤ m * t ^ 2 := le_trans h2 h1
      have hm_ne : m ≠ 0 := ne_of_gt hf.m_pos
      nlinarith [h3, hm_ne]
    have hinner : inner (𝕜 := ℝ) (gradient f 0) x ≥ -b * t := by
      have h := abs_real_inner_le_norm (gradient f 0) x
      have h' := (abs_le.mp h).1
      nlinarith [h']
    have hbound := hf.lower_bound 0 x
    have hbound' :
        f x ≥ f 0 + inner (𝕜 := ℝ) (gradient f 0) x + (m / 2) * t ^ 2 := by
      simpa [ht] using hbound
    have hbound'' : f x ≥ f 0 - b * t + (m / 2) * t ^ 2 := by
      linarith [hbound', hinner]
    have hquad :
        (m / 2) * t ^ 2 - b * t ≥ R := by
      calc
        (m / 2) * t ^ 2 - b * t
            ≥ (m / 2) * t ^ 2 - (m / 4) * t ^ 2 := by
                  have := hbt
                  nlinarith
        _ = (m / 4) * t ^ 2 := by ring
        _ ≥ R := hRt
    nlinarith [hbound'', hquad]

  -- Step 3: Existence on a closed ball.
  obtain ⟨x_star, hx_star⟩ :
      ∃ x_star ∈ Metric.closedBall (0 : Config n) (Classical.choose (h_coercive 1 zero_lt_one)),
        ∀ y ∈ Metric.closedBall (0 : Config n) (Classical.choose (h_coercive 1 zero_lt_one)),
          f x_star ≤ f y := by
    have h_continuous :
        ContinuousOn f (Metric.closedBall (0 : Config n) (Classical.choose (h_coercive 1 zero_lt_one))) :=
      hcont.continuousOn
    exact
      (IsCompact.exists_isMinOn (ProperSpace.isCompact_closedBall _ _)
        ⟨0, by
          have hr_nonneg :
              0 ≤ Classical.choose (h_coercive 1 zero_lt_one) :=
            (Classical.choose_spec (h_coercive 1 zero_lt_one)).1.le
          exact Metric.mem_closedBall_self hr_nonneg⟩
        h_continuous) |>
        fun ⟨x, hx₁, hx₂⟩ => ⟨x, hx₁, fun y hy => hx₂ hy⟩

  -- Extend minimizer to all of space using coercivity.
  obtain ⟨x_star, hx_star'⟩ : ∃ x_star, ∀ y, f x_star ≤ f y := by
    refine ⟨x_star, ?_⟩
    intro y
    by_cases hy :
        y ∈ Metric.closedBall (0 : Config n) (Classical.choose (h_coercive 1 zero_lt_one))
    · exact hx_star.2 y hy
    · have h_far :
        f y ≥ f 0 + 1 :=
        (Classical.choose_spec (h_coercive 1 zero_lt_one)).2 y (by
          have hy' : Classical.choose (h_coercive 1 zero_lt_one) < ‖y‖ := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hy
          exact le_of_lt hy')
      have h0 : f x_star ≤ f 0 := by
        have hr_nonneg :
            0 ≤ Classical.choose (h_coercive 1 zero_lt_one) :=
          (Classical.choose_spec (h_coercive 1 zero_lt_one)).1.le
        exact hx_star.2 0 (Metric.mem_closedBall_self hr_nonneg)
      linarith

  -- Step 4: Uniqueness by strict convexity.
  refine ⟨x_star, hx_star', ?_⟩
  intro y hy
  by_contra h_neq
  have h_midpoint :
      f ((1 / 2 : ℝ) • x_star + (1 / 2 : ℝ) • y) <
        (1 / 2 : ℝ) * f x_star + (1 / 2 : ℝ) * f y := by
    apply_rules [h_strict_convex.2] <;> norm_num [h_neq]
    exact Ne.symm h_neq
  linarith [hx_star' ((1 / 2 : ℝ) • x_star + (1 / 2 : ℝ) • y),
    hy ((1 / 2 : ℝ) • x_star + (1 / 2 : ℝ) • y)]

/-- Existence of a unique minimizer for a strongly convex function. -/
theorem exists_unique_minimizer (f : Config n → ℝ) (m : ℝ)
    (hf : StronglyConvex f m) (hcont : Continuous f) :
    ∃! x, ∀ y, f x ≤ f y :=
  exists_unique_minimizer_proof (f := f) (m := m) hf hcont

/-- Chosen minimizer of a strongly convex function. -/
noncomputable def minimizer (f : Config n → ℝ) (m : ℝ)
    (hf : StronglyConvex f m) (hcont : Continuous f) : Config n :=
  Classical.choose (exists_unique_minimizer (n := n) f m hf hcont)

/-- Characterization of the chosen minimizer. -/
theorem minimizer_spec (f : Config n → ℝ) (m : ℝ)
    (hf : StronglyConvex f m) (hcont : Continuous f) :
    ∀ y, f (minimizer (n := n) f m hf hcont) ≤ f y :=
  (Classical.choose_spec (exists_unique_minimizer (n := n) f m hf hcont)).1

end

end Gibbs.Hamiltonian.Examples
