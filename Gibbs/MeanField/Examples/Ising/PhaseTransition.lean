import Gibbs.MeanField.Examples.Ising.Drift

/-
The Problem. Prove the phase transition in the mean-field Ising model:
paramagnetic phase (βJ < 1) has unique equilibrium m=0, while
ferromagnetic phase (βJ > 1) has two nonzero equilibria ±m*.

Solution Structure.
1. Self-consistency equation: m = tanh(βJm)
2. Paramagnetic: |tanh(βJm)| < |βJm| ≤ |m| forces m = 0
3. Ferromagnetic: IVT on f(m) = m - tanh(βJm) with f'(0) < 0
-/

namespace Gibbs.MeanField.Examples

open Gibbs.MeanField

open scoped Classical

noncomputable section

/-! ## Self-Consistency and Equilibria -/

/-- Self-consistency equation: m* = tanh(β(Jm* + h)). -/
def isSelfConsistent (p : IsingParams) (m : ℝ) : Prop :=
  m = Real.tanh (p.β * (p.J * m + p.h))

/-- Equilibrium magnetizations are self-consistent solutions in [-1, 1]. -/
def equilibriumMagnetizations (p : IsingParams) : Set ℝ :=
  { m | isSelfConsistent p m ∧ -1 ≤ m ∧ m ≤ 1 }

/-- m = 0 is always a solution when h = 0. -/
theorem zero_is_equilibrium (p : IsingParams) (hh : p.h = 0) :
    0 ∈ equilibriumMagnetizations p := by
  simp only [equilibriumMagnetizations, isSelfConsistent, Set.mem_setOf_eq]
  exact ⟨by simp [hh], by constructor <;> norm_num⟩

/-! ## Paramagnetic Phase -/

/-- When J ≥ 0 and βJ < 1, the strict sub-linearity |tanh(x)| < |x|
    forces any self-consistent m ≠ 0 to satisfy 1 < βJ, a contradiction. -/
private theorem paramagnetic_J_nonneg (p : IsingParams) (hh : p.h = 0)
    (hpara : p.isParamagnetic) (hJ : p.J ≥ 0) (m : ℝ) (hsc : m = Real.tanh (p.β * (p.J * m)))
    (hm_ne : m ≠ 0) : False := by
  -- Handle J = 0 separately
  by_cases hJ_eq : p.J = 0
  · -- tanh(0) = 0, contradicts m ≠ 0
    rw [hJ_eq, show p.β * (0 * m) = 0 from by ring, Real.tanh_zero] at hsc
    exact hm_ne hsc
  · -- J > 0: use |tanh(x)| < |x| to get |m| < βJ|m|, so 1 < βJ
    have hJ_pos : p.J > 0 := lt_of_le_of_ne hJ (Ne.symm hJ_eq)
    have hβJm_ne : p.β * (p.J * m) ≠ 0 := by
      intro h; simp only [mul_eq_zero] at h
      rcases h with hβ | h
      · exact (ne_of_gt p.β_pos) hβ
      · rcases h with hJ' | hm'; exact hJ_eq hJ'; exact hm_ne hm'
    have h1 : |m| = |Real.tanh (p.β * (p.J * m))| := congrArg abs hsc
    have h2 := Real.abs_tanh_lt_abs _ hβJm_ne
    have h3 : |p.β * (p.J * m)| = p.β * p.J * |m| := by
      rw [abs_mul, abs_mul, abs_of_pos p.β_pos, abs_of_pos hJ_pos]; ring
    -- |m| = |tanh(βJm)| < |βJm| = βJ|m|, so 1 < βJ
    have hm_pos : 0 < |m| := abs_pos.mpr hm_ne
    have h4 : |m| < p.β * p.J * |m| := lt_of_eq_of_lt h1 (lt_of_lt_of_eq h2 h3)
    have h5 : 1 < p.β * p.J := by
      by_contra h; push_neg at h
      linarith [mul_le_mul_of_nonneg_right h (le_of_lt hm_pos)]
    have : p.β * p.J < 1 := hpara; linarith

/-- When J < 0, tanh(βJm) has opposite sign to m, so m = tanh(βJm) forces m = 0. -/
private theorem paramagnetic_J_neg (p : IsingParams)
    (hJ : p.J < 0) (m : ℝ) (hsc : m = Real.tanh (p.β * (p.J * m)))
    (hm_ne : m ≠ 0) : False := by
  by_cases hm_pos : m > 0
  · -- m > 0 ⟹ βJm < 0 ⟹ tanh(βJm) < 0, but m = tanh(βJm) > 0
    have : p.β * (p.J * m) < 0 := mul_neg_of_pos_of_neg p.β_pos (mul_neg_of_neg_of_pos hJ hm_pos)
    have : Real.tanh (p.β * (p.J * m)) < 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr this) (Real.cosh_pos _)
    linarith [hsc]
  · -- m < 0 ⟹ βJm > 0 ⟹ tanh(βJm) > 0, but m = tanh(βJm) < 0
    push_neg at hm_pos
    have hm_neg : m < 0 := lt_of_le_of_ne hm_pos hm_ne
    have : p.β * (p.J * m) > 0 := mul_pos p.β_pos (mul_pos_of_neg_of_neg hJ hm_neg)
    have : Real.tanh (p.β * (p.J * m)) > 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr this) (Real.cosh_pos _)
    linarith [hsc]

/-- In the paramagnetic phase (βJ < 1), m = 0 is the unique equilibrium.
    If m = tanh(βJm) and m ≠ 0, then |tanh(βJm)| < |βJm| = βJ|m| gives 1 < βJ,
    contradicting βJ < 1. For J < 0, sign analysis gives contradiction directly. -/
theorem paramagnetic_unique_equilibrium (p : IsingParams) (hh : p.h = 0)
    (hpara : p.isParamagnetic) :
    equilibriumMagnetizations p = {0} := by
  ext m
  simp only [equilibriumMagnetizations, isSelfConsistent, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Any equilibrium must be 0
    intro ⟨hsc, _, _⟩
    simp only [hh, add_zero] at hsc
    by_contra hm_ne
    by_cases hJ : p.J ≥ 0
    · exact paramagnetic_J_nonneg p hh hpara hJ m hsc hm_ne
    · exact paramagnetic_J_neg p (not_le.mp hJ) m hsc hm_ne
  · -- 0 is an equilibrium
    intro hm; rw [hm]
    exact ⟨by simp [hh], by constructor <;> norm_num⟩

/-! ## Ferromagnetic Phase -/

/-- Self-consistency residual f(m) = m - tanh(βJm). -/
private def selfConsistencyResidual (p : IsingParams) (m : ℝ) : ℝ :=
  m - Real.tanh (p.β * (p.J * m))

/-- f(0) = 0 -/
private theorem residual_zero (p : IsingParams) :
    selfConsistencyResidual p 0 = 0 := by simp [selfConsistencyResidual]

/-- f is continuous -/
private theorem residual_continuous (p : IsingParams) :
    Continuous (selfConsistencyResidual p) := by
  apply Continuous.sub continuous_id
  -- tanh(β(J·m)) = tanh(βJ·m) is continuous
  have : (fun m => Real.tanh (p.β * (p.J * m))) = (fun m => Real.tanh (p.β * p.J * m)) := by
    ext m; ring_nf
  rw [this]
  exact continuous_tanh.comp (continuous_const.mul continuous_id)

/-- f(1) > 0 since tanh < 1 -/
private theorem residual_one_pos (p : IsingParams) :
    selfConsistencyResidual p 1 > 0 := by
  simp only [selfConsistencyResidual, mul_one]
  linarith [tanh_lt_one (p.β * p.J)]

/-- f has derivative 1 - βJ at 0, which is negative when βJ > 1. -/
private theorem residual_hasDerivAt_zero (p : IsingParams) :
    HasDerivAt (selfConsistencyResidual p) (1 - p.β * p.J) 0 := by
  -- f = id - (tanh ∘ (βJ · ·))
  have h_id : HasDerivAt (fun (m : ℝ) => m) 1 (0 : ℝ) := hasDerivAt_id 0
  have h_inner : HasDerivAt (fun (m : ℝ) => p.β * p.J * m) (p.β * p.J) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (p.β * p.J)
  -- tanh'(0) = 1 (since cosh(0) = 1)
  have h_tanh_0 : HasDerivAt Real.tanh 1 0 := by
    have h := hasDerivAt_tanh 0
    simp only [Real.cosh_zero, one_pow, div_one] at h; exact h
  -- Chain rule: (tanh ∘ g)'(0) = tanh'(g(0)) · g'(0) = 1 · βJ = βJ
  have h_comp : HasDerivAt (fun (m : ℝ) => Real.tanh (p.β * p.J * m)) (p.β * p.J) (0 : ℝ) := by
    have h0 : p.β * p.J * (0 : ℝ) = 0 := mul_zero _
    have := (by rw [h0]; exact h_tanh_0 : HasDerivAt Real.tanh 1 (p.β * p.J * 0)).comp (0 : ℝ) h_inner
    simpa using this
  -- f(m) = m - tanh(βJ·m), and β(J·m) = βJ·m
  have h_eq : selfConsistencyResidual p = fun m => m - Real.tanh (p.β * p.J * m) := by
    ext m; simp only [selfConsistencyResidual]; ring_nf
  rw [h_eq]
  exact h_id.sub h_comp

/-- Near zero, f(ε) < 0 for small ε > 0 (since f(0) = 0 and f'(0) < 0). -/
private theorem residual_negative_near_zero (p : IsingParams)
    (hferro : p.isFerromagnetic) :
    ∃ ε > 0, ε < 1 ∧ selfConsistencyResidual p ε < 0 := by
  -- f'(0) = 1 - βJ < 0 when βJ > 1
  have hderiv_neg : deriv (selfConsistencyResidual p) 0 < 0 := by
    rw [(residual_hasDerivAt_zero p).deriv]
    have : p.β * p.J > 1 := hferro; linarith
  -- Use sign lemma: f(0) = 0 and f'(0) < 0 ⟹ sign(f(x)) = sign(-x) near 0
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hderiv_neg (residual_zero p)
  rw [Filter.Eventually, Metric.mem_nhds_iff] at hsign
  obtain ⟨r, hr_pos, hr_ball⟩ := hsign
  -- Take ε = min(r/2, 1/2)
  use min (r / 2) (1 / 2)
  refine ⟨lt_min (by linarith) (by norm_num), ?_, ?_⟩
  · calc min (r / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num
  · -- sign(f(ε)) = sign(-ε) = -1, so f(ε) < 0
    set ε := min (r / 2) (1 / 2) with hε_def
    have hε_pos : 0 < ε := lt_min (by linarith) (by norm_num)
    have hε_in_ball : ε ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε_pos]
      calc ε ≤ r / 2 := min_le_left _ _
        _ < r := by linarith
    have hsign_eq : SignType.sign (selfConsistencyResidual p ε) =
        SignType.sign (0 - ε) := hr_ball hε_in_ball
    rw [sign_eq_neg_one_iff.mpr (sub_neg.mpr hε_pos)] at hsign_eq
    exact sign_eq_neg_one_iff.mp hsign_eq

/-- In the ferromagnetic phase (βJ > 1), there are two nonzero equilibria ±m*.
    IVT applied to f(m) = m - tanh(βJm) on [ε, 1] where f(ε) < 0 < f(1),
    with oddness of tanh giving the negative solution. -/
theorem ferromagnetic_bistable (p : IsingParams) (hh : p.h = 0)
    (hferro : p.isFerromagnetic) :
    ∃ m₀ > 0, m₀ ∈ equilibriumMagnetizations p ∧
              -m₀ ∈ equilibriumMagnetizations p := by
  -- Get ε with f(ε) < 0 < f(1) and apply IVT
  obtain ⟨ε, hε_pos, hε_lt_one, hfε_neg⟩ := residual_negative_near_zero p hferro
  have hε_le_one : ε ≤ 1 := le_of_lt hε_lt_one
  have hcont_on : ContinuousOn (selfConsistencyResidual p) (Set.Icc ε 1) :=
    (residual_continuous p).continuousOn
  -- IVT: f(ε) < 0 < f(1), so ∃ m₀ ∈ [ε,1] with f(m₀) = 0
  have h0_in_range : (0 : ℝ) ∈ Set.Icc (selfConsistencyResidual p ε)
      (selfConsistencyResidual p 1) :=
    ⟨le_of_lt hfε_neg, le_of_lt (residual_one_pos p)⟩
  obtain ⟨m₀, hm₀_mem, hfm₀⟩ := intermediate_value_Icc hε_le_one hcont_on h0_in_range
  -- Extract properties
  have hm₀_pos : m₀ > 0 := lt_of_lt_of_le hε_pos hm₀_mem.1
  have hm₀_sc : m₀ = Real.tanh (p.β * (p.J * m₀)) := by
    simp only [selfConsistencyResidual, sub_eq_zero] at hfm₀; exact hfm₀
  use m₀, hm₀_pos
  constructor
  · -- m₀ is an equilibrium
    exact ⟨by simp only [isSelfConsistent, hh, add_zero]; exact hm₀_sc, by linarith, hm₀_mem.2⟩
  · -- -m₀ is an equilibrium by oddness of tanh
    refine ⟨?_, by constructor <;> linarith [hm₀_mem.2]⟩
    simp only [isSelfConsistent, hh, add_zero]
    -- tanh(βJ(-m₀)) = -tanh(βJm₀) = -m₀
    have : p.β * (p.J * (-m₀)) = -(p.β * (p.J * m₀)) := by ring
    rw [this, Real.tanh_neg, ← hm₀_sc]

end

end Gibbs.MeanField.Examples
