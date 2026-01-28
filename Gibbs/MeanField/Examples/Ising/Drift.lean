import Gibbs.MeanField.Projection
import Gibbs.MeanField.Examples.Ising.TanhAnalysis

/-
The Problem. Define the mean-field Ising drift function and prove it
forms a valid choreography (conserves probability and is Lipschitz).

Solution Structure.
1. IsingParams: model parameters (β, J, h, τ)
2. isingDrift: the ODE right-hand side
3. Conservation: dx_up + dx_down = 0
4. Lipschitz: drift is Lipschitz via tanh being 1-Lipschitz
-/

namespace Gibbs.MeanField.Examples

open Gibbs.MeanField

open scoped Classical

noncomputable section

/-! ## Ising Parameters -/

/-- Parameters for the mean-field Ising model. -/
structure IsingParams where
  /-- Inverse temperature β = 1/(k_B T) -/
  β : ℝ
  /-- Coupling strength (ferromagnetic if J > 0) -/
  J : ℝ
  /-- External magnetic field -/
  h : ℝ
  /-- Relaxation time scale -/
  τ : ℝ
  /-- Temperature is positive -/
  β_pos : β > 0
  /-- Time scale is positive -/
  τ_pos : τ > 0

namespace IsingParams

/-- Critical inverse temperature: β_c = 1/J (for h = 0). -/
def criticalβ (p : IsingParams) : ℝ := 1 / p.J

/-- System is in ferromagnetic phase (T < T_c). -/
def isFerromagnetic (p : IsingParams) : Prop := p.β * p.J > 1

/-- System is in paramagnetic phase (T > T_c). -/
def isParamagnetic (p : IsingParams) : Prop := p.β * p.J < 1

end IsingParams

/-! ## Ising Drift Function -/

/-- The mean-field Ising drift function.
    dm/dt = -(1/τ)(m - tanh(β(Jm + h)))
    Converted to dx_up/dt and dx_down/dt. -/
def isingDrift (p : IsingParams) : DriftFunction TwoState :=
  fun x =>
    let m := magnetizationOf x  -- m = 2x_up - 1
    let target := Real.tanh (p.β * (p.J * m + p.h))
    -- dm/dt = -(1/τ)(m - target), dx_up = (1/2)dm/dt
    fun q => match q with
      | .up   => -(1 / (2 * p.τ)) * (m - target)
      | .down =>  (1 / (2 * p.τ)) * (m - target)

/-! ## Conservation -/

/-- The Ising drift conserves probability: dx_up/dt + dx_down/dt = 0. -/
theorem isingDrift_conserves (p : IsingParams) :
    DriftFunction.Conserves (isingDrift p) := by
  intro x _
  -- up = -a, down = +a, sum = 0
  simp only [isingDrift]
  have key : ∀ (a : ℝ), -(1 / (2 * p.τ)) * a + (1 / (2 * p.τ)) * a = 0 := fun a => by ring
  conv_lhs => rw [show (Finset.univ : Finset TwoState) = {.up, .down} by ext q; fin_cases q <;> simp]
  rw [Finset.sum_pair TwoState.up_ne_down]
  exact key _

/-! ## Lipschitz Property -/

/-- Magnetization difference bound: |m_x - m_y| ≤ 2‖x - y‖. -/
private theorem magnetization_diff_bound (x y : TwoState → ℝ) :
    |magnetizationOf x - magnetizationOf y| ≤ 2 * ‖x - y‖ := by
  -- m = 2·x_up - 1, so |m_x - m_y| = 2|x_up - y_up|
  have hm_diff : |magnetizationOf x - magnetizationOf y| =
      2 * |x TwoState.up - y TwoState.up| := by
    simp only [magnetizationOf]
    have : 2 * x TwoState.up - 1 - (2 * y TwoState.up - 1) =
      2 * (x TwoState.up - y TwoState.up) := by ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- |x_up - y_up| ≤ ‖x - y‖ by pi norm
  have hcomp : |x TwoState.up - y TwoState.up| ≤ ‖x - y‖ := by
    have : ‖(x - y) TwoState.up‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) TwoState.up
    simp only [Pi.sub_apply, Real.norm_eq_abs] at this; exact this
  rw [hm_diff]
  exact mul_le_mul_of_nonneg_left hcomp (by norm_num)

/-- Component-level bound for the Ising drift difference. -/
private theorem isingDrift_component_bound (p : IsingParams) (x y : TwoState → ℝ) :
    |(magnetizationOf x - magnetizationOf y) -
     (Real.tanh (p.β * (p.J * magnetizationOf x + p.h)) -
      Real.tanh (p.β * (p.J * magnetizationOf y + p.h)))| ≤
    (1 + p.β * |p.J|) * |magnetizationOf x - magnetizationOf y| := by
  -- tanh argument difference simplifies to β·J·(m_x - m_y)
  set m_x := magnetizationOf x; set m_y := magnetizationOf y
  set t_x := Real.tanh (p.β * (p.J * m_x + p.h))
  set t_y := Real.tanh (p.β * (p.J * m_y + p.h))
  -- |t_x - t_y| ≤ β|J|·|m_x - m_y| by 1-Lipschitz of tanh
  have htanh_bound : |t_x - t_y| ≤ p.β * |p.J| * |m_x - m_y| := by
    have harg : p.β * (p.J * m_x + p.h) - p.β * (p.J * m_y + p.h) = p.β * p.J * (m_x - m_y) := by ring
    calc |t_x - t_y| ≤ |p.β * (p.J * m_x + p.h) - p.β * (p.J * m_y + p.h)| :=
          Real.abs_tanh_sub_tanh_le _ _
      _ = |p.β * p.J * (m_x - m_y)| := by rw [harg]
      _ = |p.β * p.J| * |m_x - m_y| := abs_mul _ _
      _ = p.β * |p.J| * |m_x - m_y| := by rw [abs_mul, abs_of_pos p.β_pos]
  -- Triangle inequality: |(m-m') - (t-t')| ≤ |m-m'| + |t-t'|
  calc |(m_x - m_y) - (t_x - t_y)| ≤ |m_x - m_y| + |t_x - t_y| := abs_sub _ _
    _ ≤ |m_x - m_y| + p.β * |p.J| * |m_x - m_y| := by linarith [htanh_bound]
    _ = (1 + p.β * |p.J|) * |m_x - m_y| := by ring

/-- Core Lipschitz bound: (1/(2τ)) × |component diff| ≤ L × ‖x - y‖. -/
private theorem isingDrift_lipschitz_chain (p : IsingParams) (x y : TwoState → ℝ) :
    (1 / (2 * p.τ)) * |(magnetizationOf x - magnetizationOf y) -
      (Real.tanh (p.β * (p.J * magnetizationOf x + p.h)) -
       Real.tanh (p.β * (p.J * magnetizationOf y + p.h)))| ≤
      (p.β * |p.J| + 1) / p.τ * ‖x - y‖ := by
  -- Chain: coeff × |diff| ≤ coeff × (1+β|J|) × |m-m'| ≤ coeff × (1+β|J|) × 2‖x-y‖
  have hcoeff : 0 < 1 / (2 * p.τ) := div_pos one_pos (mul_pos two_pos p.τ_pos)
  calc (1 / (2 * p.τ)) * |(magnetizationOf x - magnetizationOf y) -
        (Real.tanh (p.β * (p.J * magnetizationOf x + p.h)) -
         Real.tanh (p.β * (p.J * magnetizationOf y + p.h)))|
      ≤ (1 / (2 * p.τ)) * ((1 + p.β * |p.J|) * |magnetizationOf x - magnetizationOf y|) :=
        mul_le_mul_of_nonneg_left (isingDrift_component_bound p x y) (le_of_lt hcoeff)
    _ ≤ (1 / (2 * p.τ)) * ((1 + p.β * |p.J|) * (2 * ‖x - y‖)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hcoeff)
        exact mul_le_mul_of_nonneg_left (magnetization_diff_bound x y)
          (add_nonneg one_pos.le (mul_nonneg (le_of_lt p.β_pos) (abs_nonneg p.J)))
    _ = (p.β * |p.J| + 1) / p.τ * ‖x - y‖ := by field_simp; ring

/-- Match reduction for Ising drift difference (up component). -/
private theorem isingDrift_diff_up (τ a b : ℝ) :
    (fun q => match q with | .up => -(1/(2*τ)) * a | .down => 1/(2*τ) * a) TwoState.up -
    (fun q => match q with | .up => -(1/(2*τ)) * b | .down => 1/(2*τ) * b) TwoState.up =
    -(1/(2*τ)) * (a - b) := by ring

/-- Match reduction for Ising drift difference (down component). -/
private theorem isingDrift_diff_down (τ a b : ℝ) :
    (fun q => match q with | .up => -(1/(2*τ)) * a | .down => 1/(2*τ) * a) TwoState.down -
    (fun q => match q with | .up => -(1/(2*τ)) * b | .down => 1/(2*τ) * b) TwoState.down =
    (1/(2*τ)) * (a - b) := by ring

/-- The Ising drift is Lipschitz on the simplex with constant (β|J|+1)/τ. -/
theorem isingDrift_lipschitz (p : IsingParams) :
    ∃ L, DriftFunction.IsLipschitz (isingDrift p) L := by
  use (p.β * |p.J| + 1) / p.τ
  intro x y _ _
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg
    (div_nonneg (add_nonneg (mul_nonneg (le_of_lt p.β_pos) (abs_nonneg p.J)) one_pos.le)
      (le_of_lt p.τ_pos)) (norm_nonneg _))]
  intro q; simp only [isingDrift, Pi.sub_apply]
  -- Core bound via chain inequality
  have hcoeff : 0 < 1 / (2 * p.τ) := div_pos one_pos (mul_pos two_pos p.τ_pos)
  have hchain := isingDrift_lipschitz_chain p x y
  -- Each component is ±(1/(2τ))·(diff)
  -- Rearrangement: (m-t) - (m'-t') = (m-m') - (t-t')
  set m_x := magnetizationOf x; set m_y := magnetizationOf y
  set t_x := Real.tanh (p.β * (p.J * m_x + p.h))
  set t_y := Real.tanh (p.β * (p.J * m_y + p.h))
  have hdiff : |m_x - t_x - (m_y - t_y)| = |(m_x - m_y) - (t_x - t_y)| := by congr 1; ring
  fin_cases q
  · rw [Real.norm_eq_abs, isingDrift_diff_up, abs_mul, abs_neg, abs_of_pos hcoeff, hdiff]
    exact hchain
  · rw [Real.norm_eq_abs, isingDrift_diff_down, abs_mul, abs_of_pos hcoeff, hdiff]
    exact hchain

/-! ## Boundary Invariance -/

/-- Helper: -1 < tanh(x) for all x (from tanh(-x) < 1). -/
private theorem neg_one_lt_tanh (x : ℝ) : -1 < Real.tanh x := by
  have := tanh_lt_one (-x); rw [Real.tanh_neg] at this; linarith

/-- At boundary x_q = 0, the Ising drift pushes inward. -/
theorem isingDrift_boundary_nonneg (p : IsingParams) :
    ∀ x ∈ Simplex TwoState, ∀ q, x q = 0 → 0 ≤ isingDrift p x q := by
  intro x hx q hq
  simp only [isingDrift, magnetizationOf]
  have hτ : 0 < 1 / (2 * p.τ) := div_pos one_pos (by linarith [p.τ_pos])
  fin_cases q
  · -- up: x_up = 0, m = -1, need -(1/(2τ))(-1 - tanh) ≥ 0
    simp only at hq ⊢; rw [hq]
    -- Rewrite: -(a) * (b) = a * (-b) where a > 0 and -b > 0
    have htanh := neg_one_lt_tanh (p.β * (p.J * (2 * (0 : ℝ) - 1) + p.h))
    have : -(1 / (2 * p.τ)) * (2 * (0 : ℝ) - 1 - Real.tanh (p.β * (p.J * (2 * 0 - 1) + p.h))) =
      (1 / (2 * p.τ)) * (1 + Real.tanh (p.β * (p.J * (2 * 0 - 1) + p.h))) := by ring
    rw [this]
    exact mul_nonneg (le_of_lt hτ) (by linarith)
  · -- down: x_down = 0, x_up = 1, need (1/(2τ))(1 - tanh) ≥ 0
    simp only at hq ⊢
    -- Extract x_up = 1 from simplex + x_down = 0
    have hxup : x TwoState.up = 1 := by
      have hsum := hx.2
      conv at hsum =>
        lhs
        rw [show (Finset.univ : Finset TwoState) = {.up, .down} by ext q; fin_cases q <;> simp]
        rw [Finset.sum_pair TwoState.up_ne_down]
      linarith
    rw [hxup]
    exact mul_nonneg (le_of_lt hτ) (by linarith [tanh_lt_one (p.β * (p.J * (2 * 1 - 1) + p.h))])

/-! ## Ising as Rules -/

/-- Single flip rule encoding the Ising drift. -/
def isingRule (p : IsingParams) : PopRule TwoState where
  -- Update flips up to down; rate is the down-component of the drift.
  update := fun q => match q with
    | .up => -1
    | .down => 1
  rate := fun x => isingDrift p x TwoState.down

/-- The Ising rule conserves population. -/
theorem isingRule_conserves (p : IsingParams) : (isingRule p).Conserves := by
  -- Sum of updates is -1 + 1 = 0.
  simp [isingRule, PopRule.Conserves]
  conv_lhs =>
    rw [show (Finset.univ : Finset TwoState) = {.up, .down} by
      ext q; fin_cases q <;> simp]
    rw [Finset.sum_pair TwoState.up_ne_down]
  ring

/-- The Ising rule matches the drift contribution for each component. -/
private theorem isingRule_contrib (p : IsingParams) (x : TwoState → ℝ) (q : TwoState) :
    (isingRule p).update q * (isingRule p).rate x = isingDrift p x q := by
  -- Case split on the state.
  fin_cases q <;> simp [isingRule, isingDrift]

/-- The Ising rule is boundary-nonnegative. -/
theorem isingRule_boundary_nonneg (p : IsingParams) :
    PopRule.BoundaryNonneg (isingRule p) := by
  -- Reduce to `isingDrift_boundary_nonneg` via the contribution identity.
  intro x hx q hq
  have h := isingDrift_boundary_nonneg p x hx q hq
  simpa [isingRule_contrib] using h

/-- Drift from the Ising rule equals the Ising drift. -/
theorem driftFromRules_isingRule (p : IsingParams) :
    driftFromRules [isingRule p] = isingDrift p := by
  -- Expand the singleton list sum.
  funext x q
  simp [driftFromRules, isingRule_contrib]

/-! ## Ising Choreography from Rules -/

/-- The Ising choreography assembled from a rule list. -/
def IsingChoreographyFromRules (p : IsingParams) : MeanFieldChoreography TwoState :=
  -- Use `fromRules` and the derived invariants.
  MeanFieldChoreography.fromRules [isingRule p]
    (by simpa [driftFromRules_isingRule] using isingDrift_lipschitz p)
    (by
      -- Singleton list: reduce to `isingRule_conserves`.
      intro r hr
      have hr' : r = isingRule p := by simpa using hr
      simpa [hr'] using (isingRule_conserves p))
    (by
      -- Singleton list: reduce to `isingRule_boundary_nonneg`.
      intro r hr
      have hr' : r = isingRule p := by simpa using hr
      simpa [hr'] using (isingRule_boundary_nonneg p))

/-! ## Ising Choreography -/

/-- The Ising model as a mean-field choreography. -/
abbrev IsingChoreography (p : IsingParams) : MeanFieldChoreography TwoState :=
  -- Alias the rule-derived choreography.
  IsingChoreographyFromRules p

end

end Gibbs.MeanField.Examples
