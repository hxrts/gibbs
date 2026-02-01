import Gibbs.MeanField.Examples.Ising.Drift

/-!
# Glauber Dynamics

Glauber dynamics are local spin-flip rates that implement the global Ising
drift at the microscopic level. The rate alpha (down to up) and gamma (up to
down) satisfy alpha - gamma = (1/tau) tanh(beta(J m + h)) and alpha + gamma =
1/tau. The projection theorem shows that aggregating these local rates over
the population recovers the macroscopic Ising drift exactly.
-/

namespace Gibbs.MeanField.Examples

open Gibbs.MeanField

open scoped Classical

noncomputable section

/-! ## Glauber Rates -/

/-- Glauber rate for down → up transition.
    α(m) = (1/τ) / (1 + exp(-2β(Jm + h)))
    In `glauber_produces_isingDrift`, inflow to up = x_down · α. -/
def glauberAlpha (p : IsingParams) (x : TwoState → ℝ) : ℝ :=
  let m := magnetizationOf x
  (1 / p.τ) / (1 + Real.exp (-2 * p.β * (p.J * m + p.h)))

/-- Glauber rate for up → down transition.
    γ(m) = (1/τ) / (1 + exp(+2β(Jm + h)))
    In `glauber_produces_isingDrift`, outflow from up = x_up · γ. -/
def glauberGamma (p : IsingParams) (x : TwoState → ℝ) : ℝ :=
  let m := magnetizationOf x
  (1 / p.τ) / (1 + Real.exp (2 * p.β * (p.J * m + p.h)))

/-- Glauber α rate is non-negative. -/
theorem glauberAlpha_nonneg (p : IsingParams) :
    ∀ x ∈ Simplex TwoState, 0 ≤ glauberAlpha p x := by
  intro x _; simp only [glauberAlpha]
  exact div_nonneg (div_nonneg (by linarith [p.τ_pos]) p.τ_pos.le) (by positivity)

/-- Glauber γ rate is non-negative. -/
theorem glauberGamma_nonneg (p : IsingParams) :
    ∀ x ∈ Simplex TwoState, 0 ≤ glauberGamma p x := by
  intro x _; simp only [glauberGamma]
  exact div_nonneg (div_nonneg (by linarith [p.τ_pos]) p.τ_pos.le) (by positivity)

/-! ## Rate Identities -/

/-- Helper: rewrite exponentials in terms of exp(z) for Glauber identities. -/
private theorem glauber_exp_setup (p : IsingParams) (x : TwoState → ℝ) :
    let z := p.β * (p.J * magnetizationOf x + p.h)
    p.τ ≠ 0 ∧
    1 + Real.exp (-(2 * z)) ≠ 0 ∧
    1 + Real.exp (2 * z) ≠ 0 ∧
    Real.exp z + (Real.exp z)⁻¹ ≠ 0 := by
  refine ⟨ne_of_gt p.τ_pos, ?_, ?_, ?_⟩ <;> positivity

/-- The Glauber rates satisfy α - γ = (1/τ) tanh(β(Jm + h)). -/
theorem glauber_diff (p : IsingParams) (x : TwoState → ℝ) :
    glauberAlpha p x - glauberGamma p x =
    (1 / p.τ) * Real.tanh (p.β * (p.J * magnetizationOf x + p.h)) := by
  simp only [glauberAlpha, glauberGamma]
  -- Normalize exponent signs
  have heq : -2 * p.β * (p.J * magnetizationOf x + p.h) =
             -(2 * p.β * (p.J * magnetizationOf x + p.h)) := by ring
  have heq2 : 2 * p.β * (p.J * magnetizationOf x + p.h) =
              2 * (p.β * (p.J * magnetizationOf x + p.h)) := by ring
  rw [heq, heq2]
  -- Generalize z = β(Jm+h) and clear denominators
  generalize p.β * (p.J * magnetizationOf x + p.h) = z
  rw [Real.exp_neg, show (2 : ℝ) * z = (2 : ℕ) * z by norm_num, Real.exp_nat_mul]
  rw [Real.tanh_eq, Real.exp_neg]
  -- All terms now in exp(z); clear denominators and simplify
  field_simp; ring

/-- The Glauber rates satisfy α + γ = 1/τ. -/
theorem glauber_sum (p : IsingParams) (x : TwoState → ℝ) :
    glauberAlpha p x + glauberGamma p x = 1 / p.τ := by
  simp only [glauberAlpha, glauberGamma]
  -- Normalize and generalize exponent
  have heq : -2 * p.β * (p.J * magnetizationOf x + p.h) =
             -(2 * p.β * (p.J * magnetizationOf x + p.h)) := by ring
  rw [heq]
  generalize 2 * p.β * (p.J * magnetizationOf x + p.h) = y
  -- Positivity and non-vanishing
  have hτ_ne := ne_of_gt p.τ_pos
  have hne : 1 + Real.exp (-y) ≠ 0 := by positivity
  have hne' : 1 + Real.exp y ≠ 0 := by positivity
  -- Combine fractions: 1/(τ(1+e⁻ʸ)) + 1/(τ(1+eʸ)) = 1/τ
  rw [div_div, div_div]
  rw [div_add_div _ _ (mul_ne_zero hτ_ne hne) (mul_ne_zero hτ_ne hne')]
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hτ_ne hne) (mul_ne_zero hτ_ne hne')) hτ_ne]
  -- Use exp(y)·exp(-y) = 1 and simplify
  have hprod : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc _ = p.τ * (p.τ * (1 + Real.exp y)) + p.τ * (1 + Real.exp (-y)) * (p.τ * 1) := by ring
       _ = p.τ * p.τ * (2 + Real.exp y + Real.exp (-y)) := by ring
       _ = p.τ * p.τ * (1 + Real.exp y + Real.exp y * Real.exp (-y) + Real.exp (-y)) := by
           rw [hprod]; ring
       _ = 1 * (p.τ * (1 + Real.exp (-y)) * (p.τ * (1 + Real.exp y))) := by ring
       _ = _ := by ring

/-! ## Projection Correctness -/

/-- Helper: express α and γ in terms of tanh. -/
private theorem glauber_rates_tanh (p : IsingParams) (x : TwoState → ℝ) :
    let t := Real.tanh (p.β * (p.J * magnetizationOf x + p.h))
    glauberAlpha p x = (1/(2*p.τ)) * (1 + t) ∧
    glauberGamma p x = (1/(2*p.τ)) * (1 - t) := by
  -- Derive from sum and difference identities
  set α := glauberAlpha p x; set γ := glauberGamma p x
  set t := Real.tanh (p.β * (p.J * magnetizationOf x + p.h))
  have hdiff := glauber_diff p x; rw [← show α = glauberAlpha p x from rfl] at hdiff
  rw [← show γ = glauberGamma p x from rfl] at hdiff
  have hsum := glauber_sum p x; rw [← show α = glauberAlpha p x from rfl] at hsum
  rw [← show γ = glauberGamma p x from rfl] at hsum
  have hτ_ne : p.τ ≠ 0 := ne_of_gt p.τ_pos
  constructor
  · -- α = (1/(2τ))(1 + t)
    have : 2 * α = α + γ + (α - γ) := by ring
    rw [hsum, hdiff] at this; field_simp at this ⊢; linarith
  · -- γ = (1/(2τ))(1 - t)
    have : 2 * γ = α + γ - (α - γ) := by ring
    rw [hsum, hdiff] at this; field_simp at this ⊢; linarith

/-- The Glauber rates produce the Ising drift.
    Main theorem connecting local rates to global dynamics:
    inflow (α · x_down) minus outflow (γ · x_up) = drift. -/
theorem glauber_produces_isingDrift (p : IsingParams) :
    ∀ x ∈ Simplex TwoState,
      x TwoState.down * glauberAlpha p x - x TwoState.up * glauberGamma p x =
        isingDrift p x TwoState.up := by
  intro x hx
  -- Extract sum x_up + x_down = 1
  have hsum : x TwoState.up + x TwoState.down = 1 := by
    have hsum' := hx.2
    conv at hsum' => lhs; rw [show (Finset.univ : Finset TwoState) = {.up, .down} by
      ext q; fin_cases q <;> simp]; rw [Finset.sum_pair TwoState.up_ne_down]
    exact hsum'
  -- Substitute rate expressions and simplify algebraically
  obtain ⟨hα_eq, hγ_eq⟩ := glauber_rates_tanh p x
  rw [hα_eq, hγ_eq]
  -- Goal reduces to algebra: (1-x_up)(1+t)/(2τ) - x_up(1-t)/(2τ) = -(1/(2τ))(m-t)
  have hτ_ne : p.τ ≠ 0 := ne_of_gt p.τ_pos
  show x TwoState.down * ((1 / (2 * p.τ)) * (1 + _)) -
    x TwoState.up * ((1 / (2 * p.τ)) * (1 - _)) = _
  rw [show x TwoState.down = 1 - x TwoState.up from by linarith]
  simp only [isingDrift, magnetizationOf]
  field_simp; ring

/-! ## Ising Projection -/

/-- The complete Ising projection: Glauber rates from Ising choreography.

    SPECIFY: Ising choreography with drift dm/dt = -(1/τ)(m - tanh(β(Jm+h)))
    PROJECT: Glauber rates α(m), γ(m) that produce this drift
    GUARANTEE: Local adherence to Glauber rates ⟹ global Ising dynamics -/
def IsingProjection (p : IsingParams) : ProjectionProblem TwoState :=
  TwoStateProjection (isingDrift p)

end

end Gibbs.MeanField.Examples
