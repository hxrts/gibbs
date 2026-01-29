import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.DampedFlow
import Mathlib

set_option maxHeartbeats 0

/-
The Problem. Provide a concrete Hamiltonian example that can be used in tests
and examples: the damped harmonic oscillator.

The difficulty is minimal here; we just package the existing quadratic
Hamiltonian with the damped drift definition.

Solution Structure.
1. Define the damped harmonic oscillator drift as `dampedDrift` of the
   quadratic Hamiltonian.
-/

namespace Gibbs.Hamiltonian.Examples

noncomputable section

/-! ## Explicit Solution Templates -/

/-- Parameters for the scalar damped harmonic oscillator. -/
structure OscillatorParams where
  /-- Natural frequency. -/
  ω : ℝ
  /-- Damping coefficient. -/
  γ : ℝ
  /-- Natural frequency is positive. -/
  ω_pos : 0 < ω
  /-- Damping coefficient is positive. -/
  γ_pos : 0 < γ

/-- The discriminant determines the damping regime. -/
def OscillatorParams.discriminant (p : OscillatorParams) : ℝ :=
  p.γ ^ 2 - 4 * p.ω ^ 2

/-- Underdamped: discriminant < 0. -/
def OscillatorParams.isUnderdamped (p : OscillatorParams) : Prop :=
  p.discriminant < 0

/-- Critically damped: discriminant = 0. -/
def OscillatorParams.isCriticallyDamped (p : OscillatorParams) : Prop :=
  p.discriminant = 0

/-- Overdamped: discriminant > 0. -/
def OscillatorParams.isOverdamped (p : OscillatorParams) : Prop :=
  p.discriminant > 0

/-- Damped frequency for the underdamped case. -/
noncomputable def OscillatorParams.dampedFreq (p : OscillatorParams)
    (_h : p.isUnderdamped) : ℝ :=
  Real.sqrt (p.ω ^ 2 - p.γ ^ 2 / 4)

/-- Underdamped solution: e^{-γt/2}(A cos(ω_d t) + B sin(ω_d t)). -/
noncomputable def underdampedSolution (p : OscillatorParams) (h : p.isUnderdamped)
    (A B : ℝ) : ℝ → ℝ :=
  fun t =>
    Real.exp (-p.γ * t / 2) *
      (A * Real.cos (p.dampedFreq h * t) + B * Real.sin (p.dampedFreq h * t))

/-- Critically damped solution: (A + Bt) e^{-γt/2}. -/
noncomputable def criticallyDampedSolution (p : OscillatorParams) (_h : p.isCriticallyDamped)
    (A B : ℝ) : ℝ → ℝ :=
  fun t => (A + B * t) * Real.exp (-p.γ * t / 2)

/-- Overdamped solution: A e^{λ₊t} + B e^{λ₋t}. -/
noncomputable def overdampedSolution (p : OscillatorParams) (_h : p.isOverdamped)
    (A B : ℝ) : ℝ → ℝ :=
  let sqrtDisc := Real.sqrt p.discriminant
  let lambda_plus := (-p.γ + sqrtDisc) / 2
  let lambda_minus := (-p.γ - sqrtDisc) / 2
  fun t => A * Real.exp (lambda_plus * t) + B * Real.exp (lambda_minus * t)

/-- Second-order ODE: q'' + γ q' + ω² q = 0 (using `deriv`). -/
def OscillatorEq (p : OscillatorParams) (q : ℝ → ℝ) : Prop :=
  ∀ t, deriv (deriv q) t + p.γ * deriv q t + p.ω ^ 2 * q t = 0

/-- A function solves the damped oscillator ODE with derivative certificates. -/
def SolvesOscillatorODE (p : OscillatorParams) (q : ℝ → ℝ) : Prop :=
  ∀ t,
    HasDerivAt q (deriv q t) t ∧
      HasDerivAt (deriv q) (deriv (deriv q) t) t ∧
        deriv (deriv q) t + p.γ * deriv q t + p.ω ^ 2 * q t = 0

/-! ## Explicit Solutions Solve the ODE -/

/-- The underdamped solution satisfies the ODE. -/
theorem underdamped_solves_ode (p : OscillatorParams) (h : p.isUnderdamped) (A B : ℝ) :
    SolvesOscillatorODE p (underdampedSolution p h A B) := by
  unfold SolvesOscillatorODE underdampedSolution
  unfold OscillatorParams.dampedFreq
  unfold OscillatorParams.isUnderdamped at h
  unfold OscillatorParams.discriminant at h
  unfold deriv
  norm_num [fderiv_deriv, mul_comm]
  intro t
  refine' ⟨_, _, _⟩
  ·
    convert
        HasDerivAt.mul
          (HasDerivAt.exp
            (HasDerivAt.div_const (HasDerivAt.neg (hasDerivAt_mul_const _)) _))
          (HasDerivAt.add
            (HasDerivAt.const_mul _ (HasDerivAt.cos (hasDerivAt_mul_const _)))
            (HasDerivAt.const_mul _ (HasDerivAt.sin (hasDerivAt_mul_const _))))
        using 1 <;> ring
    norm_num
    ring
  ·
    convert
        HasDerivAt.add
          (HasDerivAt.mul
            (HasDerivAt.mul (hasDerivAt_const _ _)
              (HasDerivAt.exp
                (HasDerivAt.div_const (HasDerivAt.neg (hasDerivAt_mul_const _)) _)))
            (HasDerivAt.add
              (HasDerivAt.mul (hasDerivAt_const _ _)
                (HasDerivAt.cos (hasDerivAt_mul_const _)))
              (HasDerivAt.mul (hasDerivAt_const _ _)
                (HasDerivAt.sin (hasDerivAt_mul_const _)))))
          (HasDerivAt.mul
            (HasDerivAt.exp
              (HasDerivAt.div_const (HasDerivAt.neg (hasDerivAt_mul_const _)) _))
            (HasDerivAt.add
              (HasDerivAt.neg
                (HasDerivAt.mul (hasDerivAt_const _ _)
                  (HasDerivAt.mul (hasDerivAt_const _ _)
                    (HasDerivAt.sin (hasDerivAt_mul_const _)))))
              (HasDerivAt.mul (hasDerivAt_const _ _)
                (HasDerivAt.mul (hasDerivAt_const _ _)
                  (HasDerivAt.cos (hasDerivAt_mul_const _))))))
        using 1 <;> ring
    norm_num
    ring
  ·
    ring
    rw [Real.sq_sqrt] <;> nlinarith

/-- The critically damped solution satisfies the ODE. -/
theorem criticallyDamped_solves_ode (p : OscillatorParams) (h : p.isCriticallyDamped) (A B : ℝ) :
    SolvesOscillatorODE p (criticallyDampedSolution p h A B) := by
  have h_discriminant : p.γ ^ 2 - 4 * p.ω ^ 2 = 0 := by
    exact h
  unfold SolvesOscillatorODE
  unfold criticallyDampedSolution
  norm_num [fderiv_deriv, mul_comm B, mul_comm p.γ]
  unfold deriv
  norm_num [fderiv_deriv]
  ring
  exact fun t =>
    ⟨by
        convert
            HasDerivAt.add
              (HasDerivAt.const_mul A
                (HasDerivAt.exp
                  (HasDerivAt.mul (hasDerivAt_mul_const _) (hasDerivAt_const _ _))))
              (HasDerivAt.mul
                (HasDerivAt.mul (hasDerivAt_id' t) (hasDerivAt_const _ _))
                (HasDerivAt.exp
                  (HasDerivAt.mul (hasDerivAt_mul_const _) (hasDerivAt_const _ _))))
          using 1 <;> norm_num <;> ring,
      by
        rw [show p.ω ^ 2 = p.γ ^ 2 / 4 by linarith]
        ring⟩

/-- The overdamped solution satisfies the ODE. -/
theorem overdamped_solves_ode (p : OscillatorParams) (h : p.isOverdamped) (A B : ℝ) :
    SolvesOscillatorODE p (overdampedSolution p h A B) := by
  intro tSolution
  unfold overdampedSolution
  unfold OscillatorParams.discriminant at *
  unfold OscillatorParams.isOverdamped at h
  unfold OscillatorParams.discriminant at h
  unfold deriv at *
  norm_num [mul_comm] at *
  refine' ⟨_, _, _⟩
  ·
    convert
        HasDerivAt.add
          (HasDerivAt.const_mul A (HasDerivAt.exp (hasDerivAt_mul_const _)))
          (HasDerivAt.const_mul B (HasDerivAt.exp (hasDerivAt_mul_const _)))
        using 1 <;> ring
  ·
    convert
        HasDerivAt.add
          (HasDerivAt.const_mul A
            (HasDerivAt.const_mul
              ((-p.γ + Real.sqrt (p.γ ^ 2 - p.ω ^ 2 * 4)) / 2)
              (HasDerivAt.exp (hasDerivAt_mul_const _))))
          (HasDerivAt.const_mul B
            (HasDerivAt.const_mul
              ((-p.γ - Real.sqrt (p.γ ^ 2 - p.ω ^ 2 * 4)) / 2)
              (HasDerivAt.exp (hasDerivAt_mul_const _))))
        using 1 <;> ring
  ·
    grind

/-! ## Decay of Explicit Solutions -/

theorem underdampedSolution_decays (p : OscillatorParams) (h : p.isUnderdamped) (A B : ℝ) :
    Filter.Tendsto (underdampedSolution p h A B) Filter.atTop (nhds 0) := by
  unfold underdampedSolution at *
  have h_bound :
      ∀ t,
        abs (A * Real.cos (p.dampedFreq h * t) + B * Real.sin (p.dampedFreq h * t)) ≤
          abs A + abs B := by
    intro t
    exact
      abs_le.mpr
        ⟨by
          cases abs_cases A <;> cases abs_cases B <;>
            nlinarith [abs_le.mp (Real.abs_cos_le_one (p.dampedFreq h * t)),
              abs_le.mp (Real.abs_sin_le_one (p.dampedFreq h * t))],
          by
          cases abs_cases A <;> cases abs_cases B <;>
            nlinarith [abs_le.mp (Real.abs_cos_le_one (p.dampedFreq h * t)),
              abs_le.mp (Real.abs_sin_le_one (p.dampedFreq h * t))]⟩
  refine
    squeeze_zero_norm
      (fun t => by
        simpa [abs_mul] using
          mul_le_mul_of_nonneg_left (h_bound t) (by positivity))
      (by
        simpa using
          Filter.Tendsto.mul
            (Real.tendsto_exp_atBot.comp <|
              Filter.tendsto_atTop_atBot.mpr
                (fun x =>
                  ⟨-x * 2 / p.γ,
                    fun t ht => by
                      nlinarith [p.γ_pos, mul_div_cancel₀ (-x * 2) p.γ_pos.ne']⟩))
            tendsto_const_nhds)

theorem criticallyDampedSolution_decays (p : OscillatorParams) (h : p.isCriticallyDamped)
    (A B : ℝ) :
    Filter.Tendsto (criticallyDampedSolution p h A B) Filter.atTop (nhds 0) := by
  have h_bound :
      ∃ C : ℝ, ∀ t ≥ 0,
        abs ((A + B * t) * Real.exp (-p.γ * t / 2)) ≤
          C * t * Real.exp (-p.γ * t / 2) + abs A * Real.exp (-p.γ * t / 2) := by
    refine ⟨abs B + 1, ?_⟩
    intro t ht
    rw [abs_le]
    constructor <;> cases abs_cases A <;> cases abs_cases B <;>
      nlinarith [abs_le.mp (show |A| ≤ |A| by norm_num),
        abs_le.mp (show |B| ≤ |B| by norm_num),
        Real.exp_pos (-p.γ * t / 2),
        mul_nonneg ht (Real.exp_nonneg (-p.γ * t / 2))]
  have h_t_exp :
      Filter.Tendsto (fun t => t * Real.exp (-p.γ * t / 2)) Filter.atTop (nhds 0) := by
    suffices h_y :
        Filter.Tendsto (fun y => (2 * y / p.γ) * Real.exp (-y)) Filter.atTop (nhds 0) by
      convert
          h_y.comp
            (Filter.tendsto_id.const_mul_atTop
              (show 0 < p.γ / 2 by linarith [p.γ_pos]))
        using 2 <;> norm_num <;> ring
      norm_num [mul_assoc, mul_comm p.γ, p.γ_pos.ne']
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    convert this.const_mul (2 / p.γ) using 2 <;> ring
  set a : ℝ → ℝ :=
    fun t =>
      h_bound.choose * t * Real.exp (-p.γ * t / 2) +
        |A| * Real.exp (-p.γ * t / 2)
  refine
    (squeeze_zero_norm' (f := criticallyDampedSolution p h A B) (a := a) ?_ ?_)
  ·
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨0, fun t ht => ?_⟩
    have hbound := h_bound.choose_spec t ht
    simpa [criticallyDampedSolution, a, Real.norm_eq_abs, abs_mul, mul_comm, mul_left_comm,
      mul_assoc] using hbound
  ·
    simpa [a, mul_assoc] using
      Filter.Tendsto.add
        (h_t_exp.const_mul _)
        (tendsto_const_nhds.mul
          (Real.tendsto_exp_atBot.comp <|
            Filter.tendsto_atTop_atBot.mpr
              (fun x =>
                ⟨-x * 2 / p.γ,
                  fun t ht => by
                    nlinarith [p.γ_pos, mul_div_cancel₀ (-x * 2) p.γ_pos.ne']⟩)))

theorem overdampedSolution_decays (p : OscillatorParams) (h : p.isOverdamped) (A B : ℝ) :
    Filter.Tendsto (overdampedSolution p h A B) Filter.atTop (nhds 0) := by
  have h_exp_decay :
      Filter.Tendsto
          (fun t => Real.exp ((-p.γ + Real.sqrt p.discriminant) / 2 * t)) Filter.atTop
          (nhds 0) ∧
        Filter.Tendsto
          (fun t => Real.exp ((-p.γ - Real.sqrt p.discriminant) / 2 * t)) Filter.atTop
          (nhds 0) := by
    norm_num [Real.tendsto_exp_atBot]
    constructor <;> refine' Filter.Tendsto.const_mul_atTop_of_neg _ Filter.tendsto_id
    ·
      unfold OscillatorParams.isOverdamped at h
      unfold OscillatorParams.discriminant at *
      nlinarith [p.ω_pos, p.γ_pos, Real.sqrt_nonneg (p.γ ^ 2 - 4 * p.ω ^ 2),
        Real.mul_self_sqrt (show 0 ≤ p.γ ^ 2 - 4 * p.ω ^ 2 by linarith)]
    ·
      linarith [p.ω_pos, p.γ_pos, Real.sqrt_nonneg p.discriminant]
  simpa using Filter.Tendsto.add (h_exp_decay.1.const_mul A) (h_exp_decay.2.const_mul B)


/-! ## Damped Harmonic Oscillator -/

/-- Damped harmonic oscillator drift on phase space. -/
noncomputable def dampedHarmonicOscillator (n : ℕ) (d : Damping) :
    PhasePoint n → PhasePoint n := by
  -- Use the canonical harmonic oscillator Hamiltonian with damping.
  exact dampedDrift (harmonicOscillator n) d

/-! ## Energy Decay -/

/-- Energy dissipation rate for the damped harmonic oscillator. -/
theorem harmonic_energy_dissipation (n : ℕ) (d : Damping) (x : PhasePoint n) :
    energyDerivative (harmonicOscillator n) (dampedDrift (harmonicOscillator n) d) x =
      -d.γ * PhasePoint.kineticNormSq x := by
  -- Reduce to the generic dissipation lemma with ∇T = id.
  simpa [harmonicOscillator] using
    (energy_dissipation (H := harmonicOscillator n) (d := d)
      (hgrad := _root_.Gibbs.Hamiltonian.quadraticKinetic_grad n) x)

/-! ## Lyapunov Stability (Energy Decrease) -/

/-- Energy is non-increasing along any trajectory with the dissipation derivative. -/
theorem harmonic_energy_decreasing (n : ℕ) (d : Damping) (sol : ℝ → PhasePoint n)
    (hderiv : ∀ t,
      HasDerivAt (fun s => (harmonicOscillator n).energy (sol s))
        (-d.γ * PhasePoint.kineticNormSq (sol t)) t) :
    ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ →
      (harmonicOscillator n).energy (sol t₂) ≤ (harmonicOscillator n).energy (sol t₁) := by
  -- Apply the general energy monotonicity lemma.
  simpa using (energy_decreasing (H := harmonicOscillator n) (d := d) (sol := sol) hderiv)

end

end Gibbs.Hamiltonian.Examples
