import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.DampedFlow

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

/-- Discriminant for classifying damping regimes. -/
def discriminant (p : OscillatorParams) : ℝ :=
  p.γ ^ 2 - 4 * p.ω ^ 2

/-- Second-order ODE: q'' + γ q' + ω² q = 0 (using `deriv`). -/
def OscillatorEq (p : OscillatorParams) (q : ℝ → ℝ) : Prop :=
  ∀ t, deriv (deriv q) t + p.γ * deriv q t + p.ω ^ 2 * q t = 0

/-- Underdamped explicit solution template. -/
noncomputable def underdampedSolution (p : OscillatorParams) (A B : ℝ)
    (c s : ℝ → ℝ) : ℝ → ℝ :=
  fun t => Real.exp (-p.γ / 2 * t) * (A * c t + B * s t)

/-- Critically damped explicit solution template. -/
noncomputable def criticallyDampedSolution (p : OscillatorParams) (A B : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (-p.γ / 2 * t) * (A + B * t)

/-- Overdamped explicit solution template. -/
noncomputable def overdampedSolution (p : OscillatorParams) (A B : ℝ) : ℝ → ℝ :=
  fun t =>
    Real.exp ((-p.γ + Real.sqrt (p.γ ^ 2 - 4 * p.ω ^ 2)) / 2 * t) * A +
      Real.exp ((-p.γ - Real.sqrt (p.γ ^ 2 - 4 * p.ω ^ 2)) / 2 * t) * B

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
