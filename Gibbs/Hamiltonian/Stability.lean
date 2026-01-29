import Gibbs.Hamiltonian.DampedFlow
import Mathlib.Analysis.SpecialFunctions.Exp

/-
The Problem. Provide Lyapunov-style stability scaffolding for Hamiltonian
systems with damping, using energy as the canonical Lyapunov candidate.

The difficulty is bookkeeping: we need a stability data structure that
matches the Hamiltonian phase space, and a wrapper that packages the
energy decrease lemma into that structure.

Solution Structure.
1. Define `LyapunovData` for phase-space drifts.
2. Construct `energyLyapunov` from energy monotonicity assumptions.
-/

namespace Gibbs.Hamiltonian

open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ## Lyapunov Data -/

/-- Lyapunov data for a phase-space drift. -/
structure LyapunovData (F : PhasePoint n → PhasePoint n) (x : PhasePoint n) where
  /-- Lyapunov function -/
  V : PhasePoint n → ℝ
  /-- Continuity of V -/
  V_cont : Continuous V
  /-- V vanishes at equilibrium -/
  V_zero : V x = 0
  /-- V is positive away from equilibrium -/
  V_pos : ∀ y, y ≠ x → 0 < V y
  /-- V is nonnegative everywhere -/
  V_nonneg : ∀ y, 0 ≤ V y
  /-- V is non-increasing along trajectories -/
  V_decreasing : ∀ (sol : ℝ → PhasePoint n),
    (∀ t, HasDerivAt sol (F (sol t)) t) →
    ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → V (sol t₂) ≤ V (sol t₁)

/-- Strict Lyapunov data: V decays to zero along trajectories. -/
structure StrictLyapunovData (F : PhasePoint n → PhasePoint n) (x : PhasePoint n)
    extends LyapunovData F x where
  /-- V tends to zero along any trajectory. -/
  V_to_zero : ∀ (sol : ℝ → PhasePoint n),
    (∀ t, HasDerivAt sol (F (sol t)) t) →
    Filter.Tendsto (V ∘ sol) Filter.atTop (nhds 0)

/-! ## Asymptotic Stability (Lyapunov Form) -/

/-- Asymptotic stability expressed via existence of strict Lyapunov data. -/
def IsAsymptoticallyStable (F : PhasePoint n → PhasePoint n) (x : PhasePoint n) : Prop :=
  Nonempty (StrictLyapunovData F x)

/-! ## Exponential Convergence (Energy-Based Wrapper) -/

/-- Exponential decay of energy along a trajectory. -/
def ExponentialEnergyDecay (H : ConvexHamiltonian n) (sol : ℝ → PhasePoint n) (rate : ℝ) : Prop :=
  ∀ t ≥ 0, H.energy (sol t) ≤ H.energy (sol 0) * Real.exp (-rate * t)

/-- Exponential convergence in squared norm. -/
def ExponentialConvergenceSq (sol : ℝ → PhasePoint n) (x : PhasePoint n) (C rate : ℝ) : Prop :=
  ∀ t ≥ 0, ‖sol t - x‖ ^ 2 ≤ C * Real.exp (-rate * t)

/-!
If energy decays exponentially and energy controls the distance to equilibrium,
then the trajectory converges exponentially (in squared norm).
-/
theorem exponential_convergence (H : ConvexHamiltonian n) (x_eq : PhasePoint n)
    (sol : ℝ → PhasePoint n) (c rate : ℝ)
    (hc : 0 ≤ c)
    (hbound : ∀ x, ‖x - x_eq‖ ^ 2 ≤ c * H.energy x)
    (hdecay : ExponentialEnergyDecay H sol rate) :
    ExponentialConvergenceSq sol x_eq (c * H.energy (sol 0)) rate := by
  intro t ht
  have hdist : ‖sol t - x_eq‖ ^ 2 ≤ c * H.energy (sol t) := hbound (sol t)
  have hdec : H.energy (sol t) ≤ H.energy (sol 0) * Real.exp (-rate * t) := hdecay t ht
  have hmul :
      c * H.energy (sol t) ≤ c * H.energy (sol 0) * Real.exp (-rate * t) := by
    simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hdec hc)
  exact le_trans hdist hmul

/-! ## Energy Lyapunov Construction -/

/-- Energy as a Lyapunov function for damped Hamiltonian dynamics,
    assuming a derivative certificate for the energy along trajectories. -/
noncomputable def energyLyapunov (H : ConvexHamiltonian n) (d : Damping) (x_eq : PhasePoint n)
    (hcont : Continuous fun x => H.energy x)
    (hzero : H.energy x_eq = 0)
    (hpos : ∀ y, y ≠ x_eq → 0 < H.energy y)
    (hnonneg : ∀ y, 0 ≤ H.energy y)
    (henergy : ∀ (sol : ℝ → PhasePoint n),
      (∀ t, HasDerivAt sol (dampedDrift H d (sol t)) t) →
      ∀ t,
        HasDerivAt (fun s => H.energy (sol s))
          (-d.γ * PhasePoint.kineticNormSq (sol t)) t) :
    LyapunovData (dampedDrift H d) x_eq := by
  -- Package the energy data with monotonicity from `energy_decreasing`.
  refine
    { V := H.energy
      V_cont := hcont
      V_zero := hzero
      V_pos := hpos
      V_nonneg := hnonneg
      V_decreasing := ?_ }
  intro sol hsol t₁ t₂ ht₁ ht₁₂
  have hderiv := henergy sol hsol
  exact energy_decreasing (H := H) (d := d) (sol := sol) hderiv t₁ t₂ ht₁ ht₁₂

/-- Damped dynamics are asymptotically stable when equipped with strict Lyapunov data. -/
theorem damped_asymptotically_stable (H : ConvexHamiltonian n) (d : Damping) (x_eq : PhasePoint n)
    (L : StrictLyapunovData (dampedDrift H d) x_eq) :
    IsAsymptoticallyStable (dampedDrift H d) x_eq := by
  -- Existence of strict Lyapunov data is the stability certificate.
  exact ⟨L⟩

end

end Gibbs.Hamiltonian
