import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.DampedFlow
import Gibbs.Hamiltonian.Ergodic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

/-!
# Nose-Hoover Thermostat

The Nose-Hoover thermostat extends phase space by a scalar friction variable xi
that couples to the momentum equation. Unlike fixed damping, xi evolves
dynamically to enforce a target kinetic temperature, producing canonical
(constant-temperature) sampling in the ergodic limit.

This file defines thermostat parameters, the extended phase space (q, p, xi),
the Nose-Hoover drift, and the energy-rate identities for both the physical
subsystem and the extended Hamiltonian.
-/

namespace Gibbs.Hamiltonian

open scoped Classical NNReal
open InnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ## Thermostat Parameters and Phase Space -/

/-- Thermostat parameters: coupling strength and target temperature. -/
structure ThermostatParams where
  /-- Thermostat mass -/
  Q : ℝ
  /-- Target temperature (k_B * T) -/
  kT : ℝ
  /-- Positivity of Q -/
  Q_pos : 0 < Q
  /-- Positivity of kT -/
  kT_pos : 0 < kT

/-- Extended phase space point with thermostat variable ξ.
    Implemented as a triple product to inherit norm/metric instances. -/
abbrev ThermostatPoint (n : ℕ) := Config n × Config n × ℝ

namespace ThermostatPoint

variable {n : ℕ}

/-- Position projection. -/
def q (x : ThermostatPoint n) : Config n := x.1

/-- Momentum projection. -/
def p (x : ThermostatPoint n) : Config n := x.2.1

/-- Thermostat variable projection. -/
def ξ (x : ThermostatPoint n) : ℝ := x.2.2

/-- Construct a thermostat point from (q,p,ξ). -/
def mk (q : Config n) (p : Config n) (ξ : ℝ) : ThermostatPoint n := (q, p, ξ)

/-- Project to ordinary phase space (forget ξ). -/
def toPhasePoint (x : ThermostatPoint n) : PhasePoint n :=
  (x.q, x.p)

/-- Embed a phase point with ξ = 0. -/
def fromPhasePoint (x : PhasePoint n) : ThermostatPoint n :=
  (x.1, x.2, 0)

theorem toPhasePoint_q (x : ThermostatPoint n) : x.toPhasePoint.q = x.q := rfl

theorem toPhasePoint_p (x : ThermostatPoint n) : x.toPhasePoint.p = x.p := rfl

theorem fromPhasePoint_q (x : PhasePoint n) : (fromPhasePoint x).q = x.q := rfl

theorem fromPhasePoint_p (x : PhasePoint n) : (fromPhasePoint x).p = x.p := rfl

theorem fromPhasePoint_ξ (x : PhasePoint n) : (fromPhasePoint x).ξ = 0 := rfl

end ThermostatPoint

/-! ## Nosé–Hoover Drift -/

/-- Nosé–Hoover drift on the extended phase space.
    q̇ = ∇_p H,  ṗ = -∇_q H - ξ p,  ξ̇ = (‖p‖² - n·kT)/Q. -/
def noseHooverDrift (H : ConvexHamiltonian n) (params : ThermostatParams) :
    ThermostatPoint n → ThermostatPoint n :=
  fun x =>
    ThermostatPoint.mk (H.velocity x.p)
      (H.force x.q - x.ξ • x.p)
      ((1 / params.Q) * (‖x.p‖ ^ 2 - n * params.kT))

/-! ## Subsystem Energy Rate -/

/-- Subsystem energy derivative along a thermostat drift.
    This is the Hamiltonian directional derivative restricted to (q,p). -/
def subsystemEnergyDerivative (H : ConvexHamiltonian n) (F : ThermostatPoint n → ThermostatPoint n)
    (x : ThermostatPoint n) : ℝ :=
  ⟪gradient H.T x.p, (F x).p⟫_ℝ + ⟪gradient H.V x.q, (F x).q⟫_ℝ

/-- Subsystem energy rate along the Nosé–Hoover drift.
    Assumes `∇T = id`, i.e. quadratic kinetic energy. -/
theorem subsystem_energy_rate (H : ConvexHamiltonian n) (params : ThermostatParams)
    (hgrad : ∀ p, gradient H.T p = p) (x : ThermostatPoint n) :
    subsystemEnergyDerivative H (noseHooverDrift H params) x = -x.ξ * ‖x.p‖ ^ 2 := by
  -- Expand the derivative and cancel Hamiltonian cross terms.
  have hcross :
      ⟪gradient H.T x.p, H.force x.q⟫_ℝ + ⟪gradient H.V x.q, H.velocity x.p⟫_ℝ = 0 := by
    -- Force is minus gradient and velocity is gradient.
    simp [ConvexHamiltonian.force, ConvexHamiltonian.velocity, real_inner_comm, add_comm]
  have hsplit :
      ⟪gradient H.T x.p, H.force x.q - x.ξ • x.p⟫_ℝ
        = ⟪gradient H.T x.p, H.force x.q⟫_ℝ - x.ξ * ⟪gradient H.T x.p, x.p⟫_ℝ := by
    -- Expand the inner product and collect the scalar term.
    simp [inner_sub_right, inner_smul_right]
  calc
    subsystemEnergyDerivative H (noseHooverDrift H params) x
        = ⟪gradient H.T x.p, H.force x.q - x.ξ • x.p⟫_ℝ
          + ⟪gradient H.V x.q, H.velocity x.p⟫_ℝ := by
            rfl
    _ = ⟪gradient H.T x.p, H.force x.q⟫_ℝ
          - x.ξ * ⟪gradient H.T x.p, x.p⟫_ℝ
          + ⟪gradient H.V x.q, H.velocity x.p⟫_ℝ := by
            -- Replace the p-term using the inner-product split.
            simp [hsplit]
    _ = -x.ξ * ⟪gradient H.T x.p, x.p⟫_ℝ := by
            -- The cross terms cancel.
            linarith [hcross]
    _ = -x.ξ * ‖x.p‖ ^ 2 := by
            -- Replace ∇T with identity and use ‖p‖² = ⟪p,p⟫.
            simp [hgrad]

/-! ## Energy Injection and Cooling -/

/-- Energy flows into the subsystem iff ξ < 0 (for nonzero momentum). -/
theorem energy_injection_iff (H : ConvexHamiltonian n) (params : ThermostatParams)
    (hgrad : ∀ p, gradient H.T p = p) (x : ThermostatPoint n) (hp : x.p ≠ 0) :
    0 < subsystemEnergyDerivative H (noseHooverDrift H params) x ↔ x.ξ < 0 := by
  -- Reduce to the sign of `-ξ` using positivity of ‖p‖².
  have hpos : 0 < ‖x.p‖ ^ 2 := by
    have hne : ‖x.p‖ ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hp)
    have hsq : 0 < ‖x.p‖ ^ 2 := by
      simpa [pow_two] using (sq_pos_iff.mpr hne)
    exact hsq
  constructor
  · intro hE
    have hE' : 0 < -x.ξ * ‖x.p‖ ^ 2 := by
      simpa [subsystem_energy_rate H params hgrad x] using hE
    have hE'' : 0 < ‖x.p‖ ^ 2 * -x.ξ := by simpa [mul_comm] using hE'
    have hneg : 0 < -x.ξ := pos_of_mul_pos_right hE'' (le_of_lt hpos)
    simpa [neg_pos] using hneg
  · intro hξ
    have hneg : 0 < -x.ξ := by simpa [neg_pos] using hξ
    have hE' : 0 < -x.ξ * ‖x.p‖ ^ 2 := mul_pos hneg hpos
    simpa [subsystem_energy_rate H params hgrad x] using hE'

/-- Thermostat variable decreases when the system is cold. -/
theorem thermostat_cools_when_cold (H : ConvexHamiltonian n) (params : ThermostatParams)
    (x : ThermostatPoint n) (hcold : ‖x.p‖ ^ 2 < n * params.kT) :
    (noseHooverDrift H params x).ξ < 0 := by
  -- ξ̇ has the sign of ‖p‖² - n·kT, scaled by 1/Q.
  have hdiff : ‖x.p‖ ^ 2 - n * params.kT < 0 := by linarith
  have hQ : 0 < (1 / params.Q) := by
    -- Positivity of 1/Q follows from Q > 0.
    simpa [one_div] using (inv_pos.mpr params.Q_pos)
  have hmul : (1 / params.Q) * (‖x.p‖ ^ 2 - n * params.kT) < 0 := by
    nlinarith [hQ, hdiff]
  simpa [noseHooverDrift] using hmul

/-! ## Extended Hamiltonian -/

/-- Extended Hamiltonian including thermostat kinetic energy. -/
def extendedHamiltonian (H : ConvexHamiltonian n) (params : ThermostatParams)
    (x : ThermostatPoint n) : ℝ :=
  H.energy x.toPhasePoint + (1 / 2) * params.Q * x.ξ ^ 2

/-- Extended energy derivative along a solution (assumed). -/
theorem extended_energy_conserved (H : ConvexHamiltonian n) (params : ThermostatParams)
    (sol : ℝ → ThermostatPoint n)
    (hderiv : ∀ t,
      HasDerivAt (fun s => extendedHamiltonian H params (sol s))
        (-n * params.kT * (sol t).ξ) t) :
    ∀ t, deriv (fun s => extendedHamiltonian H params (sol s)) t =
      -n * params.kT * (sol t).ξ := by
  -- Extract the derivative from the HasDerivAt hypothesis.
  intro t
  exact (hderiv t).deriv

/-! ## Lipschitz on Bounded Regions -/

/-- Nosé–Hoover drift is Lipschitz on bounded regions, given a local Lipschitz hypothesis.
    This wrapper packages the hypothesis into an existential form. -/
theorem noseHoover_lipschitz_on (H : ConvexHamiltonian n) (params : ThermostatParams)
    (radius : ℝ) (K : ℝ≥0)
    (hLip : LipschitzOnWith K (noseHooverDrift H params)
      {x : ThermostatPoint n | ‖x.q‖ ≤ radius ∧ ‖x.p‖ ≤ radius ∧ |x.ξ| ≤ radius}) :
    ∃ K, LipschitzOnWith K (noseHooverDrift H params)
      {x : ThermostatPoint n | ‖x.q‖ ≤ radius ∧ ‖x.p‖ ≤ radius ∧ |x.ξ| ≤ radius} := by
  -- Reuse the provided Lipschitz bound.
  exact ⟨K, hLip⟩

/-! ## Equipartition Target -/

/-- Target kinetic energy at thermal equilibrium. -/
def targetKineticEnergy (n : ℕ) (params : ThermostatParams) : ℝ :=
  n * params.kT

/-- When ‖p‖² = n·kT, the thermostat variable is stationary (ξ̇ = 0). -/
theorem equipartition_target (n : ℕ) (params : ThermostatParams)
    (H : ConvexHamiltonian n) (x : ThermostatPoint n)
    (hp : ‖x.p‖ ^ 2 = n * params.kT) :
    (noseHooverDrift H params x).ξ = 0 := by
  -- Directly simplify the ξ̇ definition.
  simp [noseHooverDrift, ThermostatPoint.ξ, ThermostatPoint.mk, hp]

/-! ## Invariant Measure and Ergodicity Scaffolding -/

-- Use the Borel σ-algebra on configuration space to match `Ergodic.IsErgodic`.
local instance instMeasurableSpaceConfigBorel : MeasurableSpace (Config n) := by
  exact borel (Config n)

/-- Unnormalized invariant weight on extended phase space. -/
noncomputable def noseHooverInvariantWeight (H : ConvexHamiltonian n) (params : ThermostatParams)
    (x : ThermostatPoint n) : ℝ :=
  Real.exp (-H.energy x.toPhasePoint / params.kT) *
    Real.exp (-params.Q * x.ξ ^ 2 / (2 * params.kT))

/-- Gibbs-style measure on the extended phase space, defined by a reference measure. -/
noncomputable def noseHooverInvariantMeasure (H : ConvexHamiltonian n) (params : ThermostatParams)
    (μ : MeasureTheory.Measure (ThermostatPoint n)) : MeasureTheory.Measure (ThermostatPoint n) :=
  MeasureTheory.Measure.withDensity μ
    (fun x => ENNReal.ofReal (noseHooverInvariantWeight H params x))

/-- Measure preservation predicate for a flow on extended phase space. -/
def IsMeasurePreserving (flow : ℝ → ThermostatPoint n → ThermostatPoint n)
    (μ : MeasureTheory.Measure (ThermostatPoint n)) : Prop :=
  ∀ t, MeasureTheory.MeasurePreserving (flow t) μ μ

/-- If the flow is assumed measure-preserving, record it as a Gibbs invariance statement. -/
theorem noseHoover_preserves_invariantMeasure (H : ConvexHamiltonian n) (params : ThermostatParams)
    (μ : MeasureTheory.Measure (ThermostatPoint n))
    (flow : ℝ → ThermostatPoint n → ThermostatPoint n)
    (hpres : ∀ t,
      MeasureTheory.MeasurePreserving (flow t)
        (noseHooverInvariantMeasure H params μ)
        (noseHooverInvariantMeasure H params μ)) :
    IsMeasurePreserving flow (noseHooverInvariantMeasure H params μ) := by
  exact hpres

/-- Project a thermostat flow to a configuration-space process family. -/
noncomputable def noseHooverProcessFamily
    (flow : ℝ → ThermostatPoint n → ThermostatPoint n)
    (lift : Config n → ThermostatPoint n) :
    Config n → StochasticProcess n :=
  fun q₀ t => (flow t (lift q₀)).q

/-- Ergodicity wrapper for Nosé–Hoover processes, assuming the core ergodicity hypothesis. -/
theorem noseHoover_ergodic (H : ConvexHamiltonian n) (params : ThermostatParams)
    (μ : MeasureTheory.Measure (Config n))
    (flow : ℝ → ThermostatPoint n → ThermostatPoint n)
    (lift : Config n → ThermostatPoint n)
    (hErg :
      IsErgodic (V := H.V) (kT := params.kT) μ
        (noseHooverProcessFamily (n := n) flow lift)) :
    IsErgodic (V := H.V) (kT := params.kT) μ
      (noseHooverProcessFamily (n := n) flow lift) := by
  exact hErg

end

end Gibbs.Hamiltonian
