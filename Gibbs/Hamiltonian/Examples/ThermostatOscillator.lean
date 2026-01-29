import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.NoseHoover

/-
The Problem. Provide a concrete Nosé-Hoover example: the harmonic oscillator
coupled to a thermostat. This is used to instantiate the general thermostat
machinery in a simple setting.

The difficulty is minimal: we just bundle the harmonic oscillator Hamiltonian
with thermostat parameters.

Solution Structure.
1. Define `ThermostatOscillator` as a pair of the harmonic oscillator and
   thermostat parameters.
-/

namespace Gibbs.Hamiltonian.Examples

noncomputable section

/-! ## Thermostat Oscillator -/

/-- Harmonic oscillator with Nosé-Hoover parameters. -/
abbrev ThermostatOscillator (n : ℕ) := ConvexHamiltonian n × ThermostatParams

/-- Build a thermostat oscillator from parameters. -/
noncomputable def thermostatOscillator (n : ℕ) (params : ThermostatParams) :
    ThermostatOscillator n := by
  -- Bundle the canonical harmonic oscillator with the given parameters.
  exact (harmonicOscillator n, params)

/-! ## Drift Instantiation -/

/-- Nosé–Hoover drift specialized to the harmonic oscillator. -/
noncomputable def thermostat_oscillator_drift (n : ℕ) (params : ThermostatParams) :
    ThermostatPoint n → ThermostatPoint n := by
  -- Apply the thermostat drift to the harmonic oscillator Hamiltonian.
  exact noseHooverDrift (harmonicOscillator n) params

/-! ## Equipartition at Equilibrium -/

/-- At equilibrium, kinetic energy equals the thermostat target. -/
theorem equipartition_at_equilibrium (n : ℕ) (params : ThermostatParams)
    (x : ThermostatPoint n)
    (hξ : (thermostat_oscillator_drift n params x).ξ = 0) :
    ‖x.p‖ ^ 2 = n * params.kT := by
  -- Unfold ξ̇ = (1/Q)(‖p‖² - n·kT) and cancel the nonzero factor.
  have hQne : (1 / params.Q) ≠ 0 := by
    -- Q > 0 implies 1/Q ≠ 0.
    exact one_div_ne_zero (ne_of_gt params.Q_pos)
  have hzero : (1 / params.Q) * (‖x.p‖ ^ 2 - n * params.kT) = 0 := by
    simpa [thermostat_oscillator_drift, noseHooverDrift,
      ThermostatPoint.ξ, ThermostatPoint.mk] using hξ
  have hdiff : ‖x.p‖ ^ 2 - n * params.kT = 0 := by
    exact (mul_eq_zero.mp hzero).resolve_left hQne
  linarith

/-! ## Bounded Trajectories -/

/-- The origin in thermostat phase space. -/
private def thermostatOrigin (n : ℕ) : ThermostatPoint n :=
  -- Zero position, momentum, and thermostat variable.
  ThermostatPoint.mk 0 0 0

/-- The extended Hamiltonian vanishes at the origin. -/
private theorem extendedHamiltonian_origin (n : ℕ) (params : ThermostatParams) :
    extendedHamiltonian (harmonicOscillator n) params (thermostatOrigin n) = 0 := by
  -- Expand the Hamiltonian and use that all components are zero.
  simp [thermostatOrigin, extendedHamiltonian, ThermostatPoint.toPhasePoint,
    ThermostatPoint.q, ThermostatPoint.p, ThermostatPoint.ξ, ThermostatPoint.mk,
    _root_.Gibbs.Hamiltonian.HarmonicOscillator.energy_eq]

/-- Expand the conserved extended energy for the harmonic oscillator. -/
private theorem thermostat_energy_expand (n : ℕ) (params : ThermostatParams)
    (sol : ℝ → ThermostatPoint n) (E : ℝ)
    (hconst : ∀ t, extendedHamiltonian (harmonicOscillator n) params (sol t) = E)
    (t : ℝ) :
    E =
      (1 / 2) * ‖(sol t).p‖ ^ 2 + (1 / 2) * ‖(sol t).q‖ ^ 2 +
        (1 / 2) * params.Q * (sol t).ξ ^ 2 := by
  -- Rewrite the extended Hamiltonian using the harmonic oscillator energy.
  simpa [extendedHamiltonian, _root_.Gibbs.Hamiltonian.HarmonicOscillator.energy_eq,
    ThermostatPoint.toPhasePoint_q, ThermostatPoint.toPhasePoint_p, add_assoc] using
    (hconst t).symm

/-- Each half-energy term is bounded by the conserved total energy. -/
private theorem thermostat_half_bounds (n : ℕ) (params : ThermostatParams)
    (sol : ℝ → ThermostatPoint n) (E : ℝ)
    (hconst : ∀ t, extendedHamiltonian (harmonicOscillator n) params (sol t) = E)
    (t : ℝ) :
    (1 / 2) * ‖(sol t).q‖ ^ 2 ≤ E ∧
      (1 / 2) * ‖(sol t).p‖ ^ 2 ≤ E ∧
      (1 / 2) * params.Q * (sol t).ξ ^ 2 ≤ E := by
  -- Expand the energy and drop nonnegative terms.
  have hE := thermostat_energy_expand n params sol E hconst t
  have hq_nonneg : 0 ≤ (1 / 2) * ‖(sol t).q‖ ^ 2 := by positivity
  have hp_nonneg : 0 ≤ (1 / 2) * ‖(sol t).p‖ ^ 2 := by positivity
  have hxi_nonneg : 0 ≤ (1 / 2) * params.Q * (sol t).ξ ^ 2 := by
    -- Q > 0 and ξ² ≥ 0 ensure nonnegativity.
    have hQ : 0 ≤ params.Q := le_of_lt params.Q_pos
    have hξ : 0 ≤ (sol t).ξ ^ 2 := by nlinarith
    nlinarith [hQ, hξ]
  -- Bound each term by discarding the other nonnegative terms.
  have hq_le : (1 / 2) * ‖(sol t).q‖ ^ 2 ≤ E := by
    nlinarith [hE, hp_nonneg, hxi_nonneg]
  have hp_le : (1 / 2) * ‖(sol t).p‖ ^ 2 ≤ E := by
    nlinarith [hE, hq_nonneg, hxi_nonneg]
  have hxi_le : (1 / 2) * params.Q * (sol t).ξ ^ 2 ≤ E := by
    nlinarith [hE, hq_nonneg, hp_nonneg]
  exact ⟨hq_le, hp_le, hxi_le⟩

/-- If the extended Hamiltonian is constant, the oscillator's components are bounded. -/
theorem thermostat_oscillator_bounded (n : ℕ) (params : ThermostatParams)
    (sol : ℝ → ThermostatPoint n) (E : ℝ)
    (hconst : ∀ t, extendedHamiltonian (harmonicOscillator n) params (sol t) = E) :
    ∀ t, ‖(sol t).q‖ ^ 2 ≤ 2 * E ∧
      ‖(sol t).p‖ ^ 2 ≤ 2 * E ∧
      params.Q * (sol t).ξ ^ 2 ≤ 2 * E := by
  -- Convert half-energy bounds into full bounds.
  intro t
  obtain ⟨hq_le, hp_le, hxi_le⟩ := thermostat_half_bounds n params sol E hconst t
  refine ⟨?_, ?_, ?_⟩
  · -- Convert the half-bound into a full bound for ‖q‖².
    nlinarith [hq_le]
  · -- Convert the half-bound into a full bound for ‖p‖².
    nlinarith [hp_le]
  · -- Convert the half-bound into a full bound for Q·ξ².
    nlinarith [hxi_le]

/-! ## Non-decay to the Origin -/

/-- If the extended energy is positive and conserved, the solution never reaches the origin. -/
theorem thermostat_oscillator_oscillates (n : ℕ) (params : ThermostatParams)
    (sol : ℝ → ThermostatPoint n) (E : ℝ)
    (hconst : ∀ t, extendedHamiltonian (harmonicOscillator n) params (sol t) = E)
    (hEpos : 0 < E) :
    ∀ t, sol t ≠ thermostatOrigin n := by
  -- Reaching the origin would force the conserved energy to be zero.
  intro t hzero
  have hzeroE : E = extendedHamiltonian (harmonicOscillator n) params (thermostatOrigin n) := by
    -- Rewrite the conserved energy at the origin.
    simpa [hzero] using (hconst t).symm
  have hE : E = 0 := by
    -- Use the origin energy computation.
    simpa [extendedHamiltonian_origin n params] using hzeroE
  exact (lt_irrefl 0) (by simp [hE] at hEpos)

end

end Gibbs.Hamiltonian.Examples
