import Gibbs.Hamiltonian.NoseHoover
import Gibbs.Hamiltonian.Stochastic.Basic

/-!
# Simplex-Projected Langevin Drift

On the probability simplex, any drift must preserve the constraint that
coordinates sum to one. The standard technique is to project an unconstrained
drift onto the simplex tangent space by subtracting its mean, enforcing
mass conservation. This file defines the projection, proves it preserves
the sum, and shows it acts as the identity on drifts that already conserve mass.
-/

namespace Gibbs.Hamiltonian.Examples

open scoped BigOperators

noncomputable section


/-! ## Simplex Projection -/

/-- Project a drift onto the simplex tangent space by subtracting its mean. -/
noncomputable def simplexProject (n : ℕ) (v : Fin n → ℝ) : Fin n → ℝ := by
  -- Enforce sum-zero by removing the average component.
  exact fun i => v i - (1 / (n : ℝ)) * ∑ j, v j

/-- The simplex projection has zero total mass. -/
theorem simplexProject_sum_zero (n : ℕ) [NeZero n] (v : Fin n → ℝ) :
    ∑ i, simplexProject n v i = 0 := by
  -- Expand the sum and cancel the mean correction.
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by
    -- Convert `card_univ` to `n` using `Fintype.card_fin`.
    simp [Fintype.card_fin]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  set s : ℝ := ∑ j, v j
  have hsum :
      ∑ i, simplexProject n v i = s - (1 / (n : ℝ)) * (n : ℝ) * s := by
    -- Sum the constant correction term.
    simp [simplexProject, Finset.sum_sub_distrib, Finset.sum_const, hcard, s,
      mul_comm, mul_left_comm]
  calc
    ∑ i, simplexProject n v i = s - (1 / (n : ℝ)) * (n : ℝ) * s := hsum
    _ = s - s := by simp [one_div, hn]
    _ = 0 := by simp [s]

/-! ## Connection to Gradient Descent -/

/-- If a drift already conserves mass, simplex projection leaves it unchanged. -/
theorem simplexProject_eq_of_sum_zero (n : ℕ) (v : Fin n → ℝ)
    (hsum : ∑ i, v i = 0) :
    simplexProject n v = v := by
  -- The mean correction term vanishes when the sum is zero.
  funext i
  simp [simplexProject, hsum]

end

/-! ## Comparison with Nosé–Hoover -/

/-- When the thermostat variable equals the damping coefficient, the
    Nosé–Hoover drift agrees with the damped drift on (q,p). -/
theorem noseHoover_matches_damped {n : ℕ} (H : ConvexHamiltonian n) (d : Damping)
    (params : ThermostatParams) (x : ThermostatPoint n) (hξ : x.ξ = d.γ) :
    (noseHooverDrift H params x).toPhasePoint = dampedDrift H d x.toPhasePoint := by
  -- Expand both drifts and rewrite ξ = γ.
  rcases x with ⟨q, p, ξ⟩
  have hξ' : ξ = d.γ := by simpa [ThermostatPoint.ξ] using hξ
  -- Unfold the drifts to a pair equality.
  change (H.velocity p, H.force q - ξ • p) = (H.velocity p, H.force q - d.γ • p)
  -- Compare components and use ξ = γ.
  refine Prod.ext ?_ ?_
  · rfl
  · simp [hξ']

/-! ## Same Equilibrium, Different Dynamics -/

/-- Unnormalized Gibbs density for a Hamiltonian at temperature kT. -/
noncomputable def gibbsDensity (H : ConvexHamiltonian n) (kT : ℝ) : PhasePoint n → ℝ :=
  fun x => Real.exp (-H.energy x / kT)

/-- Equilibrium density targeted by Langevin dynamics. -/
noncomputable def langevinEquilibrium (H : ConvexHamiltonian n) (kT : ℝ) : PhasePoint n → ℝ :=
  gibbsDensity H kT

/-- Equilibrium density targeted by Nosé–Hoover dynamics. -/
noncomputable def noseHooverEquilibrium (H : ConvexHamiltonian n) (kT : ℝ) : PhasePoint n → ℝ :=
  gibbsDensity H kT

/-- Langevin and Nosé–Hoover target the same Gibbs equilibrium density. -/
theorem langevin_noseHoover_same_equilibrium (H : ConvexHamiltonian n) (kT : ℝ) :
    langevinEquilibrium H kT = noseHooverEquilibrium H kT := by
  -- Both are defined to be the Gibbs density.
  rfl

/-! ## Stochastic Extension (Minimal Core) -/

/-- A Langevin SDE with damped drift and constant momentum noise. -/
noncomputable def langevinSDE (H : ConvexHamiltonian n) (d : Damping) (σ : ℝ) :
    Gibbs.Hamiltonian.Stochastic.SDE n := by
  -- Noise lives in the momentum component; the position noise is zero.
  refine { drift := dampedDrift H d, diffusion := ?_ }
  exact (σ : ℝ) • ContinuousLinearMap.inr ℝ (Config n) (Config n)

/-- A concrete Langevin process from a chosen integration theory and Brownian path. -/
noncomputable def langevinProcess {Ω : Type*} [MeasurableSpace Ω]
    (H : ConvexHamiltonian n) (d : Damping) (σ : ℝ)
    (W : Gibbs.Hamiltonian.Stochastic.BrownianMotion (Ω := Ω) n)
    (X : Gibbs.Hamiltonian.Stochastic.StochasticProcess (Ω := Ω) n)
    (hX : Gibbs.Hamiltonian.Stochastic.SolvesSDE (Ω := Ω) (langevinSDE H d σ) W X) :
    Gibbs.Hamiltonian.Stochastic.SDEProcess (Ω := Ω) n :=
  { sde := langevinSDE H d σ
    brownian := W
    path := X
    solves := hX }

end Gibbs.Hamiltonian.Examples
