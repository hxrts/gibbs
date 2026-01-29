import Gibbs.Hamiltonian.Basic

/-!
Minimal stochastic scaffolding for Hamiltonian dynamics.

This module intentionally axiomatizes Brownian paths and the Itô integral
interface, so downstream files can state SDE solution predicates without
committing to a full stochastic analysis library.
-/

namespace Gibbs.Hamiltonian.Stochastic

noncomputable section

/-! ## Brownian paths -/

/-- A Brownian path is represented as a time-indexed configuration curve
    together with the zero initial condition. -/
structure BrownianPath (n : ℕ) where
  /-- The path realization. -/
  path : ℝ → Config n
  /-- Brownian paths start at the origin. -/
  zero : path 0 = 0

instance (n : ℕ) : CoeFun (BrownianPath n) (fun _ => ℝ → Config n) :=
  ⟨BrownianPath.path⟩

/-! ## Abstract SDE interface -/

/-- An SDE on phase space with drift and diffusion fields. -/
structure SDE (n : ℕ) where
  /-- Deterministic drift. -/
  drift : PhasePoint n → PhasePoint n
  /-- Diffusion coefficient. -/
  diffusion : PhasePoint n → PhasePoint n

/-- Abstract Itô integration operator for drift and diffusion terms. -/
structure SDEIntegral (n : ℕ) where
  /-- Integral of a time-dependent drift term. -/
  driftIntegral : (ℝ → PhasePoint n) → ℝ → PhasePoint n
  /-- Integral of a time-dependent diffusion term against a Brownian path. -/
  diffusionIntegral : (ℝ → PhasePoint n) → BrownianPath n → ℝ → PhasePoint n

/-- A trajectory solves an SDE relative to a chosen stochastic integral. -/
def SolvesSDE (I : SDEIntegral n) (sde : SDE n)
    (W : BrownianPath n) (X : ℝ → PhasePoint n) : Prop :=
  ∀ t, X t =
    X 0 +
      I.driftIntegral (fun s => sde.drift (X s)) t +
      I.diffusionIntegral (fun s => sde.diffusion (X s)) W t

/-- A concrete SDE process bundles data and a proof of the solution predicate. -/
structure SDEProcess (n : ℕ) where
  /-- The SDE being solved. -/
  sde : SDE n
  /-- Integration operator (axiomatized). -/
  integral : SDEIntegral n
  /-- Driving Brownian path. -/
  brownian : BrownianPath n
  /-- Sample path of the process. -/
  path : ℝ → PhasePoint n
  /-- The path satisfies the SDE in the chosen integration theory. -/
  solves : SolvesSDE integral sde brownian path

end
