import Gibbs.Hamiltonian.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Minimal stochastic scaffolding for Hamiltonian dynamics.

This module is a lightweight bridge to Mathlib's measure-theoretic process
machinery. We avoid axiomatizing a bespoke Itô integral by restricting to
additive-noise SDEs in integral form, using Bochner integrals in time.

Limitations:
- `BrownianMotion` is only a pathwise object (zero-started paths), with no
  distributional axioms or filtration/adaptedness hypotheses.
- SDE solutions are expressed in a deterministic integral form with additive
  noise; we do not model Itô/Stratonovich integration here.
- This is sufficient for wiring example code, but not for stochastic analysis
  theorems that require true Brownian properties.
-/

namespace Gibbs.Hamiltonian.Stochastic

noncomputable section

open MeasureTheory

/-! ## Processes and Brownian motion (pathwise) -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stochastic process on phase space. -/
abbrev StochasticProcess (n : ℕ) := ℝ → Ω → PhasePoint n

/-- A Brownian motion on configuration space (pathwise view).
    This is intentionally minimal and does not encode distributional axioms. -/
structure BrownianMotion (n : ℕ) where
  /-- Path realization. -/
  path : ℝ → Ω → Config n
  /-- Brownian paths start at the origin. -/
  zero : ∀ ω, path 0 ω = 0

instance (n : ℕ) : CoeFun (BrownianMotion (Ω := Ω) n) (fun _ => ℝ → Ω → Config n) :=
  ⟨BrownianMotion.path⟩

/-! ## Additive-noise SDE -/

/-- An additive-noise SDE on phase space. -/
structure SDE (n : ℕ) where
  /-- Deterministic drift. -/
  drift : PhasePoint n → PhasePoint n
  /-- Noise embedding into phase space. -/
  noise : Config n → PhasePoint n

/-- Pathwise integral solution for additive-noise SDEs.
    `X_t = X_0 + ∫₀ᵗ b(X_s) ds + noise (W_t)` (with `W_0 = 0`). -/
def SolvesSDE (sde : SDE n) (W : BrownianMotion (Ω := Ω) n)
    (X : StochasticProcess (Ω := Ω) n) : Prop :=
  ∀ t ω,
    X t ω =
      X 0 ω +
        ∫ s in Set.Icc (0 : ℝ) t, sde.drift (X s ω) +
        sde.noise (W.path t ω)

/-- A concrete SDE process bundles data and a proof of the solution predicate. -/
structure SDEProcess (n : ℕ) where
  /-- The SDE being solved. -/
  sde : SDE n
  /-- Driving Brownian motion. -/
  brownian : BrownianMotion (Ω := Ω) n
  /-- Sample path of the process. -/
  path : StochasticProcess (Ω := Ω) n
  /-- The path satisfies the SDE in integral form. -/
  solves : SolvesSDE (Ω := Ω) sde brownian path

end
