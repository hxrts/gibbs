import Gibbs.Hamiltonian.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Minimal stochastic scaffolding for Hamiltonian dynamics.

This module models constant-diffusion Langevin noise by using the closed-form
Itô integral for a constant diffusion matrix: `∫₀ᵗ A dW = A (W_t - W_0)`. We keep
the diffusion term constant so that the noise contribution is concrete rather
than axiomatic.

Limitations:
- The diffusion term is constant in time and state.
- We do not model Itô/Stratonovich integrals for general predictable processes.
- Only a minimal Brownian interface is exposed (coordinate-wise Brownian).
- The goal is to provide a concrete integral form without building a full SDE
  theory.
-/

namespace Gibbs.Hamiltonian.Stochastic

noncomputable section

open MeasureTheory
/-! ## Processes and Brownian motion -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stochastic process on phase space. -/
abbrev StochasticProcess (n : ℕ) := ℝ → Ω → PhasePoint n

/-- A Brownian motion on configuration space (coordinate-wise). -/
structure BrownianMotion (n : ℕ) where
  /-- Path realization. -/
  path : ℝ → Ω → Config n
  /-- Brownian paths start at the origin. -/
  zero : ∀ ω, path 0 ω = 0

instance (n : ℕ) : CoeFun (BrownianMotion (Ω := Ω) n)
    (fun _ => ℝ → Ω → Config n) :=
  ⟨BrownianMotion.path⟩

/-! ## Additive-noise SDE -/

/-- An additive-noise SDE on phase space with constant diffusion. -/
structure SDE (n : ℕ) where
  /-- Deterministic drift. -/
  drift : PhasePoint n → PhasePoint n
  /-- Constant diffusion map from configuration-space noise to phase space. -/
  diffusion : Config n →L[ℝ] PhasePoint n

/-- The stochastic integral of a constant diffusion map against Brownian motion.
    For constant `A`, `∫₀ᵗ A dW = A (W_t - W_0)`. -/
noncomputable def stochasticIntegral (n : ℕ) (A : Config n →L[ℝ] PhasePoint n)
    (W : BrownianMotion (Ω := Ω) n) : StochasticProcess (Ω := Ω) n :=
  fun t ω => A (W.path t ω)

/-- Integral solution for additive-noise SDEs with constant diffusion.
    `X_t = X_0 + ∫₀ᵗ b(X_s) ds + ∫₀ᵗ A dW_s`. -/
def SolvesSDE (sde : SDE n) (W : BrownianMotion (Ω := Ω) n)
    (X : StochasticProcess (Ω := Ω) n) : Prop :=
  ∀ t ω,
    X t ω =
      X 0 ω +
        ∫ s in Set.Icc (0 : ℝ) t, sde.drift (X s ω) +
        stochasticIntegral (Ω := Ω) (n := n) sde.diffusion W t ω

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

end Gibbs.Hamiltonian.Stochastic
