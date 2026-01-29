import Gibbs.MeanField.Examples.Ising.TanhAnalysis
import Gibbs.MeanField.Examples.Ising.Drift
import Gibbs.MeanField.Examples.Ising.Glauber
import Gibbs.MeanField.Examples.Ising.PhaseTransition

/-
The Problem. Re-export all Ising model submodules through a single facade.

Solution Structure.
1. TanhAnalysis: analytic properties of tanh (Lipschitz, strict sub-linearity)
2. Drift: Ising drift function, conservation, Lipschitz property, choreography
3. Glauber: local transition rates and projection correctness
4. PhaseTransition: paramagnetic uniqueness and ferromagnetic bistability
-/
