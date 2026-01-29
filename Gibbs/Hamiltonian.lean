import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.DampedFlow
import Gibbs.Hamiltonian.Ergodic
import Gibbs.Hamiltonian.FenchelMoreau
import Gibbs.Hamiltonian.Legendre
import Gibbs.Hamiltonian.NoseHoover
import Gibbs.Hamiltonian.Choreography
import Gibbs.Hamiltonian.Stability
import Gibbs.Hamiltonian.Examples.HarmonicOscillator
import Gibbs.Hamiltonian.Examples.Langevin
import Gibbs.Hamiltonian.Examples.ThermostatOscillator
import Gibbs.Hamiltonian.Examples.GradientDescent
import Gibbs.Hamiltonian.Examples.LatticeMaxwell

/-! # Gibbs.Hamiltonian

Hamiltonian mechanics infrastructure for the Gibbs framework.

## Overview

This module provides types and theorems for Hamiltonian systems,
focusing on the tractable subset: convex Hamiltonians with dissipation.
The key insight is that damped convex Hamiltonians have the Hamiltonian
itself as a Lyapunov function, enabling reuse of MeanField stability machinery.

## Main Definitions

- `Config n`: Configuration space as EuclideanSpace ℝ (Fin n)
- `PhasePoint n`: Phase space (q, p) pairs
- `ConvexHamiltonian n`: Separable H = T(p) + V(q) with convexity
- `StrictlyConvexHamiltonian n`: Adds strict convexity of V
- `Damping`, `dampedDrift`: Dissipative Hamiltonian dynamics
- `ThermostatParams`, `noseHooverDrift`: Deterministic thermal reservoir
- `legendre`: Legendre transform (convex conjugate)
- `bregman`: Bregman divergence
- `fenchel_moreau_roadmap`: roadmap statement for f** = f under subgradients

## Main Results

- `bregman_nonneg`: Bregman divergence ≥ 0 for convex functions
- `bregman_eq_zero_iff`: D_f(x,y) = 0 ↔ x = y for strictly convex f
- `quadraticKinetic_convex`: ½‖p‖² is convex
- `quadraticPotential_strictConvex`: ½‖q‖² is strictly convex

## References

- Reference implementation for Lipschitz proofs:
  `work/aristotle/02_damped_drift_lipschitz_solution.lean`
- Reference implementation for Maxwell domain decomposition:
  `work/aristotle/09_maxwell_domain_decomposition_solition.lean`
-/
