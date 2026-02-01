import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.DampedFlow
import Gibbs.Hamiltonian.Ergodic
import Gibbs.Hamiltonian.FenchelMoreau
import Gibbs.Hamiltonian.GaussianIntegrals
import Gibbs.Hamiltonian.GeneralHamiltonian
import Gibbs.Hamiltonian.Legendre
import Gibbs.Hamiltonian.PartitionFunction
import Gibbs.Hamiltonian.EnergyDistance
import Gibbs.Hamiltonian.EnergyGap
import Gibbs.Hamiltonian.NoseHoover
import Gibbs.Hamiltonian.SymplecticFlow
import Gibbs.Hamiltonian.Stochastic
import Gibbs.Hamiltonian.Choreography
import Gibbs.Hamiltonian.Stability
import Gibbs.Hamiltonian.Examples.HarmonicOscillator
import Gibbs.Hamiltonian.Examples.Langevin
import Gibbs.Hamiltonian.Examples.ThermostatOscillator
import Gibbs.Hamiltonian.Examples.GradientDescent
import Gibbs.Hamiltonian.Examples.GradientDescentMinimizer
import Gibbs.Hamiltonian.Examples.HeavyBallConvergence
import Gibbs.Hamiltonian.Examples.LatticeMaxwell

/-
The Problem. Provide a single entry point for the Hamiltonian layer so
clients can import phase space, convex Hamiltonians, damped dynamics,
Legendre transforms, stability, ergodic infrastructure, Nosé-Hoover
thermostat, choreography, and examples without enumerating individual files.

Solution Structure.
1. Re-export all Hamiltonian submodules and examples
-/
