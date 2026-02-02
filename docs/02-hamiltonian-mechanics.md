# Hamiltonian Mechanics

Physical systems evolve by trading energy between different forms. A pendulum converts potential energy into kinetic energy and back. A damped spring loses energy to friction until it comes to rest. A thermostat injects and extracts energy to maintain a target temperature. In each case, the total energy function governs the dynamics.

Gibbs takes this as its starting point. The Hamiltonian (total energy) defines a landscape over the system's state space. Convexity of that landscape is the central structural assumption. It guarantees that energy has a well-defined minimum, that the Legendre transform connecting position and momentum descriptions is well-behaved, and that damped systems converge to equilibrium. These properties propagate through every module in the project: convex duality (Chapter 3) inherits the energy structure, mean-field dynamics (Chapter 4) uses it for stability, and consensus (Chapter 8) reinterprets energy gaps as fault tolerance thresholds.

This chapter covers the undamped and damped equations of motion, energy conservation and dissipation, Lyapunov stability, the Nose-Hoover thermostat, Gibbs ensembles, stochastic (Langevin) dynamics, and a concrete case study in lattice electrodynamics.

For the convex analysis toolkit, see [Convex Duality and Bregman Divergence](03-convex-duality.md). For how these dynamics connect to population models, see [Mean-Field Dynamics](04-mean-field.md).

## Phase Space and Separable Hamiltonians

A system with $n$ degrees of freedom lives in a $2n$-dimensional phase space: $n$ position coordinates and $n$ momentum coordinates. The configuration space is `Config n = EuclideanSpace ℝ (Fin n)`. A phase point bundles position $q$ and momentum $p$ into a pair. The Hamiltonian is the total energy:

$$H(q, p) = T(p) + V(q)$$

Separability means kinetic energy $T$ depends only on momentum and potential energy $V$ depends only on position. Both are assumed convex and differentiable everywhere. The canonical example is the harmonic oscillator with $T(p) = \frac{1}{2}\|p\|^2$ and $V(q) = \frac{1}{2}\omega^2\|q\|^2$.

The structure `ConvexHamiltonian n` bundles $T$, $V$, their convexity proofs, and their differentiability proofs.

## Symplectic vs Damped Dynamics

The distinction between conservative and dissipative systems is fundamental. A frictionless pendulum swings forever. A pendulum in honey comes to rest. Both obey the same Hamiltonian, but damping changes the long-term behavior entirely.

The undamped (symplectic) equations of motion are:

$$\dot{q} = \nabla_p T, \quad \dot{p} = -\nabla_q V$$

Energy is exactly conserved along these trajectories. The proof in `symplectic_energy_conserved` shows $dH/dt = 0$ by inner-product cancellation.

Adding linear friction produces the damped system:

$$\dot{q} = \nabla_p T, \quad \dot{p} = -\nabla_q V - \gamma p$$

The damping coefficient $\gamma > 0$ introduces energy dissipation. Computing the time derivative of energy along damped trajectories gives the key identity:

$$\frac{dH}{dt} = -\gamma \|p\|^2 \leq 0$$

This inequality makes $H$ a Lyapunov function. Energy decreases monotonically and can only be zero when momentum vanishes. The theorem `energy_dissipation` proves this identity, and `energy_decreasing` establishes monotonicity.

## The Lyapunov Connection

How do you prove a system converges to equilibrium without solving the equations of motion? The answer is to find a quantity that always decreases. If you can exhibit such a function, convergence follows without computing a single trajectory.

A Lyapunov function $V$ for a dynamical system satisfies three properties: it is nonneg, zero at equilibrium, and decreasing along trajectories. The damped Hamiltonian satisfies all three when $V$ has a unique minimum.

The `LyapunovData` and `StrictLyapunovData` structures in `Stability.lean` capture these conditions. A strict Lyapunov function additionally tends to zero along trajectories, which gives asymptotic stability. The theorem `damped_asymptotically_stable` packages this implication.

Exponential energy decay occurs when the system is strongly convex. The `ExponentialEnergyDecay` predicate and `exponential_convergence` theorem provide convergence rate bounds via the condition number $L/m$.

## Nosé-Hoover Thermostat

Constant damping drives a system to zero energy. But in statistical mechanics, the goal is often to maintain a specific temperature, not to cool to absolute zero. The Nose-Hoover thermostat achieves this with a feedback variable $\xi$ that speeds up or slows down particles to hold the average kinetic energy at a target $kT$:

$$\dot{q} = \nabla_p T, \quad \dot{p} = -\nabla_q V - \xi p, \quad \dot{\xi} = \frac{\|p\|^2 - n \cdot kT}{Q}$$

The thermostat mass $Q > 0$ controls the coupling timescale. When kinetic energy exceeds the target ($\|p\|^2 > n \cdot kT$), $\xi$ increases, extracting energy. When kinetic energy falls below the target, $\xi$ decreases, injecting energy. Equilibrium occurs at equipartition: $\|p\|^2 = n \cdot kT$.

The subsystem energy rate is $dH/dt = -\xi \|p\|^2$. Unlike constant damping, the sign of $\xi$ fluctuates. An extended Hamiltonian that includes the $\xi$ degree of freedom is exactly conserved, proved in `extended_energy_conserved`.

## Gibbs Ensemble and Ergodicity

Rather than tracking a single trajectory, statistical mechanics describes the probability of finding the system in each configuration. At thermal equilibrium, low-energy configurations are exponentially more likely than high-energy ones.

The Gibbs (Boltzmann) distribution assigns probability proportional to $e^{-V(q)/kT}$ to each configuration. The partition function normalizes this weight:

$$Z = \int e^{-V(q)/kT} \, d\mu(q)$$

The `gibbsDensity` divides the Boltzmann weight by $Z$ to produce a probability density. The theorem `gibbsDensity_integral_eq_one` confirms normalization.

The ergodic hypothesis asserts that time averages along trajectories equal ensemble averages against the Gibbs density. The `IsErgodic` predicate captures this equality. Time averages of constant functions are trivially ergodic, proved in `ergodic_of_constant_process`.

## Stochastic Extension

Real physical systems are not deterministic at the microscopic level. Thermal fluctuations randomly kick particles, and the strength of these kicks is tied to the amount of damping. Langevin dynamics models this by adding noise to the damped system:

$$\dot{q} = \nabla_p T, \quad dp = (-\nabla_q V - \gamma p) \, dt + \sigma \, dW$$

The noise strength $\sigma$ satisfies the fluctuation-dissipation relation $\sigma^2 = 2\gamma kT$. This ensures the Gibbs density is the stationary distribution of the associated Fokker-Planck equation.

The theorem `gibbs_is_stationary` in `ChannelNoise.lean` proves stationarity by direct substitution of the Gibbs density into the Fokker-Planck operator and cancellation via $\sigma^2 = 2\gamma kT$. The `LangevinParams` structure bundles the potential, damping, and temperature with their positivity constraints.

The stochastic layer uses a constant-diffusion model. The Itô integral for constant diffusion matrices reduces to $\int_0^t A \, dW = A(W_t - W_0)$, implemented using Mathlib's Bochner integral.

## Case Study: Lattice Maxwell

Let's use Gibbs to work with Maxwell's equations. The electromagnetic field energy on a lattice is quadratic (and therefore convex):

$$H = \frac{1}{2} \sum_i \left( \varepsilon \|E_i\|^2 + \frac{1}{\mu} \|B_i\|^2 \right)$$

Adding conductivity $\sigma$ introduces Ohmic damping: $dH/dt = -\int \sigma |E|^2 \, dx \leq 0$. The Hamiltonian becomes a Lyapunov function, so a lattice Maxwell system with conductivity fits naturally into our framework. The discrete curl operator couples neighboring lattice sites, serving as the spatial kernel. To distribute the computation, domain decomposition partitions the lattice into regions, each assigned to a session role.

| Regime | Status |
|---|---|
| Lattice Maxwell + conductivity | Full support |
| Vacuum Maxwell ($\sigma = 0$) | Integrable, periodic solutions |
| Dispersive media | Memory effects for $\varepsilon(\omega)$ |
| Nonlinear optics | Loss of quadratic structure |

The implementation in `LatticeMaxwell.lean` provides lattice index types, quadratic field energy, zero-field minimizer proofs, curl stencils, ghost sets, and local/global coherence proofs for subdomains.
