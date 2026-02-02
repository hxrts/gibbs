# Continuum Fields

The mean-field module describes populations where every agent interacts with every other agent equally. In many systems this is not realistic. Molecules in a fluid interact with nearby molecules, not distant ones. Electromagnetic fields couple neighboring lattice sites through curl operators. Flocking birds align with neighbors within a perceptual cone, not with the entire flock.

The ContinuumField module extends the discrete framework to spatially extended systems. Instead of a finite state space with uniform coupling, the state is a set of fields over continuous space, and interactions are mediated by nonlocal integral kernels. The central result is that projecting the global kernel to local displacement coordinates introduces zero approximation error. Global and local operators are definitionally equal, proved by `rfl`. This exactness guarantee means that distributing the computation across spatial roles loses nothing.

For the discrete population dynamics that this module generalizes, see [Mean-Field Dynamics](04-mean-field.md). For the session-type guarantees that govern the distributed computation, see [The Session-Physics Correspondence](07-session-physics-correspondence.md).

## Fields and Kernels

A `FieldState X V W` bundles three fields over a measurable space $X$: a density field $\rho(x)$, a polarization field $p(x)$ (vector-valued), and an optional spin field $\omega(x)$. These are the continuum analogues of population counts in the mean-field setting.

Interactions between spatial positions are encoded by a `GlobalKernel X`. This is a function $K(x, x')$ that specifies how strongly position $x'$ influences position $x$. The kernel is nonneg, integrable, and normalized so that $\int K(x, x') \, dx' = 1$. The nonlocal alignment operator applies the kernel to the polarization field:

$$\int K(x, x') \left[ p(x') - p(x) \right] dx'$$

This integral averages the difference between the local polarization and the polarization at every other point, weighted by the kernel. It is the continuum generalization of the coupling terms in lattice models.

## Exact Projection

The key result in the ContinuumField module is that the global kernel operator can be rewritten in local displacement coordinates without loss. Define the local kernel field at position $x$ by shifting to displacement coordinates:

$$K_x(\xi) := K(x, x + \xi)$$

Then the nonlocal operator becomes:

$$\int K_x(\xi) \left[ p(x + \xi) - p(x) \right] d\xi$$

The theorem `nonlocal_exact` proves that these two forms are equal by `rfl`. This is not an approximation. The global and local operators are definitionally the same computation expressed in different coordinates. The function `projectKernelAt` extracts the local kernel field for each spatial position.

## Spatial + Temporal Bridges

Distributing a continuum computation requires assigning spatial regions to protocol roles. A `RoleLoc` map sends each role to a position in the continuous space. The `Colocated` predicate identifies roles at the same location, and `Within` checks that two roles are within a distance bound.

The temporal bridge connects discrete protocol steps to continuous time. A `SamplingSchedule` maps step indices to real-valued times. Sampling depends only on the sampler's own step counter or a globally agreed schedule, never on a remote party's local clock. The predicate `ClockIndependent` formalizes this constraint, and `mkSampler_clockIndependent` proves that schedule-based sampling satisfies it.

## Coherence

When the global kernel is distributed across roles, each role receives a local kernel field. The `KernelCoherent` predicate asserts that every role's local kernel matches what you get by projecting the global kernel to that role's location. The theorem `projection_sound` closes the loop: when coherence holds, evaluating the local kernel at a role's position reproduces the global operator exactly. This is the ContinuumField analogue of well-formedness in the session layer.

## Adaptivity and Closure

Kernels can evolve with the field state. A `KernelDependence` structure specifies how the kernel depends on the current fields, with a Lipschitz bound ensuring regularity. A `KernelDynamics` structure adds a continuous-time drift for the kernel itself.

For analysis, the full kernel can be compressed into a `KernelSummary` that records effective range, anisotropy, and total mass. A `ClosureSpec` packages the compression and reconstruction with a uniform approximation bound. This is the continuum analogue of mean-field truncation: you track only the leading moments of the coupling function, with explicit control over the error introduced.
