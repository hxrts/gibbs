# Gibbs

Gibbs is a statistical mechanics formalization in Lean 4. It develops three layers of physical theory: Hamiltonian mechanics in finite-dimensional phase space, mean-field population dynamics on the probability simplex, and continuum field theory with nonlocal integral kernels. The Hamiltonian layer formalizes convex energy functions, damped flows, Legendre duality, and Lyapunov stability. The mean-field layer constructs drift functions from stoichiometric rules and proves ODE existence on the simplex via Picard-Lindelöf. The continuum field layer lifts these dynamics to spatially extended systems where interactions are mediated by global integral kernels.

The three layers form a stack. Hamiltonian mechanics provides the dynamical semantics: energy, stability, and equilibrium. Mean-field gives the population-level view: many agents choosing among finitely many states with no spatial structure. Continuum field adds space, replacing uniform all-to-all coupling with a kernel that weights interactions by distance and direction.

The project employs a structural analogy between multiparty session type (MPST) projection and physical coarse-graining as dual approaches to modeling concurrency. Both perform erasure at the extensional level, mapping global specifications to local views. Each physical layer exhibits the same pattern: mean-field abstraction forgets individual identity, Hamiltonian choreography partitions phase-space coordinates among roles, and continuum field projection decomposes nonlocal kernels into local views.

## Setup

```bash
direnv allow   # loads nix environment
just build     # builds lean library
```
