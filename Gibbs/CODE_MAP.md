# Gibbs — Code Map

## Module Dependency Tree

```
Gibbs/Core.lean
│
├── Hamiltonian/Basic.lean
│   ├── Hamiltonian/ConvexHamiltonian.lean
│   │   ├── Hamiltonian/DampedFlow.lean
│   │   │   ├── Hamiltonian/Choreography.lean
│   │   │   ├── Hamiltonian/SymplecticFlow.lean
│   │   │   ├── Hamiltonian/Examples/HarmonicOscillator.lean
│   │   │   └── Hamiltonian/Examples/Langevin.lean
│   │   ├── Hamiltonian/GeneralHamiltonian.lean
│   │   ├── Hamiltonian/Legendre.lean
│   │   │   └── Hamiltonian/FenchelMoreau.lean
│   │   ├── Hamiltonian/NoseHoover.lean
│   │   │   └── Hamiltonian/Examples/ThermostatOscillator.lean
│   │   ├── Hamiltonian/Examples/GradientDescent.lean
│   │   │   ├── Hamiltonian/Examples/GradientDescentMinimizer.lean
│   │   │   └── Hamiltonian/Examples/HeavyBallConvergence.lean
│   │   └── Hamiltonian/Examples/LatticeMaxwell.lean
│   ├── Hamiltonian/Ergodic.lean
│   │   └── Hamiltonian/GaussianIntegrals.lean
│   ├── Hamiltonian/Stability.lean
│   └── Hamiltonian/Stochastic/
│       ├── Hamiltonian/Stochastic/Basic.lean
│       └── Hamiltonian/Stochastic/LangevinFokkerPlanck.lean
│
├── ContinuumField/Basic.lean
│   ├── ContinuumField/Kernel.lean
│   │   ├── ContinuumField/Adaptivity.lean
│   │   ├── ContinuumField/Closure.lean
│   │   ├── ContinuumField/Projection.lean
│   │   ├── ContinuumField/EffectsIntegration.lean
│   │   └── ContinuumField/Examples/Anisotropic2D.lean
│   └── ContinuumField/TimeBridge.lean
│       └── ContinuumField/SpatialBridge.lean
│           └── ContinuumField/SpatialMirror.lean
│
└── MeanField/Basic.lean
    └── MeanField/Choreography.lean
        ├── MeanField/Rules.lean
        │   └── MeanField/Projection.lean
        ├── MeanField/LipschitzBridge.lean
        │   ├── MeanField/ODE.lean
        │   │   ├── MeanField/Existence.lean
        │   │   └── MeanField/Stability.lean
        │   └── MeanField/Examples/Ising/…
        └── MeanField/Projection.lean
```

Facade modules: `Gibbs/Hamiltonian.lean`, `Gibbs/MeanField.lean`, `Gibbs/ContinuumField.lean`.
Stochastic facade: `Gibbs/Hamiltonian/Stochastic.lean` (re-exports `Basic` + `LangevinFokkerPlanck`).

---

## Proof Completeness

**No `sorry` anywhere in the codebase.**
All previously noted placeholder stubs have been replaced with concrete definitions.

---

## Per-File Detail

### `Core.lean`

Foundational type aliases and structures for session typing. Defines the vocabulary shared across all layers: session identifiers, roles, labels, endpoints, and communication edges.

| Kind | Name | Notes |
|------|------|-------|
| def | `SessionId`, `Role`, `Label` | Type aliases (Nat, String) |
| structure | `Endpoint`, `Edge` | Session endpoints and edges |
| def | `Edge.senderEp`, `Edge.receiverEp`, `Endpoint.edgeTo` | Projections |

All proofs: `rfl`.

---

### Hamiltonian Layer

The Hamiltonian layer formalizes classical and statistical mechanics in finite-dimensional phase space. It provides the physical semantics that the session-type choreography projects into: energy conservation, dissipation, stability, and thermodynamic equilibrium.

#### `Hamiltonian/Basic.lean`

Defines the phase space on which all Hamiltonian dynamics takes place. Configuration space is a finite-dimensional Euclidean space; a phase point bundles position and momentum.

| Kind | Name | Notes |
|------|------|-------|
| def | `Config n`, `PhasePoint n` | `EuclideanSpace ℝ (Fin n)` and pairs |
| def | `PhasePoint.q`, `.p`, `.mk`, `.fromPosition`, `.zero` | Projections and constructors |
| theorem | `fromPosition_isAtRest` | `simp` |
| theorem | `kineticNormSq_nonneg` | `simp` |
| theorem | `kineticNormSq_eq_zero_iff` | `simp` |
| theorem | `dist_eq_max` | `simp` |

#### `Hamiltonian/ConvexHamiltonian.lean`

Defines Hamiltonians with separable, convex kinetic and potential energy. Convexity is the central structural assumption: it guarantees energy has a well-defined minimum and enables all downstream stability and duality results.

| Kind | Name | Notes |
|------|------|-------|
| structure | `ConvexHamiltonian n` | Separable H = T(p) + V(q) |
| structure | `StrictlyConvexHamiltonian` | Adds strict convexity of V |
| def | `energy`, `velocity`, `force` | H(q,p), ∇T, −∇V |
| def | `quadraticKinetic`, `quadraticPotential` | ½‖·‖² instances |
| def | `harmonicOscillator`, `harmonicOscillatorStrict` | Canonical example |
| theorem | `quadraticKinetic_convex` | `smul` on norm-sq convexity |
| theorem | `quadraticKinetic_grad` | `ext_inner_right`, `fderiv_norm_sq_apply`, `simp` |
| theorem | `quadraticPotential_strictConvex` | `refine`, `nlinarith`. Requires `[NeZero n]` |
| theorem | `energy_nonneg` | `positivity` |
| theorem | `energy_eq_zero_iff` | `linarith` |

**Assumptions on `ConvexHamiltonian`:**
- `T_convex : ConvexOn ℝ Set.univ T` — kinetic energy is convex everywhere
- `V_convex : ConvexOn ℝ Set.univ V` — potential energy is convex everywhere
- `T_diff : Differentiable ℝ T` — kinetic energy is differentiable
- `V_diff : Differentiable ℝ V` — potential energy is differentiable

**Additional on `StrictlyConvexHamiltonian`:**
- `V_strictConvex : StrictConvexOn ℝ Set.univ V` — potential is strictly convex (unique minimum)

**Strategy**: inner-product identities, `positivity`, `nlinarith`.

#### `Hamiltonian/GeneralHamiltonian.lean`

Extends the Hamiltonian framework to non-separable, potentially non-convex Hamiltonians H(q,p). Provides gradients in both components and the canonical symplectic drift, plus a coercion from the separable convex case.

| Kind | Name | Notes |
|------|------|-------|
| structure | `GeneralHamiltonian n` | H : PhasePoint n → ℝ with partial differentiability |
| def | `GeneralHamiltonian.grad_q`, `.grad_p` | Partial gradients |
| def | `GeneralHamiltonian.drift` | Symplectic drift (∇_p H, −∇_q H) |
| def | `ConvexHamiltonian.toGeneral` | Coercion from separable convex to general |

**Assumptions on `GeneralHamiltonian`:**
- `diff_q : ∀ p, Differentiable ℝ (fun q => H (q, p))` — differentiable in position
- `diff_p : ∀ q, Differentiable ℝ (fun p => H (q, p))` — differentiable in momentum

#### `Hamiltonian/DampedFlow.lean`

Adds linear friction to Hamiltonian dynamics. The damped drift ṗ = −∇V − γp dissipates energy at rate −γ‖p‖², which is the engine behind all stability results. Lipschitz regularity of the drift is established for ODE well-posedness.

| Kind | Name | Notes |
|------|------|-------|
| structure | `Damping` | γ > 0 |
| def | `dampedDrift` | q̇ = ∇T, ṗ = −∇V − γp |
| theorem | `energy_dissipation` | dH/dt = −γ‖p‖² |
| theorem | `energy_decreasing` | Monotonicity via `antitone_of_hasDerivAt_nonpos` |
| theorem | `dampedDrift_lipschitz` | Lipschitz on bounded sets |
| theorem | `dampedDrift_hasLipschitz` | Explicit Lipschitz constant |

**Key theorem hypotheses:**
- `energy_dissipation` assumes `∀ p, gradient H.T p = p` (quadratic kinetic energy)
- `energy_decreasing` takes a derivative certificate as hypothesis
- `dampedDrift_lipschitz` assumes `LipschitzWith K_T (gradient H.T)` and `LipschitzWith K_V (gradient H.V)`

**Strategy**: Lipschitz composition, `mul_le_mul_of_nonneg`.

#### `Hamiltonian/SymplecticFlow.lean`

Undamped (symplectic) Hamiltonian dynamics: q̇ = ∇_p T, ṗ = −∇_q V with no friction term. Energy is exactly conserved. Provides the conservative baseline against which damped and thermostatted flows are compared.

| Kind | Name | Notes |
|------|------|-------|
| def | `symplecticDrift` | Undamped Hamiltonian drift |
| theorem | `symplectic_energy_conserved` | dH/dt = 0 along symplectic drift |
| theorem | `harmonicOscillator_symplectic_energy` | Specialization to harmonic oscillator |

**Strategy**: inner-product cancellation, `ring`.

#### `Hamiltonian/Legendre.lean`

Develops the Legendre transform and Bregman divergence. The Bregman divergence D_f(x,y) measures "how far x is from y according to f" and serves as a Lyapunov function for convergence proofs.

| Kind | Name | Notes |
|------|------|-------|
| def | `legendre` | Convex conjugate f*(p) = sup_x ⟨p,x⟩ − f(x) |
| def | `bregman` | D_f(x,y) = f(x) − f(y) − ⟨∇f(y), x−y⟩ |
| theorem | `bregman_nonneg` | Convexity → D_f ≥ 0 |
| theorem | `bregman_eq_zero_iff` | Strict convexity → D_f = 0 ↔ x = y |
| theorem | `bregman_quadratic` | For f = ½‖·‖²: D_f = ½‖x−y‖² |
| def | `bregman_lyapunov_data` | Packages Bregman divergence as Lyapunov data |

**Key theorem hypotheses:**
- `bregman_nonneg` requires `ConvexOn ℝ Set.univ f` and `Differentiable ℝ f`
- `bregman_eq_zero_iff` requires `StrictConvexOn ℝ Set.univ f` and `Differentiable ℝ f`

**Strategy**: calculus on line maps (`lineMap_comp_convex`), slope inequalities, `ring`.

#### `Hamiltonian/FenchelMoreau.lean`

Proves the Fenchel–Moreau theorem: a lower-semicontinuous convex function equals its double conjugate (f = f**). Uses geometric Hahn–Banach separation to construct supporting hyperplanes at every point of the epigraph.

| Kind | Name | Notes |
|------|------|-------|
| theorem | `fenchel_young` | ⟨p,x⟩ ≤ f(x) + f*(p) |
| theorem | `biconjugate_le` | f** ≤ f |
| theorem | `le_biconjugate_of_subgradient` | Subgradient everywhere → f ≤ f** |
| theorem | `epigraph_convex` | Convex function → convex epigraph |
| theorem | `epigraph_closed` | lsc function → closed epigraph |
| def | `separation_data` | Hyperplane separating point from closed convex set |
| theorem | `supporting_affine` | Supporting hyperplane at boundary of epigraph |
| theorem | `fenchel_moreau` | **f = f\*\*** for lsc convex f |

**Key predicates:**
- `HasFiniteConjugate f` — conjugate is finite everywhere
- `HasFiniteBiconjugate f` — biconjugate is finite
- `IsSubgradientAt f x p` — p is a subgradient of f at x
- `SubgradientExists f` — every point admits a subgradient

**Theorem hypotheses for `fenchel_moreau`:**
- `ConvexOn ℝ Set.univ f`, `LowerSemicontinuous f`, `HasFiniteConjugate f`, `HasFiniteBiconjugate f`

**Strategy**: `ciSup_le` / `le_ciSup`, geometric Hahn–Banach (`geometric_hahn_banach_point_closed`), rescaling.

#### `Hamiltonian/NoseHoover.lean`

Implements the Nosé–Hoover thermostat, which extends Hamiltonian dynamics with a feedback variable ξ that injects or removes energy to drive the system toward a target temperature. Includes ergodicity scaffolding connecting to the Gibbs measure.

| Kind | Name | Notes |
|------|------|-------|
| structure | `ThermostatParams` | Q, kT > 0 |
| def | `ThermostatPoint n` | (q, p, ξ) triple |
| def | `noseHooverDrift` | q̇ = ∇T, ṗ = −∇V − ξp, ξ̇ = (‖p‖² − n·kT)/Q |
| theorem | `subsystem_energy_rate` | dH/dt = −ξ‖p‖² |
| theorem | `energy_injection_iff` | Energy injected ↔ ξ < 0 |
| theorem | `thermostat_cools_when_cold` | ξ̇ < 0 when ‖p‖² < n·kT |
| theorem | `extended_energy_conserved` | Extended Hamiltonian is constant of motion |
| theorem | `equipartition_target` | ξ̇ = 0 at ‖p‖² = n·kT |
| def | `noseHooverInvariantMeasure` | Gibbs-style measure on extended phase space |
| def | `IsMeasurePreserving` | Flow preserves a measure |
| theorem | `noseHoover_ergodic` | Ergodicity wrapper consuming `IsErgodic` hypothesis |

**Key theorem hypotheses:**
- `subsystem_energy_rate` assumes `∀ p, gradient H.T p = p` (quadratic kinetic energy)
- `energy_injection_iff` additionally requires `x.p ≠ 0`
- `extended_energy_conserved` takes a derivative certificate as hypothesis

**Strategy**: `nlinarith` for thermodynamic inequalities.

#### `Hamiltonian/Ergodic.lean`

Defines the Gibbs/Boltzmann ensemble and the ergodic hypothesis. The partition function normalizes the Boltzmann weight exp(−V/kT) into a probability density; ergodicity asserts that time averages along trajectories converge to ensemble averages against this density.

| Kind | Name | Notes |
|------|------|-------|
| def | `partitionFunction`, `gibbsDensity`, `gibbsMeasure` | Boltzmann statistics |
| def | `timeAverage`, `ensembleAverage` | Ergodic observables |
| def | `IsErgodic` | Time average = ensemble average |
| theorem | `measurable_gibbsDensity`, `aemeasurable_gibbsDensity` | Measurability closure |
| theorem | `integrable_gibbsDensity` | Integrable under integrable weight |
| theorem | `gibbsDensity_nonneg` | `div_nonneg`, `exp_nonneg` |
| theorem | `gibbsDensity_integral_eq_one` | `div_self` |
| theorem | `partitionFunction_pos` | `integral_exp_pos` |
| theorem | `gibbsMeasure_isProbability_of_integrable_nonzero` | Probability measure |
| theorem | `ensembleAverage_eq_integral_gibbsMeasure` | `withDensity` integral |
| theorem | `timeAverage_const` | `simp` |
| theorem | `ensembleAverage_const_eq` | `simp` |
| theorem | `timeAverage_const_traj` | Time average along constant trajectory = f(q₀) |
| theorem | `ergodic_of_constant_process` | Constant trajectory is ergodic at matching point |

**Key theorem hypotheses:**
- `gibbsDensity_integral_eq_one` requires `partitionFunction V kT μ ≠ 0`
- `partitionFunction_pos` requires `[NeZero μ]` and integrability of Boltzmann weight
- `timeAverage_const_traj` requires `0 < T`
- `IsErgodic` requires `Continuous f`, `Integrable f μ` for each observable

**Strategy**: `integral_nonneg`, `integral_exp_pos`, `div_self`, `withDensity` integral identities.

#### `Hamiltonian/GaussianIntegrals.lean`

Gaussian integral identities over configuration space, used for equipartition-style calculations in the ergodic layer.

| Kind | Name | Notes |
|------|------|-------|
| theorem | `integral_gaussian_pi` | Gaussian integral over `Fin n → ℝ` (product form) |
| theorem | `integral_gaussian_config` | Gaussian integral over `Config n` (norm-based form) |

**Strategy**: product measure decomposition, one-dimensional Gaussian integral.

#### `Hamiltonian/Stability.lean`

Defines Lyapunov stability theory for Hamiltonian systems. A Lyapunov function V is a nonneg function that is zero at the equilibrium, positive elsewhere, and decreasing along trajectories. Strict Lyapunov gives asymptotic stability.

| Kind | Name | Notes |
|------|------|-------|
| structure | `LyapunovData` | V ≥ 0, V(x*)=0, V>0 elsewhere, V decreasing |
| structure | `StrictLyapunovData` | Adds V → 0 along trajectories |
| def | `IsAsymptoticallyStable`, `ExponentialEnergyDecay` | Stability predicates |
| theorem | `exponential_convergence` | Energy decay → dist convergence |
| def | `energyLyapunov` | Constructs Lyapunov data from energy |
| theorem | `damped_asymptotically_stable` | Strict Lyapunov → asymptotic stability |

**Key theorem hypotheses:**
- `exponential_convergence` requires `0 ≤ c`, `∀ x, ‖x − x_eq‖² ≤ c * H.energy x`, and `ExponentialEnergyDecay`
- `energyLyapunov` requires energy continuity, positivity, vanishing at equilibrium, and a derivative certificate

#### `Hamiltonian/Choreography.lean`

Bridges Hamiltonian mechanics with session-type choreography by partitioning phase-space coordinates among roles.

| Kind | Name | Notes |
|------|------|-------|
| structure | `HamiltonianChoreography` | Hamiltonian + damping + role partition |
| theorem | `roles_disjoint` | Different roles → disjoint coordinate sets |
| theorem | `projectConfig_disjoint` | Projection zeroes non-owned coordinates |
| inductive | `PhaseMessage` | position, momentum, force, coupled |

**Assumptions on `HamiltonianChoreography n`:**
- `roles_partition : ∀ i, ∃! r, i ∈ roles r` — every coordinate is owned by exactly one role

#### `Hamiltonian/Stochastic/Basic.lean`

Minimal stochastic scaffolding with constant-diffusion Itô integral. Provides a Brownian motion interface, SDE structure, and solution predicate using Mathlib's Bochner integral for the pathwise additive-noise case.

| Kind | Name | Notes |
|------|------|-------|
| abbrev | `StochasticProcess n` | `ℝ → Ω → PhasePoint n` |
| structure | `BrownianMotion n` | path : ℝ → Ω → Config n, starts at origin |
| structure | `SDE n` | drift + constant diffusion map |
| def | `stochasticIntegral` | ∫₀ᵗ A dW = A(W_t − W_0) for constant A |
| def | `SolvesSDE` | Integral solution predicate |
| structure | `SDEProcess n` | Bundles SDE + Brownian + path + solves proof |

**Limitations:**
- Constant (state-independent) diffusion only
- No general Itô/Stratonovich calculus

#### `Hamiltonian/Stochastic/LangevinFokkerPlanck.lean`

Full Langevin dynamics with Fokker–Planck equation and proof that the Gibbs density is stationary under the fluctuation–dissipation relation σ² = 2γkT.

| Kind | Name | Notes |
|------|------|-------|
| structure | `LangevinParams n` | V, γ, kT with positivity and differentiability |
| def | `LangevinParams.σ` | Noise strength √(2γkT) |
| theorem | `LangevinParams.σ_sq` | σ² = 2γkT |
| structure | `BrownianIncrement n` | ΔW vector with time step |
| class | `BrownianEffect n M` | Abstract effect providing Brownian increments |
| def | `langevinStep` | One Euler–Maruyama step |
| def | `Density n` | Time-dependent density ℝ → PhasePoint n → ℝ |
| def | `FokkerPlanckRHS` | Fokker–Planck operator for Langevin dynamics |
| def | `SatisfiesFokkerPlanck` | Density satisfies FP equation |
| def | `gibbsDensity` | ρ(q,p) ∝ exp(−(½‖p‖² + V(q))/kT) |
| def | `gibbsStationary` | Gibbs as time-independent density |
| theorem | `gibbs_is_stationary` | **Gibbs density is FP-stationary** |

**Strategy**: substitution of Gibbs density into FP operator, cancellation via `σ² = 2γkT`.

#### Examples

| File | Description |
|------|-------------|
| `HarmonicOscillator.lean` | Damped harmonic oscillator. Instantiates DampedFlow for the quadratic Hamiltonian; proves energy dissipation and decrease. |
| `Langevin.lean` | Connects Langevin dynamics to Nosé–Hoover. Proves simplex projection preserves zero-sum, Nosé–Hoover at ξ=γ matches damped dynamics, and both target Gibbs equilibrium. Constructs `langevinProcess` via stochastic core. |
| `ThermostatOscillator.lean` | Nosé–Hoover applied to oscillator. Proves equipartition at equilibrium, bounded orbits, and perpetual oscillation. |
| `GradientDescent.lean` | Heavy-ball optimization as Hamiltonian mechanics. When p = −∇V(q), configuration trajectory reduces to gradient flow. |
| `GradientDescentMinimizer.lean` | Existence and uniqueness of minimizers for strongly convex objectives. Proves coercivity, compactness on closed ball, and uniqueness via strict convexity. Provides `minimizer` and `minimizer_spec`. |
| `HeavyBallConvergence.lean` | Lyapunov analysis for heavy-ball/momentum dynamics. Proves derivative formula, strong convexity + Young bounds, and exponential decay of modified energy via `heavyBallLyapunov_decay`. |
| `LatticeMaxwell.lean` | Maxwell's equations on a discrete 3D lattice with Yee-style stencils. Implements `curlE`/`curlB`, ghost edges/faces, and local/global coherence. Proves energy nonnegativity and zero-field minimizer. |

---

### MeanField Layer

The mean-field layer formalizes population dynamics over a finite set of local states. The central result is ODE existence/uniqueness on the probability simplex via Picard–Lindelöf, with Lyapunov stability theory for equilibrium analysis.

#### `MeanField/Basic.lean`

Defines the probability simplex and population states.

| Kind | Name | Notes |
|------|------|-------|
| structure | `PopulationState Q` | Counts with total > 0 |
| def | `empirical` | Normalized counts → ℝ |
| def | `Simplex Q` | {x | x ≥ 0, ∑ x = 1} |
| theorem | `empirical_nonneg`, `empirical_sum_one` | `div_nonneg`, `div_self` |
| theorem | `Simplex.empirical_mem` | Empirical measure ∈ Simplex |
| inductive | `TwoState` | up/down with Fintype |
| theorem | `magnetizationOf_bounded` | |m| ≤ 1 |

**Typeclass context:** `[Fintype Q]` throughout.

#### `MeanField/Choreography.lean`

Defines the choreographic specification for mean-field dynamics: a drift function on the simplex that is Lipschitz, conserves total probability, and points inward at boundaries.

| Kind | Name | Notes |
|------|------|-------|
| def | `RateFunction Q` | (Q → ℝ) → ℝ with NonNeg, IsLipschitz, IsBounded |
| def | `DriftFunction Q` | (Q → ℝ) → (Q → ℝ) with Conserves, IsLipschitz |
| structure | `MeanFieldChoreography` | Drift + Lipschitz + conservation + boundary |
| def | `IsEquilibrium` | F(x) = 0 and x ∈ Simplex |
| def | `IsStable`, `IsAsymptoticallyStable` | ODE-style stability definitions |

**Assumptions on `MeanFieldChoreography Q`:**
- `drift_lipschitz` — drift is Lipschitz on the simplex
- `drift_conserves` — `∀ x ∈ Simplex Q, ∑ q, drift x q = 0`
- `boundary_nonneg` — drift points inward at simplex boundary

#### `MeanField/Rules.lean`

Builds drift functions compositionally from lists of population rules. Conservation and boundary invariance are proved by induction over the rule list.

| Kind | Name | Notes |
|------|------|-------|
| structure | `PopRule Q` | Stoichiometric update + rate function |
| structure | `BinaryRule`, `UnaryRule` | Two-agent and one-agent specializations |
| def | `driftFromRules` | Aggregates rules into drift |
| theorem | `BinaryRule.toPopRule_conserves` | ∑ update = 0 |
| theorem | `driftFromRules_conserves` | Aggregate conserves mass |
| theorem | `driftFromRules_boundary_nonneg` | Simplex forward-invariance |
| def | `MeanFieldChoreography.fromRules` | Constructs choreography from rule list |

**Strategy**: induction on `List`, Finset summation swaps, `by_cases` on state equality.

#### `MeanField/LipschitzBridge.lean`

Technical bridge between the project's Lipschitz predicate (defined on the simplex) and Mathlib's `LipschitzWith` typeclass. Extends the drift from the simplex to all of ℝ^Q while preserving the Lipschitz constant.

| Kind | Name | Notes |
|------|------|-------|
| def | `DriftFunction.toLipschitzOnWith` | Predicate → Mathlib LipschitzOnWith |
| def | `DriftFunction.extend` | Extends drift from simplex to ℝ^Q |
| theorem | `extend_lipschitz` | Extension preserves Lipschitz constant |
| def | `toTimeDep` | Wraps autonomous drift as time-dependent |

**Strategy**: `ENNReal` arithmetic, `Classical.choose_spec`.

#### `MeanField/ODE.lean`

ODE existence, uniqueness, and simplex invariance for mean-field dynamics. Uses Picard–Lindelöf for local existence and Gronwall's inequality for uniqueness.

| Kind | Name | Notes |
|------|------|-------|
| def | `IsSolution` | Derivative condition for ODE trajectory |
| theorem | `ode_exists` | Local existence via Picard–Lindelöf |
| theorem | `ode_unique` | Uniqueness via Gronwall |
| theorem | `simplex_invariant` | Solution stays in simplex |
| theorem | `fixed_point_is_constant` | Equilibrium → constant trajectory |
| def | `Jacobian`, `IsHurwitz`, `IsLinearlyStable` | Linearized stability apparatus |
| structure | `LyapunovData`, `StrictLyapunovData` | ODE-level Lyapunov structures |

**Key theorem hypotheses:**
- `ode_exists` requires `[Nonempty Q]`, `x₀ ∈ Simplex Q`, conservation and boundary on extension
- `ode_unique` requires two solutions sharing initial condition; Gronwall from `LipschitzWith K`

**Definition:**
- `IsHurwitz F x` — all eigenvalues of `Jacobian F x` have negative real part

#### `MeanField/Existence.lean`

Carries out the Picard–Lindelöf construction and proves simplex forward-invariance by a Gronwall-type argument.

| Kind | Name | Notes |
|------|------|-------|
| theorem | `local_ode_exists` | Picard–Lindelöf on bounded ball |
| theorem | `global_ode_exists` | Extended to simplex via boundedness |
| theorem | `simplex_forward_invariant` | Nonneg + sum-one preserved |
| def | `MeanFieldChoreography.solution` | Canonical solution via `Classical.choose` |

**Strategy**: `Metric.isBounded_iff`, `closedBall`, `IsPicardLindelof`.

#### `MeanField/Stability.lean`

Lyapunov stability theory for the mean-field ODE. The linearized pathway goes through the Hurwitz spectral condition.

| Kind | Name | Notes |
|------|------|-------|
| theorem | `lyapunov_implies_stable` | Lyapunov function → stability |
| theorem | `strict_lyapunov_implies_asymptotic` | Strict → asymptotic stability |
| theorem | `hurwitz_implies_lyapunov_exists` | Hurwitz spectrum → Lyapunov exists |
| theorem | `linear_stable_implies_asymptotic` | Main linearized stability result |

**Strategy**: compactness of sphere, continuity, spectral condition.

#### `MeanField/Projection.lean`

Addresses the inverse problem: given a target drift, find nonneg rate functions for stoichiometric templates that reproduce it.

| Kind | Name | Notes |
|------|------|-------|
| structure | `ProjectionProblem` | Target drift + rule templates |
| structure | `ProjectionSolution` | Rates producing the target drift |
| theorem | `projection_correct` | Solution reproduces target |
| theorem | `projection_exists` | Existence under conic decomposition |

#### `MeanField/Examples/Ising/`

Four files implementing the mean-field Ising model. `TanhAnalysis.lean` analyzes m = tanh(βm). `Drift.lean` defines drift and proves conservation. `Glauber.lean` builds Glauber spin-flip dynamics. `PhaseTransition.lean` characterizes the phase transition at β = 1.

---

### ContinuumField Layer

The continuum field layer lifts the discrete mean-field framework to spatially extended systems. Interactions are mediated by nonlocal integral kernels. The key structural result is that global and local views of the kernel operator are definitionally equal.

#### `ContinuumField/Basic.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `Field X V` | X → V |
| structure | `FieldState X V W` | (ρ, p, ω) triple |

#### `ContinuumField/Kernel.lean`

Defines the global interaction kernel with regularity and normalization conditions.

| Kind | Name | Notes |
|------|------|-------|
| def | `KernelField X` | X → ℝ |
| structure | `GlobalKernel X` | K with measurability, nonnegativity, mass normalization |
| def | `GlobalKernel.localKernel` | K(x,x') → K_x(ξ) = K(x, x+ξ) |
| structure | `KernelRule` | Deterministic kernel update from field state |

**Assumptions on `GlobalKernel X`:**
- `measurable_K`, `nonneg`, `mass_one`, `integrable_K`

#### `ContinuumField/Projection.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `nonlocalGlobal` | ∫ K(x,x') (p(x')−p(x)) dx' |
| def | `nonlocalLocal` | ∫ K_x(ξ) (p(x+ξ)−p(x)) dξ |
| theorem | `nonlocal_exact` | Global = local operator. **Proof: `rfl`** |

#### `ContinuumField/EffectsIntegration.lean`

Connects the continuum kernel to the effects/session-type framework. Each role is assigned a spatial location; coherent locals reproduce the global operator.

| Kind | Name | Notes |
|------|------|-------|
| def | `RoleLoc`, `KernelDecl`, `LocalKernelEnv` | Per-role kernel attachment |
| def | `KernelCoherent` | Local kernels = projection of global |
| theorem | `projection_sound` | Coherent locals reproduce global operator |

#### `ContinuumField/Closure.lean`

| Kind | Name | Notes |
|------|------|-------|
| structure | `KernelSummary` | Range, anisotropy, mass |
| structure | `ClosureSpec` | close/reconstruct with approximation bound |

#### `ContinuumField/Adaptivity.lean`

Specifies Lipschitz dependence of the kernel on the field state.

| Kind | Name | Notes |
|------|------|-------|
| structure | `KernelDependence` | Kernel as Lipschitz function of field state |
| structure | `KernelDynamics` | Drift for kernel evolution |

#### `ContinuumField/TimeBridge.lean`

Bridges continuous time and discrete steps. Proves constructed samplers are clock-independent.

| Kind | Name | Notes |
|------|------|-------|
| structure | `SamplingSchedule` | sampleTime : ℕ → ℝ |
| def | `ClockIndependent` | Sampler ignores remote clock |
| theorem | `mkSampler_clockIndependent` | `rfl` |
| structure | `SpatialBridge` | Role locations + topology + soundness |
| theorem | `satisfies_colocated`, `satisfies_within` | Unpack bridge soundness |

#### `ContinuumField/SpatialBridge.lean`

Adapter from the Effects spatial mirror to the continuum SpatialBridge.

| Kind | Name | Notes |
|------|------|-------|
| def | `AlignedRoleLoc` | Role locations respect site assignment |
| def | `effectsSpatialBridge` | Constructs SpatialBridge from Effects types |

#### `ContinuumField/SpatialMirror.lean`

Self-contained mirror of the Effects system's spatial types (`Site`, `RoleName`, `SpatialReq`, `Topology`, `Satisfies`). Includes helpers: `isTop`, `isBot`, `atoms`, `fromList`, `satisfiesBool`, `satisfiesBool_iff_Satisfies`.

#### `ContinuumField/Examples/Anisotropic2D.lean`

2D anisotropic kernel with direction weighting (vision cone). Demonstrates projection exactness and closure soundness.

| Kind | Name | Notes |
|------|------|-------|
| def | `anisotropicLocal` | 2D anisotropic kernel |
| theorem | `example_exact` | `simpa using nonlocal_exact` |
| theorem | `example_closure_bound` | `simpa using C.sound` |

---

## Proof Strategy Index

| Strategy | Where used | What it proves |
|----------|-----------|----------------|
| `rfl` / definitional equality | Projection, TimeBridge, LatticeMaxwell | Operator exactness, coherence, domain decomposition |
| `simp` | Everywhere | Unfolding definitions, arithmetic simplification |
| `linarith` / `nlinarith` | ConvexHamiltonian, DampedFlow, NoseHoover, Stability | Inequalities from convexity, energy bounds, thermodynamics |
| `positivity` | ConvexHamiltonian, ThermostatOscillator | Nonnegativity of energy, norms |
| `ring` | Legendre, Langevin, Basic, SymplecticFlow | Algebraic identities |
| Lipschitz composition | DampedFlow, LipschitzBridge | Drift regularity for ODE existence |
| `ext_inner_right` + `fderiv_norm_sq_apply` | ConvexHamiltonian, Legendre | Gradient of ½‖·‖² |
| `ciSup_le` / `le_ciSup` | FenchelMoreau | Fenchel–Young, biconjugate bounds |
| Geometric Hahn–Banach | FenchelMoreau | Separation, supporting hyperplanes, Fenchel–Moreau |
| Picard–Lindelöf + Gronwall | Existence, ODE | ODE existence and uniqueness |
| Induction on `List` | Rules | Conservation and boundary invariance for aggregated rules |
| `by_cases` on state equality | Rules | Boundary nonnegativity (mass-action at zero) |
| `antitone_of_hasDerivAt_nonpos` | DampedFlow | Energy monotone decrease |
| Calculus on `lineMap` | Legendre | Bregman nonnegativity via convexity of restrictions to lines |
| Spectral / Hurwitz condition | Stability | Linearized asymptotic stability |
| Young's inequality + strong convexity | HeavyBallConvergence | Lyapunov derivative bounds, exponential decay |
| Gaussian integral decomposition | GaussianIntegrals | Product-measure Gaussian identities over Config |
| Compactness + coercivity | GradientDescentMinimizer | Minimizer existence for strongly convex functions |
| FP substitution + fluctuation-dissipation | LangevinFokkerPlanck | Gibbs stationarity under σ² = 2γkT |
