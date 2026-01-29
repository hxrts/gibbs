# Gibbs — Code Map

## Module Dependency Tree

```
Gibbs/Basic.lean
│
├── Hamiltonian/Basic.lean
│   ├── Hamiltonian/ConvexHamiltonian.lean
│   │   ├── Hamiltonian/DampedFlow.lean
│   │   │   ├── Hamiltonian/Choreography.lean
│   │   │   ├── Hamiltonian/Examples/HarmonicOscillator.lean
│   │   │   └── Hamiltonian/Examples/Langevin.lean
│   │   ├── Hamiltonian/Legendre.lean
│   │   │   └── Hamiltonian/FenchelMoreau.lean
│   │   ├── Hamiltonian/NoseHoover.lean
│   │   │   └── Hamiltonian/Examples/ThermostatOscillator.lean
│   │   ├── Hamiltonian/Examples/GradientDescent.lean
│   │   └── Hamiltonian/Examples/LatticeMaxwell.lean
│   ├── Hamiltonian/Ergodic.lean
│   └── Hamiltonian/Stability.lean
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

---

## Proof Completeness

**No `sorry` anywhere in the codebase.**
All previously noted placeholder stubs have been replaced with concrete definitions.

---

## Per-File Detail

### `Basic.lean`

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
| theorem | `quadraticPotential_strictConvex` | `refine`, `nlinarith` on norm identity. Requires `[NeZero n]` |
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

**Assumptions on `Damping`:**
- `γ_pos : 0 < γ` — damping coefficient is strictly positive

**Key theorem hypotheses:**
- `energy_dissipation` assumes `∀ p, gradient H.T p = p` (i.e. T is quadratic kinetic energy ½‖p‖²)
- `energy_decreasing` takes a derivative certificate as hypothesis: the caller provides `HasDerivAt` for the energy along a solution
- `dampedDrift_lipschitz` assumes `LipschitzWith K_T (gradient H.T)` and `LipschitzWith K_V (gradient H.V)` — both gradients are globally Lipschitz

**Strategy**: Lipschitz composition, `mul_le_mul_of_nonneg`.

#### `Hamiltonian/Legendre.lean`

Develops the Legendre transform and Bregman divergence. The Bregman divergence D_f(x,y) measures "how far x is from y according to f" and serves as a Lyapunov function for convergence proofs. The key insight is that convexity of f implies D_f ≥ 0, and strict convexity makes it a true distance (zero only at equality).

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
- `bregman_lyapunov_data` additionally requires `Continuous (bregman f · x_eq)` and a monotone-decrease certificate along solutions

**Strategy**: calculus on line maps (`lineMap_comp_convex`), slope inequalities, `ring`.

#### `Hamiltonian/FenchelMoreau.lean`

Proves the Fenchel–Moreau theorem: a lower-semicontinuous convex function equals its double conjugate (f = f**). This is the deepest result in the Hamiltonian layer, using geometric Hahn–Banach separation to construct supporting hyperplanes at every point of the epigraph.

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

**Key predicates (hypotheses tracked as separate definitions):**
- `HasFiniteConjugate f` — `∀ p, BddAbove (range (fun x => ⟨p,x⟩ − f x))` — conjugate is finite everywhere
- `HasFiniteBiconjugate f` — `∀ x, BddAbove (range (fun p => ⟨x,p⟩ − f* p))` — biconjugate is finite
- `IsSubgradientAt f x p` — `∀ y, f y ≥ f x + ⟨p, y − x⟩` — p is a subgradient of f at x
- `SubgradientExists f` — every point admits a subgradient

**Theorem hypotheses for `fenchel_moreau`:**
- `ConvexOn ℝ Set.univ f` — f is convex
- `LowerSemicontinuous f` — f is lower-semicontinuous
- `HasFiniteConjugate f` — conjugate is finite
- `HasFiniteBiconjugate f` — biconjugate is finite

**Strategy**: `ciSup_le` / `le_ciSup`, geometric Hahn–Banach (`geometric_hahn_banach_point_closed`), rescaling. The proof of f ≤ f** constructs a supporting hyperplane at each point below the graph, using Hahn–Banach to separate the point from the closed convex epigraph.

#### `Hamiltonian/NoseHoover.lean`

Implements the Nosé–Hoover thermostat, which extends Hamiltonian dynamics with a feedback variable ξ that injects or removes energy to drive the system toward a target temperature. The extended system conserves a modified Hamiltonian, and the equilibrium condition ξ̇ = 0 recovers the equipartition theorem.

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

**Assumptions on `ThermostatParams`:**
- `Q_pos : 0 < Q` — thermostat inertia is positive
- `kT_pos : 0 < kT` — target temperature is positive

**Key theorem hypotheses:**
- `subsystem_energy_rate` assumes `∀ p, gradient H.T p = p` (quadratic kinetic energy)
- `energy_injection_iff` additionally requires `x.p ≠ 0` (nonzero momentum)
- `thermostat_cools_when_cold` requires `‖x.p‖² < n * params.kT` (system is below target temperature)
- `extended_energy_conserved` takes a derivative certificate as hypothesis
- `noseHoover_lipschitz_on` assumes Lipschitz regularity on a bounded ball (passed in)

**Strategy**: `nlinarith` for thermodynamic inequalities.

#### `Hamiltonian/Ergodic.lean`

**Extra imports**: `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap` (for withDensity integral identities).

Defines the Gibbs/Boltzmann ensemble and the ergodic hypothesis. The partition function normalizes the Boltzmann weight exp(−V/kT) into a probability density; ergodicity asserts that time averages along trajectories converge to ensemble averages against this density.

| Kind | Name | Notes |
|------|------|-------|
| def | `partitionFunction`, `gibbsDensity`, `gibbsMeasure` | Boltzmann statistics |
| def | `timeAverage`, `ensembleAverage` | Ergodic observables |
| def | `IsErgodic` | Time average = ensemble average |
| theorem | `measurable_gibbsDensity`, `aemeasurable_gibbsDensity` | measurability closure |
| theorem | `integrable_gibbsDensity` | integrable under integrable weight |
| theorem | `gibbsDensity_nonneg` | `div_nonneg`, `exp_nonneg` |
| theorem | `gibbsDensity_integral_eq_one` | `div_self` |
| theorem | `partitionFunction_pos` | `integral_exp_pos` |
| theorem | `gibbsMeasure_isProbability_of_integrable_nonzero` | probability measure |
| theorem | `ensembleAverage_eq_integral_gibbsMeasure` | `withDensity` integral |
| theorem | `timeAverage_const` | `simp` |
| theorem | `ensembleAverage_const_eq` | `simp` |

**Key theorem hypotheses:**
- `gibbsDensity_integral_eq_one` requires `partitionFunction V kT μ ≠ 0` — the partition function is nonzero (system is not degenerate)
- `partitionFunction_pos` requires `[NeZero μ]` (nontrivial base measure) and `Integrable (fun q => exp (−V q / kT)) μ` — the Boltzmann weight is integrable (confining potential)
- `gibbsMeasure_isProbability_of_integrable_nonzero` requires `[NeZero μ]` and integrability of the Boltzmann weight
- `ensembleAverage_eq_integral_gibbsMeasure` requires `Measurable V` for the density measurability
- `timeAverage_const` requires `0 < T` — positive time window
- `IsErgodic` requires `Continuous f`, `Integrable f μ` for each observable — only well-behaved observables are ergodic

**Strategy**: `integral_nonneg`, `integral_exp_pos`, `div_self`, `withDensity` integral identities.

#### `Hamiltonian/Stability.lean`

Defines Lyapunov stability theory for Hamiltonian systems. A Lyapunov function V is a nonneg function that is zero at the equilibrium, positive elsewhere, and decreasing along trajectories. Strict Lyapunov (V → 0) gives asymptotic stability. Energy itself serves as a Lyapunov function for damped systems.

| Kind | Name | Notes |
|------|------|-------|
| structure | `LyapunovData` | V ≥ 0, V(x*)=0, V>0 elsewhere, V decreasing |
| structure | `StrictLyapunovData` | Adds V → 0 along trajectories |
| def | `IsAsymptoticallyStable`, `ExponentialEnergyDecay` | Stability predicates |
| theorem | `exponential_convergence` | Energy decay → dist convergence |
| def | `energyLyapunov` | Constructs Lyapunov data from energy |
| theorem | `damped_asymptotically_stable` | Strict Lyapunov → asymptotic stability |

**Assumptions on `LyapunovData F x`:**
- `V_cont : Continuous V` — Lyapunov function is continuous
- `V_zero : V x = 0` — vanishes at equilibrium
- `V_pos : ∀ y, y ≠ x → 0 < V y` — strictly positive away from equilibrium
- `V_nonneg : ∀ y, 0 ≤ V y` — globally nonnegative
- `V_decreasing` — V is nonincreasing along any trajectory satisfying the ODE

**Additional on `StrictLyapunovData`:**
- `V_to_zero` — V tends to 0 along trajectories (asymptotic decay)

**Key theorem hypotheses:**
- `exponential_convergence` requires `0 ≤ c` (constant), `∀ x, ‖x − x_eq‖² ≤ c * H.energy x` (energy controls distance), and `ExponentialEnergyDecay` (exponential energy bound)
- `energyLyapunov` requires energy continuity, positivity, vanishing at equilibrium, and a derivative certificate showing dH/dt = −γ‖p‖²

#### `Hamiltonian/Choreography.lean`

Bridges Hamiltonian mechanics with session-type choreography by partitioning phase-space coordinates among roles. Each role owns a disjoint subset of the coordinate indices, and messages carry position, momentum, or force data between roles.

| Kind | Name | Notes |
|------|------|-------|
| structure | `HamiltonianChoreography` | Hamiltonian + damping + role partition |
| theorem | `roles_disjoint` | Different roles → disjoint coordinate sets |
| theorem | `projectConfig_disjoint` | Projection zeroes non-owned coordinates |
| inductive | `PhaseMessage` | position, momentum, force, coupled |

**Assumptions on `HamiltonianChoreography n`:**
- `ham : ConvexHamiltonian n` — inherits all convexity/differentiability assumptions
- `damping : Damping` — inherits γ > 0
- `roles_partition : ∀ i, ∃! r, i ∈ roles r` — every coordinate index is owned by exactly one role (partition)

#### Examples

| File | Description |
|------|-------------|
| `HarmonicOscillator.lean` | Damped harmonic oscillator. Instantiates DampedFlow for the quadratic Hamiltonian; proves energy dissipation and decrease by specialization. |
| `Langevin.lean` | Connects Langevin dynamics to Nosé–Hoover. Proves simplex projection preserves zero-sum, and that Nosé–Hoover at ξ=γ matches damped dynamics. Both target the same Gibbs equilibrium. |
| `ThermostatOscillator.lean` | Nosé–Hoover applied to oscillator. Proves equipartition at equilibrium (‖p‖² = n·kT when ξ̇ = 0), bounded orbits from energy conservation, and perpetual oscillation (positive energy ⟹ never reaches origin). |
| `GradientDescent.lean` | Heavy-ball optimization as Hamiltonian mechanics. When momentum equals −∇V, the configuration-space trajectory reduces to gradient flow q̇ = −∇V. |
| `LatticeMaxwell.lean` | Maxwell's equations on a discrete 3D lattice with domain decomposition. Defines curl operators (placeholder stubs returning 0), proves energy nonnegativity, and shows local/global update coherence by `rfl`. Assumes `σ_pos : ∀ p, 0 < σ p` (conductivity is positive). |

---

### MeanField Layer

The mean-field layer formalizes population dynamics over a finite set of local states. It models large populations where each agent occupies one of finitely many states, and transitions occur according to rate functions. The central result is ODE existence/uniqueness on the probability simplex via Picard–Lindelöf, with Lyapunov stability theory for equilibrium analysis.

#### `MeanField/Basic.lean`

Defines the probability simplex and population states. A population state is a vector of counts that sum to a positive total; the empirical measure normalizes these to fractions living on the simplex.

| Kind | Name | Notes |
|------|------|-------|
| structure | `PopulationState Q` | Counts with total > 0 |
| def | `empirical` | Normalized counts → ℝ |
| def | `Simplex Q` | {x | x ≥ 0, ∑ x = 1} |
| theorem | `empirical_nonneg`, `empirical_sum_one` | `div_nonneg`, `div_self` |
| theorem | `Simplex.empirical_mem` | Empirical measure ∈ Simplex |
| inductive | `TwoState` | up/down with Fintype |
| theorem | `magnetizationOf_bounded` | |m| ≤ 1 |

**Assumptions on `PopulationState Q`:**
- `[Fintype Q]` — state space is finite
- `total_eq : ∑ q, counts q = total` — counts sum correctly
- `total_pos : total > 0` — population is non-empty

**Typeclass context:** `[Fintype Q]` throughout.

#### `MeanField/Choreography.lean`

Defines the choreographic specification for mean-field dynamics: a drift function on the simplex that is Lipschitz, conserves total probability, and points inward at boundaries (so the simplex is forward-invariant). Equilibria are zeros of the drift.

| Kind | Name | Notes |
|------|------|-------|
| def | `RateFunction Q` | (Q → ℝ) → ℝ with NonNeg, IsLipschitz, IsBounded |
| def | `DriftFunction Q` | (Q → ℝ) → (Q → ℝ) with Conserves, IsLipschitz |
| structure | `MeanFieldChoreography` | Drift + Lipschitz + conservation + boundary |
| def | `IsEquilibrium` | F(x) = 0 and x ∈ Simplex |
| def | `IsStable`, `IsAsymptoticallyStable` | ODE-style stability definitions via solution trajectories |

**Assumptions on `MeanFieldChoreography Q`:**
- `drift_lipschitz : ∃ L, DriftFunction.IsLipschitz drift L` — drift is Lipschitz on the simplex (needed for ODE uniqueness)
- `drift_conserves : DriftFunction.Conserves drift` — `∀ x ∈ Simplex Q, ∑ q, drift x q = 0` (probability is conserved)
- `boundary_nonneg : ∀ x ∈ Simplex Q, ∀ q, x q = 0 → 0 ≤ drift x q` — drift points inward at simplex boundary (no state fraction goes negative)

#### `MeanField/Rules.lean`

Builds drift functions compositionally from lists of population rules. Each rule specifies a stoichiometric update (which states gain/lose agents) and a rate function. Binary rules model pairwise interactions; unary rules model spontaneous transitions. Conservation and boundary invariance are proved by induction over the rule list.

| Kind | Name | Notes |
|------|------|-------|
| structure | `PopRule Q` | Stoichiometric update + rate function |
| structure | `BinaryRule`, `UnaryRule` | Two-agent and one-agent specializations |
| def | `driftFromRules` | Aggregates rules into drift |
| theorem | `BinaryRule.toPopRule_conserves` | ∑ update = 0 |
| theorem | `driftFromRules_conserves` | Aggregate conserves mass |
| theorem | `driftFromRules_boundary_nonneg` | Simplex forward-invariance |
| def | `MeanFieldChoreography.fromRules` | Constructs choreography from rule list |

**Key predicates on rules:**
- `PopRule.Conserves r` — `∑ q, r.update q = 0` — each rule conserves total count
- `PopRule.HasNonNegRate r` — rate is nonneg on simplex
- `PopRule.BoundaryNonneg r` — `∀ x ∈ Simplex, ∀ q, x q = 0 → 0 ≤ (update q : ℝ) * rate x` — rule doesn't push boundary states negative

**Key theorem hypotheses:**
- `massActionRate_nonneg` (binary and unary) requires `0 ≤ k` — nonneg rate constant
- `driftFromRules_boundary_nonneg` requires `∀ r ∈ rules, PopRule.BoundaryNonneg r` — every rule respects boundaries
- `driftFromRules_conserves` requires `∀ r ∈ rules, r.Conserves` — every rule conserves mass
- `MeanFieldChoreography.fromRules` requires all of the above plus `∃ L, IsLipschitz (driftFromRules rules) L`

**Strategy**: induction on `List`, Finset summation swaps, `by_cases` on state equality.

#### `MeanField/LipschitzBridge.lean`

Technical bridge between the project's Lipschitz predicate (defined on the simplex) and Mathlib's `LipschitzWith` typeclass (defined globally). Extends the drift function from the simplex to all of ℝ^Q while preserving the Lipschitz constant, and wraps it as a time-dependent ODE for Picard–Lindelöf.

| Kind | Name | Notes |
|------|------|-------|
| def | `DriftFunction.toLipschitzOnWith` | Predicate → Mathlib LipschitzOnWith |
| def | `DriftFunction.extend` | Extends drift from simplex to ℝ^Q |
| theorem | `extend_lipschitz` | Extension preserves Lipschitz constant |
| def | `toTimeDep` | Wraps autonomous drift as time-dependent |

**Key theorem hypotheses:**
- `toLipschitzOnWith` requires `DriftFunction.IsLipschitz F K` — the simplex-local Lipschitz property
- `extend_apply` requires `x ∈ Simplex Q` — extension agrees with original on simplex

**Strategy**: `ENNReal` arithmetic, `Classical.choose_spec`.

#### `MeanField/ODE.lean`

ODE existence, uniqueness, and simplex invariance for mean-field dynamics. Uses Picard–Lindelöf for local existence (Lipschitz drift on a bounded set) and Gronwall's inequality for uniqueness. Also defines the linearized stability apparatus: Jacobian, Hurwitz condition, and ODE-level Lyapunov structures.

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
- `ode_exists` requires `[Nonempty Q]`, `x₀ ∈ Simplex Q`, `∀ x, ∑ q, extendDrift x q = 0` (conservation on extension), and boundary inwardness on extension
- `ode_unique` requires two solutions sharing the same initial condition; uniqueness follows from `LipschitzWith K` on the extended drift
- `simplex_invariant` same hypotheses as `ode_exists`
- `fixed_point_is_constant` requires `IsEquilibrium C x` plus the ODE hypotheses

**Assumptions on `LyapunovData F x` (MeanField version):**
- `V_cont`, `V_zero`, `V_pos`, `V_nonneg`, `V_decreasing` — same structure as Hamiltonian version but for (Q → ℝ)-valued trajectories

**Definition:**
- `IsHurwitz F x` — `∀ μ : ℂ, HasEigenvalue (toLin' (JacobianComplex F x)) μ → μ.re < 0` — all eigenvalues have negative real part

#### `MeanField/Existence.lean`

Carries out the Picard–Lindelöf construction and proves simplex forward-invariance by a Gronwall-type argument. The simplex is bounded (finite-dimensional simplex), the drift is Lipschitz, so a global solution exists. Forward invariance uses a scalar Gronwall inequality: if a state fraction is zero and the drift is inward, the fraction stays nonneg.

| Kind | Name | Notes |
|------|------|-------|
| theorem | `local_ode_exists` | Picard–Lindelöf on bounded ball |
| theorem | `global_ode_exists` | Extended to simplex via boundedness |
| theorem | `simplex_forward_invariant` | Nonneg + sum-one preserved |
| def | `MeanFieldChoreography.solution` | Canonical solution via `Classical.choose` |

**Key theorem hypotheses:**
- `simplex_forward_invariant` requires `LipschitzWith K C.drift` (global Lipschitz), `∀ x, ∑ q, C.drift x q = 0` (conservation), `∀ x q, x q = 0 → 0 ≤ C.drift x q` (boundary), `sol 0 ∈ Simplex Q` (initial condition), `Continuous sol`, and the derivative condition
- `scalar_nonneg_of_gronwall` requires `0 ≤ K`, `ContinuousOn u (Icc 0 T)`, derivative bound, `0 ≤ u 0`, and `∀ t, u t ≤ 0 → −K * u t ≤ u' t` — a one-sided Gronwall condition

**Strategy**: `Metric.isBounded_iff`, `closedBall`, `IsPicardLindelof`.

#### `MeanField/Stability.lean`

Lyapunov stability theory for the mean-field ODE. A Lyapunov function certifies stability; a strict Lyapunov function certifies asymptotic stability. The linearized pathway goes through the Hurwitz spectral condition (all Jacobian eigenvalues have negative real part).

| Kind | Name | Notes |
|------|------|-------|
| theorem | `lyapunov_implies_stable` | Lyapunov function → stability |
| theorem | `strict_lyapunov_implies_asymptotic` | Strict → asymptotic stability |
| theorem | `hurwitz_implies_lyapunov_exists` | Hurwitz spectrum → Lyapunov exists |
| theorem | `linear_stable_implies_asymptotic` | Main linearized stability result |

**Typeclass context:** `[Fintype Q] [DecidableEq Q]`

**Key theorem hypotheses:**
- `lyapunov_implies_stable` requires `[Nonempty Q]`, `IsEquilibrium C x`, conservation and boundary on the extended drift, and a `LyapunovData C.drift x`
- `strict_lyapunov_implies_asymptotic` same plus `StrictLyapunovData`
- `linear_stable_implies_asymptotic` requires `IsLinearlyStable C.drift x` (fixed point + Hurwitz), `x ∈ Simplex Q`, conservation, boundary, `DifferentiableAt ℝ C.drift x`, and a `StrictLyapunovData` — the Lyapunov function is assumed, not constructed

**Strategy**: compactness of sphere, continuity, spectral condition.

#### `MeanField/Projection.lean`

Addresses the inverse problem: given a target drift function, find nonneg rate functions for a fixed set of stoichiometric templates that reproduce it. This is the "projection" from a global population-level specification to a concrete set of interaction rules.

| Kind | Name | Notes |
|------|------|-------|
| structure | `ProjectionProblem` | Target drift + rule templates |
| structure | `ProjectionSolution` | Rates producing the target drift |
| theorem | `projection_correct` | Solution reproduces target |
| theorem | `projection_exists` | Existence under conic decomposition |

**Assumptions on `ProjectionProblem Q`:**
- `templates_conserve : ∀ tmpl ∈ ruleTemplates, ∑ q, tmpl q = 0` — each stoichiometric template conserves total count

**Assumptions on `ProjectionSolution Q P`:**
- `rates_nonneg : ∀ i, (rates i).NonNeg` — rates are nonneg on simplex
- `produces_drift : ∀ x ∈ Simplex Q, ∀ q, ∑ i, (P.template i q : ℝ) * rates i x = P.targetDrift x q` — rates reproduce target drift exactly

**Key theorem hypotheses:**
- `projection_exists` requires `[DecidableEq Q]` and `∀ x ∈ Simplex Q, ∃ coeffs, (∀ i, 0 ≤ coeffs i) ∧ ∀ q, targetDrift x q = ∑ i, coeffs i * template i q` — the target drift admits a conic decomposition in the templates at every simplex point

#### `MeanField/Examples/Ising/`

Four files implementing the mean-field Ising model. `TanhAnalysis.lean` analyzes the self-consistency equation m = tanh(βm). `Drift.lean` defines the Ising drift and proves conservation. `Glauber.lean` builds Glauber spin-flip dynamics from binary rules. `PhaseTransition.lean` characterizes the phase transition at β = 1 (order–disorder boundary).

---

### ContinuumField Layer

The continuum field layer lifts the discrete mean-field framework to spatially extended systems. Instead of counting agents in states, it tracks density, polarization, and spin fields over continuous space, with interactions mediated by nonlocal integral kernels. The key structural result is that global and local views of the kernel operator are definitionally equal.

#### `ContinuumField/Basic.lean`

Defines the basic field types: a field is a function from space to values, and a field state bundles density ρ, polarization p, and optional spin ω.

| Kind | Name | Notes |
|------|------|-------|
| def | `Field X V` | X → V |
| structure | `FieldState X V W` | (ρ, p, ω) triple |

#### `ContinuumField/Kernel.lean`

Defines the global interaction kernel with its regularity and normalization conditions. A kernel assigns a nonneg, unit-mass, integrable weight K(x,x') to each pair of spatial points. The local kernel K_x(ξ) = K(x, x+ξ) is the displacement view from a single point.

| Kind | Name | Notes |
|------|------|-------|
| def | `KernelField X` | X → ℝ |
| structure | `GlobalKernel X` | K with measurability, nonnegativity, mass normalization |
| def | `GlobalKernel.localKernel` | Projects K(x,x') → K_x(ξ) = K(x, x+ξ) |
| structure | `KernelRule` | Deterministic kernel update from field state |

**Assumptions on `GlobalKernel X`:**
- `[MeasureSpace X]` — X carries a measure
- `measurable_K : Measurable (fun p : X × X => K p.1 p.2)` — K is jointly measurable
- `nonneg : ∀ x x', 0 ≤ K x x'` — pointwise nonneg
- `mass_one : ∀ x, ∫ x', K x x' = 1` — normalized (each row is a probability density)
- `integrable_K : ∀ x, Integrable (fun x' => K x x')` — each row is integrable

#### `ContinuumField/Projection.lean`

Proves that the global nonlocal operator (integrating over absolute positions x') and the local operator (integrating over displacements ξ) are definitionally equal. This is the exactness lemma: no information is lost when switching between global and local kernel views.

| Kind | Name | Notes |
|------|------|-------|
| def | `nonlocalGlobal` | ∫ K(x,x') (p(x')−p(x)) dx' |
| def | `nonlocalLocal` | ∫ K_x(ξ) (p(x+ξ)−p(x)) dξ |
| theorem | `nonlocal_exact` | Global = local operator. **Proof: `rfl`** |

**Typeclass context:** `[MeasureSpace X] [Add X]`, `[NormedAddCommGroup V] [NormedSpace ℝ V]`

**Key result**: the two integral forms are definitionally equal by construction — no hypotheses beyond the types.

#### `ContinuumField/EffectsIntegration.lean`

Connects the continuum kernel to the effects/session-type framework. Each role is assigned a spatial location; the global kernel projects to a local kernel field per role. Coherence means each role's local kernel equals the projection of the global kernel at that role's location. Soundness follows: coherent locals reproduce the global operator.

| Kind | Name | Notes |
|------|------|-------|
| def | `RoleLoc`, `KernelDecl`, `LocalKernelEnv` | Per-role kernel attachment |
| def | `KernelCoherent` | Local kernels = projection of global |
| theorem | `projection_sound` | Coherent locals reproduce global operator |

**Key hypothesis:**
- `projection_sound` requires `KernelCoherent loc K env` — `∀ r, env.kernelAt r = GlobalKernel.localKernel K (loc r)` — each role's local kernel is exactly the projection of the global kernel at that role's location

#### `ContinuumField/Closure.lean`

Defines optional coarse-grained summaries of kernels (range, anisotropy, mass) and a closure specification that guarantees the summary reconstructs the kernel to within a pointwise error bound.

| Kind | Name | Notes |
|------|------|-------|
| structure | `KernelSummary` | Range, anisotropy, mass |
| structure | `ClosureSpec` | close/reconstruct with approximation bound |

**Assumptions on `ClosureSpec X`:**
- `sound : ∀ K, KernelApprox K (reconstruct (close K)) bound` — reconstruction approximates the original kernel pointwise within `bound`

Where `KernelApprox K₁ K₂ ε` means `∀ ξ, |K₁ ξ − K₂ ξ| ≤ ε`.

#### `ContinuumField/Adaptivity.lean`

Specifies how the interaction kernel depends on and co-evolves with the field state. The key regularity condition is Lipschitz dependence: small changes in the field state produce small changes in the kernel.

| Kind | Name | Notes |
|------|------|-------|
| structure | `KernelDependence` | Kernel as Lipschitz function of field state |
| structure | `KernelDynamics` | Drift for kernel evolution |

**Assumptions on `StateMetric X V W`:**
- `dist_nonneg : ∀ s₁ s₂, 0 ≤ dist s₁ s₂` — metric is nonneg

**Assumptions on `KernelDependence X V W`:**
- `lipschitz : ∃ L ≥ 0, ∀ s₁ s₂ x x', |(kernelOf s₁).K x x' − (kernelOf s₂).K x x'| ≤ L * metric.dist s₁ s₂` — kernel varies Lipschitz-continuously with the field state

#### `ContinuumField/TimeBridge.lean`

Bridges continuous time (field evolution) and discrete steps (protocol/effects). Defines a sampling schedule mapping step indices to real times, and proves that constructed samplers are clock-independent: they never consult a remote party's local clock, only their own step counter or a pre-agreed global schedule.

| Kind | Name | Notes |
|------|------|-------|
| structure | `SamplingSchedule` | sampleTime : ℕ → ℝ |
| def | `ClockIndependent` | Sampler ignores remote clock |
| theorem | `mkSampler_clockIndependent` | Constructed samplers are clock-independent. `rfl` |
| structure | `SpatialBridge` | Role locations + topology constraints + soundness |
| theorem | `satisfies_colocated`, `satisfies_within` | Unpack bridge soundness |

**Key definitions:**
- `ClockIndependent s` — `∀ k t₁ t₂, s.sample k t₁ = s.sample k t₂` — output depends only on step index, not on the remote time argument
- `Colocated loc r₁ r₂` — `loc r₁ = loc r₂` — two roles share the same spatial location
- `Within loc r₁ r₂ d` — `dist (loc r₁) (loc r₂) ≤ d` — roles are within distance d

**Assumptions on `SpatialBridge X Topology SpatialReq`:**
- `[PseudoMetricSpace X]` — space has a metric
- `colocated_sound` — topology satisfaction implies actual colocation
- `within_sound` — topology satisfaction implies actual distance bound

#### `ContinuumField/SpatialMirror.lean`

A self-contained mirror of the Effects system's spatial types (sites, spatial requirements, topology, satisfaction). This avoids a direct dependency on the Effects library while maintaining structural compatibility.

Defines `Site := String`, `RoleName := Role`, `SpatialReq` (inductive with `netCapable`, `timeoutCapable`, `colocated`, `reliableEdge`, `conj`, `top`, `bot`), `Topology`, and `Satisfies`.

#### `ContinuumField/SpatialBridge.lean`

Adapter from the Effects spatial mirror to the continuum SpatialBridge. Requires role locations to be aligned with the topology's site assignment (roles assigned to the same site are actually at the same spatial point).

| Kind | Name | Notes |
|------|------|-------|
| def | `AlignedRoleLoc` | Role locations respect site assignment |
| def | `effectsSpatialBridge` | Constructs SpatialBridge from Effects types |

**Key assumption:**
- `AlignedRoleLoc` — `∀ r₁ r₂, topo.assign r₁ = topo.assign r₂ → loc r₁ = loc r₂` — roles assigned to the same site share the same spatial location

#### `ContinuumField/Examples/Anisotropic2D.lean`

A concrete 2D example with an anisotropic kernel that weights influence by direction (models a vision cone). Demonstrates projection exactness and closure soundness by specialization of the general theorems.

| Kind | Name | Notes |
|------|------|-------|
| def | `anisotropicLocal` | 2D anisotropic kernel with direction weighting |
| theorem | `example_exact` | Projection exactness. `simpa using nonlocal_exact` |
| theorem | `example_closure_bound` | Closure soundness. `simpa using C.sound` |

---

## Proof Strategy Index

| Strategy | Where used | What it proves |
|----------|-----------|----------------|
| `rfl` / definitional equality | Projection, TimeBridge, LatticeMaxwell | Operator exactness, coherence, domain decomposition |
| `simp` | Everywhere | Unfolding definitions, arithmetic simplification |
| `linarith` / `nlinarith` | ConvexHamiltonian, DampedFlow, NoseHoover, Stability | Inequalities from convexity, energy bounds, thermodynamics |
| `positivity` | ConvexHamiltonian, ThermostatOscillator | Nonnegativity of energy, norms |
| `ring` | Legendre, Langevin, Basic | Algebraic identities |
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
