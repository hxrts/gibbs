# Gibbs — Code Map

## Module Dependency Tree

```
Gibbs/Session.lean
│
├── Hamiltonian/Basic.lean
│   ├── Hamiltonian/Entropy.lean
│   ├── Hamiltonian/EntropyBregman.lean
│   ├── Hamiltonian/Channel.lean
│   ├── Hamiltonian/ChannelSession.lean
│   ├── Hamiltonian/PartitionFunction.lean
│   ├── Hamiltonian/EnergyDistance.lean
│   ├── Hamiltonian/EnergyGap.lean
│   ├── Hamiltonian/ConvexHamiltonian.lean
│   │   ├── Hamiltonian/DampedFlow.lean
│   │   │   ├── Hamiltonian/Choreography.lean
│   │   │   │   └── Hamiltonian/GlobalType.lean
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
│   ├── Hamiltonian/GaussianIntegrals.lean
│   ├── Hamiltonian/Ergodic.lean              (imports GaussianIntegrals)
│   ├── Hamiltonian/Stability.lean
│   └── Hamiltonian/Stochastic/
│       ├── Hamiltonian/Stochastic/Basic.lean
│       ├── Hamiltonian/Stochastic/LangevinFokkerPlanck.lean
│       └── Hamiltonian/Stochastic/ChannelNoise.lean
│
├── ContinuumField/Basic.lean
│   ├── ContinuumField/Kernel.lean
│   │   ├── ContinuumField/Adaptivity.lean
│   │   ├── ContinuumField/Closure.lean
│   │   ├── ContinuumField/Projection.lean
│   │   ├── ContinuumField/EffectsIntegration.lean
│   │   │   └── ContinuumField/GlobalType.lean
│   │   └── ContinuumField/Examples/Anisotropic2D.lean
│   └── ContinuumField/TimeBridge.lean
│       ├── ContinuumField/SpatialBridge.lean
│       │   └── ContinuumField/SpatialMirror.lean
│       └── ContinuumField/CapacityBridge.lean
│
└── MeanField/Basic.lean
    ├── MeanField/OrderParameter.lean
    ├── MeanField/Universality.lean
    └── MeanField/Choreography.lean
        ├── MeanField/Rules.lean
        │   ├── MeanField/Projection.lean
        │   └── MeanField/GlobalType.lean
        └── MeanField/LipschitzBridge.lean
            ├── MeanField/ODE.lean
            │   ├── MeanField/Existence.lean
            │   ├── MeanField/Stability.lean
            │   └── MeanField/BregmanBridge.lean  (also imports Hamiltonian/Legendre)
            └── MeanField/Examples/Ising/…

└── Consensus/Basic.lean
    ├── Consensus/Observation.lean
    ├── Consensus/Decision.lean
    ├── Consensus/Adversary.lean
    ├── Consensus/TranscriptDistance.lean
    ├── Consensus/InteractiveDistance.lean
    ├── Consensus/PartitionFunction.lean
    ├── Consensus/OrderParameter.lean
    ├── Consensus/Gap.lean
    ├── Consensus/Hamiltonian.lean
    ├── Consensus/SafetyLiveness.lean
    ├── Consensus/Quorum.lean
    ├── Consensus/Thresholds.lean
    ├── Consensus/UniversalityClasses.lean
    ├── Consensus/CodingBridge.lean
    ├── Consensus/CodingDistance.lean
    ├── Consensus/Certificates.lean
    ├── Consensus/ChannelThreshold.lean
    └── Consensus/Examples/…
```

Root facade: `Gibbs.lean` (imports all layers).
Layer facades: `Gibbs/Hamiltonian.lean`, `Gibbs/MeanField.lean`, `Gibbs/ContinuumField.lean`, `Gibbs/Consensus.lean`.
Stochastic facade: `Gibbs/Hamiltonian/Stochastic.lean` (re-exports `Basic`, `LangevinFokkerPlanck`, `ChannelNoise`).

---

## Proof Completeness

**No `sorry` anywhere in the codebase.**
Several deep information-theoretic results are stated as axioms in the entropy
and channel bridge files; all other proofs are concrete.

---

## Per-File Detail

### `Session.lean`

Session-typing vocabulary shared across choreography bridges: session identifiers, roles, labels, endpoints, and directed communication edges.

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
| structure | `StronglyConvex` | f is m-strongly convex (m > 0, quadratic lower bound) |
| structure | `LipschitzGradient` | gradient of f is L-Lipschitz (L > 0) |
| def | `conditionNumber` | L / m condition number |
| def | `optimalDamping` | 2√m critical damping coefficient |

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
| | | Bregman-Lyapunov bridge moved to `MeanField/BregmanBridge.lean` |

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

Implements the Nosé–Hoover thermostat, which extends Hamiltonian dynamics with a feedback variable ξ that injects or removes energy to drive the system toward a target temperature. Includes ergodicity infrastructure connecting to the Gibbs measure.

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

#### `Hamiltonian/GlobalType.lean`

Encodes a `HamiltonianChoreography` as a Telltale `GlobalType`. One time step chains position exchanges then force exchanges for all coupled pairs, wrapped in `mu "step"` for iteration. Proves well-formedness by induction on the communication list.

| Kind | Name | Notes |
|------|------|-------|
| def | `chainComms` | Chains `(sender, receiver, label)` triples into nested `comm` nodes |
| def | `coupledPairs` | Directed edges from role list + coupling predicate |
| theorem | `coupledPairs_noSelfComm` | All pairs have distinct components |
| def | `HamiltonianChoreography.toGlobalType` | Encoding: position comms ++ force comms in `mu "step"` |
| theorem | `HamiltonianChoreography.toGlobalType_wellFormed` | allVarsBound, allCommsNonEmpty, noSelfComm, isProductive |

**Strategy**: induction on comm list for four helper lemmas, `List.exists_cons_of_length_pos` for productivity.

#### `Hamiltonian/Entropy.lean`

Finite Shannon entropy, KL divergence, marginals, and mutual information for discrete distributions.

| Kind | Name | Notes |
|------|------|-------|
| structure | `Distribution` | Finite pmf with nonneg + sum-one |
| def | `shannonEntropy`, `binaryEntropy` | H(p), H₂(ε) |
| def | `klDivergence` | D_KL(p‖q) |
| def | `marginalFst`, `marginalSnd` | Joint marginals |
| def | `condEntropy`, `mutualInfo` | H(X|Y), I(X;Y) |
| def | `MarkovKernel`, `pushforward` | Markov kernel and induced joint |
| theorem | `shannonEntropy_nonneg` | Termwise log bounds |
| theorem | `shannonEntropy_deterministic` | Deterministic entropy = 0 |
| theorem | `klDivergence_nonneg` | Gibbs inequality via log bound |
| theorem | `klDivergence_eq_crossEntropy_sub` | Cross-entropy decomposition |
| theorem | `condEntropy_le_entropy` | From mutual info nonneg |
| axiom | `shannonEntropy_le_log_card` | Jensen/sharp bound |
| axiom | `klDivergence_eq_zero_iff` | Equality case of Gibbs inequality |
| axiom | `mutualInfo_nonneg` | Info-theoretic axiom |
| theorem | `mutualInfo_symm` | Symmetry of mutual information |
| axiom | `data_processing_inequality` | Markov processing cannot increase info |

**Axioms**: Jensen bound, equality case, mutual info nonnegativity, and DPI are stated axiomatically.

#### `Hamiltonian/EntropyBregman.lean`

Bridges entropy to convex duality. Negative entropy generates KL as a Bregman divergence; its Legendre dual is log-sum-exp.

| Kind | Name | Notes |
|------|------|-------|
| def | `negEntropyConfig` | Σ xᵢ log xᵢ on Config space |
| def | `softmax` | exp-normalized distribution |
| theorem | `softmax_nonneg`, `softmax_sum_one` | Valid distribution |
| axiom | `negEntropyConfig_strictConvex_on_interior` | Strict convexity on simplex |
| axiom | `kl_eq_bregman_negEntropy` | KL = Bregman(−H) |
| axiom | `legendre_negEntropy_eq_logSumExp` | Dual = log-sum-exp |
| axiom | `freeEnergy_eq_scaled_legendre_dual` | Free energy as Legendre dual |

#### `Hamiltonian/Channel.lean`

Discrete memoryless channels, induced distributions, and capacity (as a supremum of mutual information).

| Kind | Name | Notes |
|------|------|-------|
| structure | `DMC` | Stochastic matrix W(y|x) |
| def | `outputDist`, `jointDist` | Induced distributions |
| def | `channelMutualInfo`, `channelCapacity` | I(p;W), sup over p |
| def | `BSC` | Binary symmetric channel |
| theorem | `jointDist_marginalFst`, `jointDist_marginalSnd` | Marginal recovery |
| theorem | `channelCapacity_nonneg` | Nonnegativity (requires nonempty alphabets) |
| axiom | `channelCapacity_le_log_input`, `channelCapacity_le_log_output` | Log bounds |
| axiom | `bsc_capacity`, `bsc_capacity_half` | Closed-form BSC capacity |
| axiom | `capacity_as_free_energy_dual` | Variational dual structure |

#### `Hamiltonian/ChannelSession.lean`

Session-typed channels with capacity constraints; projection as marginalization.

| Kind | Name | Notes |
|------|------|-------|
| structure | `TypedChannel`, `ProtocolStep` | Edge + channel + rate |
| def | `TypedChannel.capacity` | Capacity of the edge channel |
| def | `branchEntropy` | Branching information cost |
| def | `ProtocolFeasible`, `bottleneck` | Feasibility predicate and detector |
| def | `projectionInfoLoss`, `projectionInfoRetained` | H(Y|X) and I(X;Y) |
| theorem | `projection_decomposition` | H(X,Y) = H(X) + H(Y|X) |
| theorem | `projection_preserves_feasibility` | Trivial projection property |

#### `Hamiltonian/PartitionFunction.lean`

Finite-state partition function Z(beta) = sum_x exp(-beta H(x)) and free energy F = -(1/beta) log Z. Proves nonnegativity of Z, bounds relating Z to the minimum energy, and free-energy sandwiching: min H - (log |Omega|)/beta le F le min H.

| Kind | Name | Notes |
|------|------|-------|
| def | `partitionFunction` | Z(beta) = sum exp(-beta H(x)) |
| def | `freeEnergy` | F = -(1/beta) log Z |
| def | `minEnergy` | min_x H(x) over finite state space |
| theorem | `partitionFunction_nonneg` | Z ge 0 via `Finset.sum_nonneg` |
| lemma | `energyImage_nonempty` | Image of H on Finset.univ is nonempty |
| theorem | `minEnergy_mem` | Some state attains the minimum energy |
| theorem | `minEnergy_le` | minEnergy le H(x) for all x |
| theorem | `partitionFunction_le_card_mul_exp_min` | Z le |Omega| exp(-beta min H) |
| theorem | `exp_min_le_partitionFunction` | exp(-beta min H) le Z |
| theorem | `log_partitionFunction_le_card_exp` | log Z le log|Omega| + (-beta min H) |
| theorem | `freeEnergy_le_minEnergy` | F le min H |
| theorem | `minEnergy_le_freeEnergy_add` | min H - (log|Omega|)/beta le F |

**Key hypotheses:** Bounds require `0 < beta` and `[Nonempty alpha]`.

**Strategy**: `Finset.sum_nonneg`, `exp_nonneg`, `Finset.single_le_sum`, `Real.log_le_log`, `field_simp`, `ring`.

#### `Hamiltonian/EnergyDistance.lean`

Pseudometric valued in extended nonneg reals, modeling energy barriers between states. Used by both the physics gap machinery and the consensus interactive distance.

| Kind | Name | Notes |
|------|------|-------|
| class | `EnergyDistance alpha` | dist : alpha -> alpha -> ENNReal with self/comm/triangle |
| def | `edistBall` | Ball of radius r around a state |
| theorem | `edist_self` | dist x x = 0 |

#### `Hamiltonian/EnergyGap.lean`

Gap between two sets of states, defined as the infimum of pairwise cross-set distances. A positive gap means a nontrivial energy barrier separates the sets.

| Kind | Name | Notes |
|------|------|-------|
| def | `energyGap` | sInf of cross-set distances |
| def | `HasEnergyGap` | 0 < energyGap A B |
| theorem | `energyGap_le_dist` | Any witness pair upper-bounds the gap |

**Strategy**: `sInf_le` with explicit witness.

#### `Hamiltonian/Stochastic/Basic.lean`

Constant-diffusion stochastic dynamics with a closed-form Itô integral. Provides a Brownian motion interface, SDE structure, and solution predicate using Mathlib's Bochner integral for the pathwise additive-noise case.

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

#### `Hamiltonian/Stochastic/ChannelNoise.lean`

Bridges noise variance to inverse temperature and information capacity.

| Kind | Name | Notes |
|------|------|-------|
| structure | `GaussianChannel` | Noise variance > 0 |
| def | `gaussianCapacity` | (1/2) log(1 + P/σ²) |
| def | `noiseToInvTemp`, `invTempToNoise` | σ² ↔ β conversion |
| def | `langevinCapacity` | Capacity at FDR point |
| theorem | `gaussianCapacity_nonneg` | P ≥ 0 ⇒ C ≥ 0 |
| theorem | `gaussianCapacity_antitone_variance` | More noise ⇒ lower capacity |
| theorem | `noiseToInvTemp_invTempToNoise` | Round-trip identity |
| theorem | `capacity_monotone_invTemp` | Higher β ⇒ higher capacity |
| theorem | `gaussianCapacity_monotone_power` | Monotone on nonnegative power |
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
| `GradientDescent.lean` | Heavy-ball optimization as Hamiltonian mechanics. Lyapunov candidate for momentum dynamics using `StronglyConvex` and `LipschitzGradient` from `ConvexHamiltonian`. |
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

#### `MeanField/OrderParameter.lean`

Order-parameter definitions for finite systems. Defines mean values, magnetization, and an `OrderParameter` wrapper.

| Kind | Name | Notes |
|------|------|-------|
| def | `mean` | Finite average of reals |
| def | `meanMagnetization` | Average of per-site observable |
| structure | `OrderParameter` | State → ℝ observable |
| def | `magnetizationParameter` | Packs magnetization as an order parameter |

#### `MeanField/Universality.lean`

Minimal universality-class vocabulary for macroscopic behavior.

| Kind | Name | Notes |
|------|------|-------|
| inductive | `UniversalityClass` | gapless / gapped / hybrid |
| def | `classOf` | Classifier from gap/tunneling flags |

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

#### `MeanField/GlobalType.lean`

Encodes a `MeanFieldChoreography` as a Telltale `GlobalType`. Since mean-field models have no intrinsic roles, a `MeanFieldRoleAssignment` partitions species among roles. One time step chains concentration exchanges for all coupled pairs, wrapped in `mu "step"`.

| Kind | Name | Notes |
|------|------|-------|
| structure | `MeanFieldRoleAssignment Q` | Role names, species assignment, coverage proof |
| def | `coupledPairs` | Directed edges from role list + coupling predicate |
| theorem | `coupledPairs_noSelfComm` | All pairs have distinct components |
| def | `MeanFieldChoreography.toGlobalType` | Encoding: concentration comms in `mu "step"` |
| theorem | `MeanFieldChoreography.toGlobalType_wellFormed` | allVarsBound, allCommsNonEmpty, noSelfComm, isProductive |

**Strategy**: induction on comm list for four helper lemmas, `List.exists_cons_of_length_pos` for productivity.

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

#### `MeanField/BregmanBridge.lean`

Connects the Hamiltonian Legendre layer to MeanField ODE stability. Converts between `Config n` (Euclidean) and `Fin n → ℝ` (simplex) representations and packages the Bregman divergence as a strict Lyapunov function for mean-field dynamics.

| Kind | Name | Notes |
|------|------|-------|
| def | `toConfig`, `fromConfig` | `EuclideanSpace.equiv` conversion helpers |
| theorem | `toConfig_fromConfig`, `fromConfig_toConfig` | Round-trip identities |
| theorem | `bregman_pos_of_ne` | Bregman divergence positive away from equilibrium |
| theorem | `toConfig_ne_of_ne` | Injectivity of toConfig |
| def | `bregman_lyapunov_data` | `StrictLyapunovData` from Legendre strict convexity |

**Strategy**: `EuclideanSpace.equiv` round-trips, Bregman positivity from Legendre strict convexity.

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

#### `MeanField/Examples/Ising/TanhAnalysis.lean`

Analytic properties of tanh needed for the Ising model: 1-Lipschitz bound and strict sublinearity (tanh(x) < x for x > 0).

| Kind | Name | Notes |
|------|------|-------|
| theorem | `Real.abs_tanh_sub_tanh_le` | 1-Lipschitz via MVT |
| theorem | `Real.tanh_lt_self` | tanh(x) < x for x > 0 |
| theorem | `Real.self_lt_tanh` | tanh(x) > x for x < 0 |
| theorem | `Real.abs_tanh_lt_abs` | |tanh(x)| < |x| for x ne 0 |
| theorem | `hasDerivAt_tanh` | d/dx tanh = 1/cosh^2 |
| theorem | `continuous_tanh` | Continuity |
| theorem | `tanh_lt_one` | tanh(x) < 1 for all x |

**Strategy**: MVT, monotonicity of tanh - id, `nlinarith`.

#### `MeanField/Examples/Ising/Drift.lean`

Ising drift function and choreography. The ODE right-hand side is (1/tau)[tanh(beta(Jm+h)) - m] where m is the magnetization.

| Kind | Name | Notes |
|------|------|-------|
| structure | `IsingParams` | beta, J, h, tau with positivity |
| def | `IsingParams.criticalBeta`, `.isFerromagnetic`, `.isParamagnetic` | Phase classification |
| def | `isingDrift` | ODE right-hand side on TwoState |
| theorem | `isingDrift_conserves` | Sum of drift components is zero |
| theorem | `isingDrift_lipschitz` | Lipschitz via tanh being 1-Lipschitz |
| theorem | `isingDrift_boundary_nonneg` | Drift points inward at simplex boundary |
| def | `IsingChoreography` | Full choreography bundle |

**Strategy**: `ring`, tanh Lipschitz composition, `by_cases` on TwoState.

#### `MeanField/Examples/Ising/Glauber.lean`

Glauber spin-flip dynamics: local transition rates that reproduce the global Ising drift when aggregated.

| Kind | Name | Notes |
|------|------|-------|
| def | `glauberAlpha` | Down-to-up rate |
| def | `glauberGamma` | Up-to-down rate |
| theorem | `glauberAlpha_nonneg`, `glauberGamma_nonneg` | Rate nonnegativity |
| theorem | `glauber_diff` | alpha - gamma = (1/tau) tanh(beta(Jm+h)) |
| theorem | `glauber_sum` | alpha + gamma = 1/tau |
| theorem | `glauber_produces_isingDrift` | Aggregated rates = Ising drift |

**Strategy**: algebra on exp sums, `field_simp`, `ring`.

#### `MeanField/Examples/Ising/PhaseTransition.lean`

Phase transition at beta J = 1. Paramagnetic phase has unique equilibrium m = 0. Ferromagnetic phase has two nonzero equilibria found by IVT.

| Kind | Name | Notes |
|------|------|-------|
| def | `isSelfConsistent` | m = tanh(beta(Jm + h)) |
| def | `equilibriumMagnetizations` | Self-consistent m in [-1,1] |
| theorem | `zero_is_equilibrium` | m = 0 always solves when h = 0 |
| theorem | `paramagnetic_unique_equilibrium` | beta J < 1 implies m = 0 is unique |
| theorem | `ferromagnetic_bistable` | beta J > 1 implies two nonzero solutions |

**Strategy**: strict sublinearity of tanh (paramagnetic), IVT on residual f(m) = m - tanh(beta J m) (ferromagnetic).

---

### Consensus Layer

The consensus layer specializes the physics-first machinery to executions, decisions, adversaries, and quorum thresholds.

#### `Consensus/Basic.lean`

| Kind | Name | Notes |
|------|------|-------|
| abbrev | `Process`, `Config`, `Execution` | Finite-horizon execution model |
| def | `initialConfig` | Time-0 configuration |

#### `Consensus/Observation.lean`

| Kind | Name | Notes |
|------|------|-------|
| abbrev | `Observation` | Local view interface |
| def | `Indistinguishable` | Honest-set indistinguishability |

#### `Consensus/Decision.lean`

| Kind | Name | Notes |
|------|------|-------|
| abbrev | `DecisionOut`, `DecisionFn` | Decider interface |
| def | `decisionVector`, `macrostateOf` | Macrostates from executions |
| def | `Agreement`, `Disagreement` | Safety predicates |

#### `Consensus/Adversary.lean`

| Kind | Name | Notes |
|------|------|-------|
| structure | `AdversaryClass` | Allowed transforms + budget |
| def | `adversaryBall` | Reachable execution set |

#### `Consensus/TranscriptDistance.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `hammingDistance`, `processDistance` | Static and interactive distances |
| theorem | `*_self`, `*_comm`, `*_triangle` | Pseudometric properties |
| def | `distanceBall` | Distance ball |
| theorem | `adversaryBall_subset_distanceBall` | Budget ⇒ ball inclusion |

#### `Consensus/InteractiveDistance.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `macrostateSet` | Executions realizing a macrostate |
| def | `interactiveDistance` | Distance between macrostates |
| theorem | `interactiveDistance_lower_bound` | Lifts pairwise lower bounds to the infimum |
| theorem | `interactiveDistance_eq_zero_of_overlap` | Overlap ⇒ zero distance |

#### `Consensus/PartitionFunction.lean`

| Kind | Name | Notes |
|------|------|-------|
| abbrev | `partitionFunction`, `freeEnergy` | Execution-level specialization |
| def | `partitionFunctionOn`, `freeEnergyOn` | Restrict to admissible executions |

#### `Consensus/OrderParameter.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `magnetization` | Magnetization on configurations |
| abbrev | `OrderParameter` | Consensus order parameter |

#### `Consensus/Gap.lean`

| Kind | Name | Notes |
|------|------|-------|
| abbrev | `energyGap`, `HasEnergyGap` | Physics-first gap |
| def | `restrictedPartitionFunction` | Subset partition function |
| theorem | `partitionFunctionOn_eq_restricted` | Subset partition function equality |
| def | `freeEnergyGap` | Free-energy difference |
| def | `IsSafe`, `HasSafetyGap` | Safety/gap predicates |
| def | `HasFinality`, `HasProbabilisticFinality` | Finality notions |

#### `Consensus/Hamiltonian.lean`

| Kind | Name | Notes |
|------|------|-------|
| structure | `ConsensusHamiltonian` | Conflict/delay/fault decomposition |
| def | `totalEnergy` | Summed Hamiltonian |
| def | `forbiddenEnergy` | Assign `∞` to forbidden executions |
| def | `energyWeight` | Boltzmann weight with `∞` mapped to 0 |
| theorem | `energyWeight_forbidden`, `energyWeight_allowed` | Forbidden/allowed weight behavior |

#### `Consensus/SafetyLiveness.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `IsSafeOn`, `IsLiveOn` | Safety/liveness over execution sets |
| theorem | `safety_mono`, `liveness_mono` | Monotonicity under inclusion |

#### `Consensus/Quorum.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `IsQuorum` | Quorum size predicate |
| theorem | `quorum_intersection_lower` | General intersection bound |
| theorem | `quorum_intersection_3f1` | 3f+1 specialization |

#### `Consensus/Thresholds.lean`

| Kind | Name | Notes |
|------|------|-------|
| theorem | `repetition_threshold` | 2f+1 threshold |
| theorem | `quorum_threshold`, `quorum_gap_implies` | 3f+1 threshold |
| def | `corruptionFraction` | Real-valued fraction `f / N` |
| theorem | `static_fraction_bound`, `interactive_fraction_bound` | <1/2 and <1/3 bounds |

#### `Consensus/UniversalityClasses.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `classOf`, `IsGapped` | Classifier + gap predicate |
| def | `gapSequence`, `thermodynamicGap` | Thermodynamic limit definitions |
| theorem | `thermodynamicGap_ge_of_eventually_ge` | Eventual lower bound ⇒ liminf lower bound |

#### `Consensus/CodingBridge.lean`

| Kind | Name | Notes |
|------|------|-------|
| structure | `Encoder`, `Decoder` | Block code interface |
| def | `UniqueDecoding` | Radius decoding predicate |
| def | `interactiveDistanceWord` | Non-interactive specialization |

#### `Consensus/CodingDistance.lean`

| Kind | Name | Notes |
|------|------|-------|
| instance | `hammingEnergyDistance` | EnergyDistance from Hamming distance |
| def | `minimumDistance` | Min distance via infimum |
| theorem | `unique_decoding_of_minDistance` | `t + t < d_min` uniqueness |
| theorem | `energyGap_singleton_eq_dist` | Singleton gap = distance |

#### `Consensus/Certificates.lean`

| Kind | Name | Notes |
|------|------|-------|
| def | `IsCertificate` | Quorum certifies a value |
| theorem | `certificates_agree_of_intersection` | Intersection ⇒ agreement |
| theorem | `certificates_agree_of_quorum_intersection` | Quorum bound ⇒ agreement |

#### `Consensus/ChannelThreshold.lean`

Coding-theoretic capacity as a consensus phase boundary.

| Kind | Name | Notes |
|------|------|-------|
| def | `channelEnergyGap` | Capacity − rate |
| theorem | `reliable_iff_positive_gap` | Linear inequality |
| def | `avgErrorProb` | Average decoding error |
| axiom | `blockChannel` | n-fold memoryless extension |
| axiom | `channel_coding_achievability` | Shannon direct theorem |
| axiom | `channel_coding_converse` | Shannon converse |
| def | `CodingSafe` | Arbitrarily small error below capacity |
| axiom | `codingSafe_iff_positive_gap` | Safety ↔ positive gap |
| structure | `NoisyConsensus` | Corruption rate model |
| theorem | `corruption_threshold_is_zero_capacity` | BSC ε=1/2 zero capacity |
| axiom | `consensus_requires_positive_capacity` | ε<1/2 ⇒ capacity > 0 |

#### `Consensus/Examples/RepetitionCode.lean`

Repetition code: encode one bit as N copies, decode by majority vote. Corrects up to floor((N-1)/2) errors. This is the simplest gapped phase, equivalent to the Ising ferromagnet and quorum consensus.

| Kind | Name | Notes |
|------|------|-------|
| abbrev | `Codeword` | `Fin N -> Bool` |
| def | `repetitionEncode` | Constant-value codeword |
| def | `countTrue`, `errorCount` | Counting helpers |
| def | `majorityDecode` | Decode by majority of true/false |
| def | `CorrectsUpTo` | Correction radius predicate |
| theorem | `majorityDecode_repetition` | Majority recovers original if errors le floor((N-1)/2) |
| theorem | `repetition_corrects_up_to` | `CorrectsUpTo` for radius floor((N-1)/2) |

**Strategy**: `Nat` arithmetic, `by_cases`, `omega`.

#### `Consensus/Examples/QuorumBFT.lean`

Quorum-based BFT with N = 3f+1 and quorum size 2f+1. Demonstrates that the safety gap exists (quorum intersection ge f+1) and collapses at N = 3f.

| Kind | Name | Notes |
|------|------|-------|
| theorem | `quorum_intersection_example` | Instantiates intersection bound at 3f+1 |
| theorem | `quorum_gap_collapse` | Gap vanishes at N = 3f |

**Strategy**: `omega`, specialization of `quorum_intersection_lower`.

#### `Consensus/Examples/NakamotoSketch.lean`

Nakamoto longest-chain as a gapless (Class I) system. No hard safety gap, but reorganization probability decays geometrically with confirmation depth.

| Kind | Name | Notes |
|------|------|-------|
| def | `gaplessGap` | Interactive distance is zero (no gap) |
| def | `reorgProbability` | Geometric decay model for reorg probability |
| theorem | `reorgProbability_succ_le` | Each additional confirmation reduces probability |

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

#### `ContinuumField/GlobalType.lean`

Encodes spatial field interactions as a Telltale `GlobalType`. Each role occupies a spatial location; nonlocal kernel coupling between locations becomes communication. One time step chains field exchanges for all coupled pairs, wrapped in `mu "step"`.

| Kind | Name | Notes |
|------|------|-------|
| def | `coupledPairs` | Directed edges from role list + coupling predicate |
| theorem | `coupledPairs_noSelfComm` | All pairs have distinct components |
| def | `kernelToGlobalType` | Encoding: field comms in `mu "step"` |
| theorem | `kernelToGlobalType_wellFormed` | allVarsBound, allCommsNonEmpty, noSelfComm, isProductive |

**Strategy**: induction on comm list for four helper lemmas, `List.exists_cons_of_length_pos` for productivity.

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

#### `ContinuumField/CapacityBridge.lean`

Distance-dependent channel capacities for spatially embedded roles.

| Kind | Name | Notes |
|------|------|-------|
| structure | `SpatialChannelModel` | Signal power, noise(d), monotone noise |
| def | `spatialCapacity`, `roleCapacity` | Capacity by distance/role pair |
| theorem | `spatialCapacity_antitone` | Distance ↑ ⇒ capacity ↓ |
| theorem | `spatialCapacity_pos` | Positive capacity at finite distance |
| theorem | `colocated_max_capacity` | Colocated ⇒ distance 0 |
| theorem | `within_capacity_bound` | Within d ⇒ capacity ≥ C(d) |
| structure | `SpatialProtocol` | Role locations + rates |
| def | `SpatialProtocol.isFeasible` | Per-edge capacity constraint |

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
| Induction on `List` | Rules, GlobalType files | Conservation/boundary for rules, well-formedness for chained comms |
| `by_cases` on state equality | Rules | Boundary nonnegativity (mass-action at zero) |
| `antitone_of_hasDerivAt_nonpos` | DampedFlow | Energy monotone decrease |
| Calculus on `lineMap` | Legendre | Bregman nonnegativity via convexity of restrictions to lines |
| Spectral / Hurwitz condition | Stability | Linearized asymptotic stability |
| Young's inequality + strong convexity | HeavyBallConvergence | Lyapunov derivative bounds, exponential decay |
| Gaussian integral decomposition | GaussianIntegrals | Product-measure Gaussian identities over Config |
| Compactness + coercivity | GradientDescentMinimizer | Minimizer existence for strongly convex functions |
| FP substitution + fluctuation-dissipation | LangevinFokkerPlanck | Gibbs stationarity under σ² = 2γkT |
| `Finset.sum_nonneg` + `exp_nonneg` | PartitionFunction | Z nonnegativity, free-energy bounds |
| `sInf_le` with witness | EnergyGap | Gap upper bound from any cross-set pair |
| `log_le_sub_one_of_pos` | Entropy | Gibbs inequality (KL ≥ 0) |
| `one_div_le_one_div_of_le` | ChannelNoise, CapacityBridge | Antitone in variance/distance |
| `field_simp` | EntropyBregman, ChannelThreshold | Softmax normalization, block-rate algebra |
| MVT + monotonicity | TanhAnalysis | tanh 1-Lipschitz, strict sublinearity |
| IVT on residual | PhaseTransition | Ferromagnetic bistability |
| `omega` | QuorumBFT, Thresholds | Nat arithmetic for quorum intersection and thresholds |
