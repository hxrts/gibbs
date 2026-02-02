# Mean-Field Dynamics

This document covers population dynamics on the probability simplex. The mean-field layer formalizes ODE existence, uniqueness, and stability for drift functions built from stoichiometric rules. For the convex analysis underpinning stability, see [Convex Duality and Bregman Divergence](03-convex-duality.md). For the application to consensus, see [Consensus as Statistical Mechanics](06-consensus-statistical-mechanics.md).

## The Probability Simplex

The probability simplex over a finite state space $Q$ is the set of nonneg vectors that sum to one:

$$\text{Simplex}(Q) = \{ x : Q \to \mathbb{R} \mid x_q \geq 0 \text{ for all } q, \; \sum_q x_q = 1 \}$$

A `PopulationState Q` stores integer counts with a positive total. The `empirical` function normalizes these counts into a point on the simplex. The theorems `empirical_nonneg` and `empirical_sum_one` verify the normalization.

The simplex is compact (closed and bounded in finite dimensions). This compactness is essential for ODE existence: it prevents finite-time blowup and guarantees that bounded drifts produce globally defined solutions.

## Drift Functions and Rules

A `DriftFunction Q` maps a state $x : Q \to \mathbb{R}$ to a velocity $F(x) : Q \to \mathbb{R}$. Two constraints ensure the simplex is forward-invariant:

1. Conservation: $\sum_q F(x)_q = 0$ for all $x$ on the simplex.
2. Boundary: $F(x)_q \geq 0$ whenever $x_q = 0$.

Conservation keeps the total probability at one. The boundary condition prevents components from going negative. Together they guarantee that trajectories starting in the simplex remain there.

Drift functions are built compositionally from `PopRule` structures. Each rule specifies a stoichiometric update vector and a rate function. The `driftFromRules` function aggregates a list of rules by summing their contributions. Conservation and boundary invariance are proved by induction on the rule list in `driftFromRules_conserves` and `driftFromRules_boundary_nonneg`.

## ODE Existence and Uniqueness

The drift function is Lipschitz on the simplex by construction, but Mathlib's Picard-Lindelöf theorem requires a globally Lipschitz function. The `LipschitzBridge.lean` module extends the drift from the simplex to all of $\mathbb{R}^Q$ while preserving the Lipschitz constant. The theorem `extend_lipschitz` establishes this.

Local existence follows from Picard-Lindelöf on a bounded ball containing the simplex. The `local_ode_exists` theorem in `Existence.lean` constructs the `IsPicardLindelof` instance with explicit parameters: time half-width, ball radius (simplex diameter), Lipschitz constant, and drift bound.

Global existence follows from compactness. Since the simplex is bounded and the drift is bounded on it, solutions cannot escape to infinity in finite time. The `global_ode_exists` theorem chains local solutions forward. Uniqueness follows from Gronwall's inequality in `ode_unique`.

## Stability Theory

An equilibrium $x^*$ satisfies $F(x^*) = 0$ and $x^* \in \text{Simplex}(Q)$. Stability is analyzed through two approaches.

The direct (Lyapunov) approach uses a function $V$ that is nonneg, zero at $x^*$, and decreasing along trajectories. The theorem `lyapunov_implies_stable` gives stability. A strict Lyapunov function where $V \to 0$ along trajectories gives asymptotic stability via `strict_lyapunov_implies_asymptotic`.

The linearized (Hurwitz) approach examines the Jacobian $J = \partial F / \partial x$ at equilibrium. If all eigenvalues of $J$ have negative real part (the Hurwitz condition), a quadratic Lyapunov function exists. The chain `hurwitz_implies_lyapunov_exists` then `linear_stable_implies_asymptotic` completes the argument.

The Bregman divergence connects these approaches. For a strictly convex generator $f$, $D_f(x, x^*)$ provides a natural Lyapunov function. The `bregman_lyapunov_data` construction in `BregmanBridge.lean` packages this as a `StrictLyapunovData`.

## The Ising Model

The mean-field Ising model is the concrete example that ties the layer together. The state space is `TwoState` with values `up` and `down`. The magnetization order parameter is $m = x_{\text{up}} - x_{\text{down}}$.

The drift function is:

$$\frac{dm}{dt} = \frac{1}{\tau}\left[\tanh(\beta(Jm + h)) - m\right]$$

The parameter $\beta$ is inverse temperature, $J$ is coupling strength, $h$ is external field, and $\tau$ is relaxation time. Equilibria satisfy the self-consistency equation $m = \tanh(\beta(Jm + h))$.

A phase transition occurs at $\beta J = 1$ when $h = 0$. Below the critical point ($\beta J < 1$), the unique equilibrium is $m = 0$ (paramagnetic phase). The proof in `paramagnetic_unique_equilibrium` uses strict sublinearity of $\tanh$: the theorem `Real.tanh_lt_self` shows $\tanh(x) < x$ for $x > 0$.

Above the critical point ($\beta J > 1$), two nonzero equilibria appear (ferromagnetic phase). The proof in `ferromagnetic_bistable` applies the intermediate value theorem to the residual $f(m) = m - \tanh(\beta J m)$, which changes sign on $(0, 1)$.

Glauber dynamics provides the microscopic mechanism. The spin-flip rates `glauberAlpha` and `glauberGamma` reproduce the macroscopic Ising drift when aggregated, proved in `glauber_produces_isingDrift`.
