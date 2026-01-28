import Gibbs.MeanField.LipschitzBridge
import Gibbs.MeanField.Existence
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-
The Problem. Connect mean-field choreographies to ODE solutions.
Given a drift function F : Simplex Q → (Q → ℝ) that is Lipschitz and
conserves probability, we need ODE existence, uniqueness, and simplex
invariance for dx/dt = F(x).

The difficulty is that Mathlib's ODE infrastructure (Picard-Lindelöf,
Gronwall) requires globally Lipschitz functions on normed spaces,
while our drift is defined only on the simplex. The Lipschitz bridge
(LipschitzBridge.lean) extends drift to the whole space.

Solution Structure.
1. IsSolution: what it means to solve dx/dt = F(x) with x(0) = x₀
2. Uniqueness: Gronwall inequality via ODE_solution_unique
3. Simplex invariance: conservation + boundary condition
4. Fixed points and stability definitions
-/

/-!
# ODE Semantics for Mean-Field Systems

## Main Results

- `ode_unique_on_Icc`: Uniqueness on bounded intervals via Gronwall
- `ode_unique`: Global uniqueness for choreography solutions
- `equilibrium_is_fixed_point`: Equilibria are simplex fixed points
- `IsHurwitz`: Hurwitz spectral condition (all eigenvalues Re < 0)
- `linear_stable_implies_asymptotic`: Moved to Stability.lean
-/

namespace Gibbs.MeanField

open scoped Classical NNReal

noncomputable section

variable {Q : Type*} [Fintype Q]

/-! ## ODE Solution Type -/

/-- A canonical global solution for a choreography's ODE, obtained via the
    Picard–Lindelöf global existence theorem on the extended drift. -/
abbrev ODESolution [Nonempty Q] (C : MeanFieldChoreography Q) (x₀ : Q → ℝ)
    {hx₀ : x₀ ∈ Simplex Q}
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) : ℝ → (Q → ℝ) :=
  C.solution x₀ hx₀ hcons hboundary

/-! ## Existence -/

/-- Global ODE solutions exist for mean-field choreographies with the
    (global) conservation and boundary conditions on the extended drift. -/
theorem ode_exists [Nonempty Q] (C : MeanFieldChoreography Q) (x₀ : Q → ℝ)
    (hx₀ : x₀ ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) :
    ∃ sol : ℝ → (Q → ℝ), sol 0 = x₀ ∧
      Continuous sol ∧
      ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t ∧ sol t ∈ Simplex Q := by
  -- This is exactly `global_ode_exists` from `Existence.lean`.
  simpa using global_ode_exists (C := C) x₀ hx₀ hcons hboundary

/-! ## Uniqueness -/

/-- What it means to be an ODE solution with derivative condition.
    The derivative holds for all t ≥ 0, including at the initial time. -/
def IsSolution (F : DriftFunction Q) (x₀ : Q → ℝ) (sol : ℝ → (Q → ℝ)) : Prop :=
  sol 0 = x₀ ∧
  Continuous sol ∧
  ∀ t ≥ 0, HasDerivAt sol (F (sol t)) t

/-- ODE solutions are unique for Lipschitz drift on any interval [0, T].

    Uses `ODE_solution_unique` from Mathlib.Analysis.ODE.Gronwall.
    The extended drift is globally Lipschitz, so Gronwall gives uniqueness. -/
theorem ode_unique_on_Icc (F : DriftFunction Q) (K : ℝ≥0)
    (hLip : LipschitzWith K F) (_x₀ : Q → ℝ)
    (sol₁ sol₂ : ℝ → (Q → ℝ))
    (hcont₁ : Continuous sol₁) (hcont₂ : Continuous sol₂)
    (hderiv₁ : ∀ t ≥ 0, HasDerivAt sol₁ (F (sol₁ t)) t)
    (hderiv₂ : ∀ t ≥ 0, HasDerivAt sol₂ (F (sol₂ t)) t)
    (hinit : sol₁ 0 = sol₂ 0)
    (T : ℝ) (_hT : 0 ≤ T) :
    Set.EqOn sol₁ sol₂ (Set.Icc 0 T) := by
  apply ODE_solution_unique (v := fun _ => F) (K := K)
  · intro _; exact hLip
  · exact hcont₁.continuousOn
  · intro t ht
    exact (hderiv₁ t ht.1).hasDerivWithinAt
  · exact hcont₂.continuousOn
  · intro t ht
    exact (hderiv₂ t ht.1).hasDerivWithinAt
  · exact hinit

/-- ODE solutions are unique for Lipschitz drift.

    Uses Gronwall's inequality via the extended drift. -/
theorem ode_unique (C : MeanFieldChoreography Q) (x₀ : Q → ℝ)
    (sol₁ sol₂ : ℝ → (Q → ℝ))
    (hsol₁ : IsSolution C.extendDrift x₀ sol₁)
    (hsol₂ : IsSolution C.extendDrift x₀ sol₂) :
    ∀ t ≥ 0, sol₁ t = sol₂ t := by
  intro t ht
  have hK := C.extendDrift_lipschitz
  -- Apply uniqueness on [0, t]
  have heq := ode_unique_on_Icc C.extendDrift C.lipschitzConstNNReal hK x₀
    sol₁ sol₂ hsol₁.2.1 hsol₂.2.1 hsol₁.2.2 hsol₂.2.2
    (by rw [hsol₁.1, hsol₂.1]) t ht
  exact heq ⟨ht, le_refl t⟩

/-! ## Simplex Invariance -/

/-- If the extended drift conserves mass and points inward at the boundary,
    the canonical solution stays in the simplex. -/
theorem simplex_invariant [Nonempty Q] (C : MeanFieldChoreography Q)
    (x₀ : Q → ℝ) (hx₀ : x₀ ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) :
    ∀ t ≥ 0, ODESolution C x₀ hcons hboundary t ∈ Simplex Q := by
  intro t ht
  simpa [ODESolution] using
    (MeanFieldChoreography.solution_mem_simplex (C := C) x₀ hx₀ hcons hboundary t ht)

/-! ## Fixed Points -/

/-- A point is a fixed point of the drift if F(x) = 0. -/
def IsFixedPoint (F : DriftFunction Q) (x : Q → ℝ) : Prop :=
  F x = 0

/-- Fixed points yield constant solutions (forward in time). -/
theorem fixed_point_is_constant [Nonempty Q] (C : MeanFieldChoreography Q) (x : Q → ℝ)
    (hx : IsEquilibrium C x)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) :
    ∀ t ≥ 0, ODESolution C x (hx₀ := hx.1) hcons hboundary t = x := by
  -- The constant solution is also a solution; uniqueness gives equality.
  intro t ht
  have hsol_const : IsSolution C.extendDrift x (fun _ => x) := by
    refine ⟨rfl, continuous_const, ?_⟩
    intro s _hs
    have hx' : x ∈ Simplex Q := hx.1
    have hzero : C.extendDrift x = 0 := by
      simpa [C.extendDrift_apply x hx'] using hx.2
    simpa [hzero] using (hasDerivAt_const (x := s) (c := x))
  have hsol_canon : IsSolution C.extendDrift x (ODESolution C x (hx₀ := hx.1) hcons hboundary) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [ODESolution] using
        (MeanFieldChoreography.solution_init (C := C) x hx.1 hcons hboundary)
    · simpa [ODESolution] using
        (MeanFieldChoreography.solution_continuous (C := C) x hx.1 hcons hboundary)
    · intro s hs
      -- The canonical solution stays in the simplex, so extended drift equals drift.
      have hmem :
          ODESolution C x (hx₀ := hx.1) hcons hboundary s ∈ Simplex Q := by
        simpa [ODESolution] using
          (MeanFieldChoreography.solution_mem_simplex (C := C) x hx.1 hcons hboundary s hs)
      have hderiv :=
        MeanFieldChoreography.solution_hasDerivAt (C := C) x hx.1 hcons hboundary s hs
      simpa [ODESolution, C.extendDrift_apply _ hmem] using hderiv
  have hEq := ode_unique (C := C) (x₀ := x)
    (sol₁ := ODESolution C x (hx₀ := hx.1) hcons hboundary)
    (sol₂ := fun _ => x) hsol_canon hsol_const t ht
  simpa using hEq

/-- Equilibria of a choreography are fixed points in the simplex. -/
theorem equilibrium_is_fixed_point (C : MeanFieldChoreography Q) (x : Q → ℝ) :
    IsEquilibrium C x ↔ x ∈ Simplex Q ∧ IsFixedPoint C.drift x := by
  simp only [IsEquilibrium, IsFixedPoint]

/-! ## Stability Definitions -/

/-- Lyapunov stability: trajectories starting near x* stay near x*. -/
def IsLyapunovStable [Nonempty Q] (C : MeanFieldChoreography Q) (x : Q → ℝ)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) : Prop :=
  IsEquilibrium C x ∧
  ∀ ε > 0, ∃ δ > 0, ∀ x₀ ∈ Simplex Q,
    ‖x₀ - x‖ < δ → ∀ t ≥ 0,
      ‖ODESolution C x₀ hcons hboundary t - x‖ < ε

/-- Asymptotic stability: trajectories converge to x*. -/
def IsAsymptoticallyStable' [Nonempty Q] (C : MeanFieldChoreography Q) (x : Q → ℝ)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) : Prop :=
  IsLyapunovStable C x hcons hboundary ∧
  ∃ δ > 0, ∀ x₀ ∈ Simplex Q,
    ‖x₀ - x‖ < δ →
      Filter.Tendsto (ODESolution C x₀ hcons hboundary) Filter.atTop (nhds x)

/-! ## Linear Stability -/

/-- The Jacobian of the drift at a point (Fréchet derivative). -/
def Jacobian [DecidableEq Q] (F : DriftFunction Q) (x : Q → ℝ) : (Q → ℝ) →L[ℝ] (Q → ℝ) :=
  fderiv ℝ F x

/-- Jacobian as a real matrix via the standard Pi basis. -/
def JacobianMatrix [DecidableEq Q] (F : DriftFunction Q) (x : Q → ℝ) :
    Matrix Q Q ℝ :=
  -- Represent the Fréchet derivative as a matrix in the standard basis
  LinearMap.toMatrix (Pi.basisFun ℝ Q) (Pi.basisFun ℝ Q)
    (Jacobian F x).toLinearMap

/-- Complexified Jacobian matrix (entries lifted ℝ → ℂ). -/
def JacobianComplex [DecidableEq Q] (F : DriftFunction Q) (x : Q → ℝ) :
    Matrix Q Q ℂ :=
  -- Apply algebraMap ℝ ℂ entry-wise to get complex matrix
  (JacobianMatrix F x).map (algebraMap ℝ ℂ)

/-- Hurwitz stability: all eigenvalues of the complexified Jacobian
    have strictly negative real part.

    Uses `Module.End.HasEigenvalue` on the linear endomorphism
    induced by the complexified Jacobian matrix via `Matrix.toLin'`. -/
def IsHurwitz [DecidableEq Q] (F : DriftFunction Q) (x : Q → ℝ) : Prop :=
  -- Every complex eigenvalue of the Jacobian has Re(μ) < 0
  ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (JacobianComplex F x)) μ → μ.re < 0

/-- Linear stability: fixed point with Hurwitz-stable Jacobian. -/
def IsLinearlyStable [DecidableEq Q] (F : DriftFunction Q) (x : Q → ℝ) : Prop :=
  IsFixedPoint F x ∧ IsHurwitz F x

/-! ## Lyapunov Functions -/

/-- A Lyapunov function certificate for stability at a fixed point.
    V is continuous, zero at x*, positive elsewhere, and non-increasing
    along ODE trajectories. -/
structure LyapunovData (F : DriftFunction Q) (x : Q → ℝ) where
  /-- The Lyapunov function -/
  V : (Q → ℝ) → ℝ
  /-- V is continuous -/
  V_cont : Continuous V
  /-- V vanishes at the equilibrium -/
  V_zero : V x = 0
  /-- V is positive away from the equilibrium -/
  V_pos : ∀ y, y ≠ x → 0 < V y
  /-- V is non-negative everywhere -/
  V_nonneg : ∀ y, 0 ≤ V y
  /-- V is non-increasing along ODE trajectories -/
  V_decreasing : ∀ (sol : ℝ → (Q → ℝ)),
    (∀ t ≥ 0, HasDerivAt sol (F (sol t)) t) →
    ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → V (sol t₂) ≤ V (sol t₁)

/-- Strict Lyapunov function: V(sol t) → 0 along trajectories,
    which forces convergence to the equilibrium. -/
structure StrictLyapunovData (F : DriftFunction Q) (x : Q → ℝ)
    extends LyapunovData F x where
  /-- V converges to zero along any trajectory -/
  V_to_zero : ∀ (sol : ℝ → (Q → ℝ)),
    (∀ t ≥ 0, HasDerivAt sol (F (sol t)) t) →
    Filter.Tendsto (V ∘ sol) Filter.atTop (nhds 0)

end

end Gibbs.MeanField
