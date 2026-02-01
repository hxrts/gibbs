import Gibbs.MeanField.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Mean-Field Choreography

A mean-field choreography specifies the global constraints on population
dynamics: a drift function F on the simplex that is probability-conserving
(components sum to zero) and Lipschitz (ensuring ODE well-posedness). These
two conditions guarantee that dx/dt = F(x) has a unique solution that remains
on the simplex for all time.

This file defines rate functions, the `MeanFieldChoreography` bundle,
equilibrium (fixed) points, and linearized stability conditions.
-/

namespace Gibbs.MeanField

open scoped Classical

noncomputable section

/-! ## Rate Functions -/

/-- A rate function maps population state to a transition rate.
    Rates depend on the current distribution, not individual agents. -/
def RateFunction (Q : Type*) := (Q → ℝ) → ℝ

namespace RateFunction

variable {Q : Type*} [Fintype Q]

/-- A rate function is non-negative on the simplex. -/
def NonNeg (r : RateFunction Q) : Prop :=
  ∀ x ∈ Simplex Q, 0 ≤ r x

/-- A rate function is Lipschitz with constant L.
    Required for fluid limit theorem. -/
def IsLipschitz (r : RateFunction Q) (L : ℝ) : Prop :=
  ∀ x y, x ∈ Simplex Q → y ∈ Simplex Q →
    |r x - r y| ≤ L * ‖x - y‖

/-- A rate function is bounded on the simplex. -/
def IsBounded (r : RateFunction Q) (B : ℝ) : Prop :=
  ∀ x ∈ Simplex Q, |r x| ≤ B

/-- Constant rate function. -/
def const (c : ℝ) : RateFunction Q := fun _ => c

theorem const_nonneg {c : ℝ} (hc : 0 ≤ c) : NonNeg (const c : RateFunction Q) := by
  intro x _
  exact hc

theorem const_lipschitz (c : ℝ) : IsLipschitz (const c : RateFunction Q) 0 := by
  intro x y _ _
  simp [const]

end RateFunction

/-! ## Drift Functions -/

/-- A drift function specifies the rate of change for each state.
    The ODE is dx/dt = drift(x). -/
def DriftFunction (Q : Type*) := (Q → ℝ) → (Q → ℝ)

namespace DriftFunction

variable {Q : Type*} [Fintype Q]

/-- Drift conserves probability: components sum to zero.
    This ensures the simplex is invariant under the flow. -/
def Conserves (F : DriftFunction Q) : Prop :=
  ∀ x ∈ Simplex Q, ∑ q, F x q = 0

/-- Drift is Lipschitz in sup-norm. -/
def IsLipschitz (F : DriftFunction Q) (L : ℝ) : Prop :=
  ∀ x y, x ∈ Simplex Q → y ∈ Simplex Q →
    ‖F x - F y‖ ≤ L * ‖x - y‖

/-- Zero drift (equilibrium everywhere). -/
def zero : DriftFunction Q := fun _ _ => 0

theorem zero_conserves : Conserves (zero : DriftFunction Q) := by
  intro x _
  -- zero x q = 0 for all q, so sum is 0
  simp only [zero, Finset.sum_const_zero]

theorem zero_lipschitz : IsLipschitz (zero : DriftFunction Q) 0 := by
  intro x y _ _
  -- zero x = zero y = (fun _ => 0), so their difference is 0
  have h : zero x - zero y = 0 := by
    ext q
    simp only [zero, Pi.sub_apply, sub_self, Pi.zero_apply]
  simp only [h, norm_zero, zero_mul, le_refl]

end DriftFunction

/-! ## Mean-Field Choreography -/

/-- A mean-field choreography specifies the global dynamics of a population.
    It packages a drift function with its required properties. -/
structure MeanFieldChoreography (Q : Type*) [Fintype Q] where
  /-- The drift function: dx/dt = drift(x) -/
  drift : DriftFunction Q
  /-- Drift is Lipschitz (ensures ODE well-posedness) -/
  drift_lipschitz : ∃ L, DriftFunction.IsLipschitz drift L
  /-- Drift conserves probability (simplex is invariant) -/
  drift_conserves : DriftFunction.Conserves drift
  /-- At boundary x_q = 0, drift pushes inward (ensures non-negativity).
      Together with conservation, this implies simplex forward-invariance. -/
  boundary_nonneg : ∀ x ∈ Simplex Q, ∀ q, x q = 0 → 0 ≤ drift x q

namespace MeanFieldChoreography

variable {Q : Type*} [Fintype Q]

/-- The trivial choreography with zero drift. -/
def trivial : MeanFieldChoreography Q where
  drift := DriftFunction.zero
  drift_lipschitz := ⟨0, DriftFunction.zero_lipschitz⟩
  drift_conserves := DriftFunction.zero_conserves
  boundary_nonneg := fun _ _ _ _ => le_refl 0

/-- Extract Lipschitz constant (existence witness). -/
def lipschitzConst (C : MeanFieldChoreography Q) : ℝ :=
  C.drift_lipschitz.choose

end MeanFieldChoreography

/-! ## Equilibrium -/

/-- A point x* is an equilibrium if drift(x*) = 0. -/
def IsEquilibrium {Q : Type*} [Fintype Q]
    (C : MeanFieldChoreography Q) (x : Q → ℝ) : Prop :=
  x ∈ Simplex Q ∧ C.drift x = 0

/-- The set of all equilibria of a choreography. -/
def Equilibria {Q : Type*} [Fintype Q]
    (C : MeanFieldChoreography Q) : Set (Q → ℝ) :=
  { x | IsEquilibrium C x }

namespace MeanFieldChoreography

variable {Q : Type*} [Fintype Q]

/-- The trivial choreography has all simplex points as equilibria. -/
theorem trivial_all_equilibria :
    ∀ x ∈ Simplex Q, IsEquilibrium (trivial : MeanFieldChoreography Q) x := by
  intro x hx
  constructor
  · exact hx
  · rfl

end MeanFieldChoreography

/-! ## Stability (Definitions Only) -/

/-- An equilibrium is stable if nearby trajectories stay nearby.
    Full definition requires ODE solutions (see ODE.lean). -/
def IsStable {Q : Type*} [Fintype Q]
    (C : MeanFieldChoreography Q) (x : Q → ℝ) : Prop :=
  IsEquilibrium C x ∧
  ∀ ε > 0, ∃ δ > 0, ∀ x₀ ∈ Simplex Q, ‖x₀ - x‖ < δ →
    ∀ sol : ℝ → (Q → ℝ),
      (sol 0 = x₀ ∧ Continuous sol ∧
        ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t ∧ sol t ∈ Simplex Q) →
      ∀ t ≥ 0, ‖sol t - x‖ < ε

/-- An equilibrium is asymptotically stable if trajectories converge to it. -/
def IsAsymptoticallyStable {Q : Type*} [Fintype Q]
    (C : MeanFieldChoreography Q) (x : Q → ℝ) : Prop :=
  IsStable C x ∧
  ∀ ε > 0, ∃ δ > 0, ∀ x₀ ∈ Simplex Q, ‖x₀ - x‖ < δ →
    ∀ sol : ℝ → (Q → ℝ),
      (sol 0 = x₀ ∧ Continuous sol ∧
        ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t ∧ sol t ∈ Simplex Q) →
      Filter.Tendsto sol Filter.atTop (nhds x)

end

end Gibbs.MeanField
