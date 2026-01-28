import Gibbs.MeanField.Rules
import Gibbs.MeanField.ODE

/-
The Problem. Given a target drift function F (the global choreography),
find local transition rates that produce F when aggregated.

This is the "projection" from global to local: we solve for rates r_i
such that driftFromRules(rules with rates r_i) = F.

The projection problem is: given stoichiometric templates (the "what"
of transitions) and a target drift F, find rate functions (the "how fast")
that make the rules produce F.

Solution Structure.
1. ProjectionProblem: target drift + rule templates
2. ProjectionSolution: rates satisfying the drift equation
3. Existence theorem (linear algebra conditions)
4. Correctness theorem (solution produces target)
-/

namespace Gibbs.MeanField

open scoped Classical

noncomputable section

/-! ## Projection Problem -/

/-- A projection problem: find rates for given rule templates
    that produce a target drift function. -/
structure ProjectionProblem (Q : Type*) [Fintype Q] where
  /-- The target drift function we want to achieve -/
  targetDrift : DriftFunction Q
  /-- Available rule templates (stoichiometric updates without rates) -/
  ruleTemplates : List (Q → ℤ)
  /-- Templates conserve (each sums to zero) -/
  templates_conserve : ∀ tmpl ∈ ruleTemplates, ∑ q, tmpl q = 0

namespace ProjectionProblem

variable {Q : Type*} [Fintype Q]

/-- Number of rule templates. -/
def numRules (P : ProjectionProblem Q) : ℕ := P.ruleTemplates.length

/-- Get a specific rule template by index. -/
def template (P : ProjectionProblem Q) (i : Fin P.numRules) : Q → ℤ :=
  P.ruleTemplates.get ⟨i.val, i.isLt⟩

end ProjectionProblem

/-! ## Projection Solution -/

/-- A solution to the projection problem: rate functions for each template. -/
structure ProjectionSolution (Q : Type*) [Fintype Q]
    (P : ProjectionProblem Q) where
  /-- Rate function for each rule template -/
  rates : Fin P.numRules → RateFunction Q
  /-- Rates are non-negative on the simplex -/
  rates_nonneg : ∀ i, (rates i).NonNeg
  /-- Rates produce the target drift -/
  produces_drift : ∀ x ∈ Simplex Q, ∀ q,
    ∑ i : Fin P.numRules, (P.template i q : ℝ) * rates i x = P.targetDrift x q

namespace ProjectionSolution

variable {Q : Type*} [Fintype Q] {P : ProjectionProblem Q}

/-- Convert a projection solution to a list of PopRules. -/
def toRules (sol : ProjectionSolution Q P) : List (PopRule Q) :=
  List.finRange P.numRules |>.map fun i => {
    update := P.template i
    rate := sol.rates i
  }

/-- The rules from a projection solution have the correct length. -/
theorem toRules_length (sol : ProjectionSolution Q P) :
    sol.toRules.length = P.numRules := by
  simp [toRules]

end ProjectionSolution

/-! ## Projection Correctness -/

/-- A projection solution produces the target drift. -/
theorem projection_correct {Q : Type*} [Fintype Q]
    (P : ProjectionProblem Q) (sol : ProjectionSolution Q P) :
    ∀ x ∈ Simplex Q, driftFromRules sol.toRules x = P.targetDrift x := by
  intro x hx
  ext q
  -- Unfold definitions and convert list sum to Fin sum
  simp only [driftFromRules, ProjectionSolution.toRules]
  simp only [List.map_map, Function.comp_def]
  -- Convert list sum to Finset sum using Fin.sum_univ_def
  rw [← Fin.sum_univ_def]
  -- Apply produces_drift
  exact sol.produces_drift x hx q

/-! ## Existence Conditions -/

/-- Templates are linearly independent (sufficient for unique solution). -/
def TemplatesIndependent {Q : Type*} [Fintype Q]
    (P : ProjectionProblem Q) : Prop :=
  LinearIndependent ℝ (fun i : Fin P.numRules => fun q => (P.template i q : ℝ))

/-- Templates span the conservation subspace.
    This is the subspace of vectors summing to zero. -/
def TemplatesSpan {Q : Type*} [Fintype Q]
    (P : ProjectionProblem Q) : Prop :=
  ∀ v : Q → ℝ, (∑ q, v q = 0) →
    ∃ coeffs : Fin P.numRules → ℝ,
      ∀ q, v q = ∑ i, coeffs i * (P.template i q : ℝ)

/-- Projection solution exists if drift decomposes with non-negative coefficients.
    Note: `TemplatesSpan` alone is insufficient — it gives linear but not
    conic decomposition. Non-negative rates require the drift to lie in the
    conic hull of the templates at every simplex point. -/
theorem projection_exists {Q : Type*} [Fintype Q] [DecidableEq Q]
    (P : ProjectionProblem Q)
    (hdecomp : ∀ x ∈ Simplex Q, ∃ coeffs : Fin P.numRules → ℝ,
      (∀ i, 0 ≤ coeffs i) ∧
      ∀ q, P.targetDrift x q = ∑ i, coeffs i * (P.template i q : ℝ)) :
    ∃ (_sol : ProjectionSolution Q P), True := by
  -- Build rates from Classical.choose of the decomposition
  have hspec := fun x (hx : x ∈ Simplex Q) => (hdecomp x hx).choose_spec
  refine ⟨⟨fun i x => if h : x ∈ Simplex Q then (hdecomp x h).choose i else 0,
    fun i x hx => ?_, fun x hx q => ?_⟩, trivial⟩
  · -- Non-negativity: chosen coefficients are non-negative
    simp only [dif_pos hx]; exact (hspec x hx).1 i
  · -- Produces drift: decomposition matches target
    simp only [dif_pos hx]
    have := (hspec x hx).2 q
    rw [this]; congr 1; ext i; ring

/-! ## Two-State Specialization -/

/-- For two-state systems (like Ising), there are exactly 2 templates:
    up → down and down → up. -/
def twoStateTemplates : List (TwoState → ℤ) :=
  [ -- up → down: decrease up, increase down
    fun q => match q with | .up => -1 | .down => 1,
    -- down → up: increase up, decrease down
    fun q => match q with | .up => 1 | .down => -1 ]

/-- Two-state templates conserve population. -/
theorem twoStateTemplates_conserve :
    ∀ tmpl ∈ twoStateTemplates, ∑ q, tmpl q = 0 := by
  -- Each template has +1 in one state and -1 in the other
  intro tmpl htmpl
  -- Case split on which template it is
  fin_cases htmpl <;> native_decide

/-- Projection problem for two-state systems. -/
def TwoStateProjection (F : DriftFunction TwoState) : ProjectionProblem TwoState where
  targetDrift := F
  ruleTemplates := twoStateTemplates
  templates_conserve := twoStateTemplates_conserve

/-- For two-state systems, rates can be directly computed from drift.
    Decompose F_down into positive and negative parts:
    α(x) = max(F_down(x), 0) and γ(x) = max(-F_down(x), 0). -/
theorem twoState_projection_formula (F : DriftFunction TwoState)
    (_hcons : DriftFunction.Conserves F) :
    ∃ (α γ : RateFunction TwoState),
      (∀ x ∈ Simplex TwoState, F x TwoState.down = α x - γ x) ∧
      (∀ x ∈ Simplex TwoState, 0 ≤ α x) ∧
      (∀ x ∈ Simplex TwoState, 0 ≤ γ x) := by
  -- Positive/negative part decomposition: f = f⁺ - f⁻
  refine ⟨fun x => max (F x .down) 0, fun x => max (-(F x .down)) 0,
    fun x _ => ?_, fun x _ => le_max_right _ _, fun x _ => le_max_right _ _⟩
  -- f = max(f,0) - max(-f,0) by case split on sign
  rcases le_or_gt 0 (F x .down) with h | h
  · simp [max_eq_left h, max_eq_right (by linarith : -(F x .down) ≤ 0)]
  · simp [max_eq_right (by linarith : F x .down ≤ 0),
          max_eq_left (by linarith : 0 ≤ -(F x .down))]

end

end Gibbs.MeanField
