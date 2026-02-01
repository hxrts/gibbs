import Gibbs.MeanField.Choreography

/-!
# Population Transition Rules

Microscopic dynamics are specified by transition rules, each with a
stoichiometric update (which states gain or lose agents) and a rate function
(how fast the transition fires, depending on the current distribution). The
macroscopic drift is the sum over all rules: F(x)_q = sum_r update_r(q) *
rate_r(x). This is the standard generator for density-dependent continuous-time
Markov chains.

This file defines `PopRule`, the specialized `BinaryRule` for pairwise
interactions, derives `driftFromRules`, and proves the resulting drift conserves
probability.
-/

namespace Gibbs.MeanField

open scoped Classical

noncomputable section

/-! ## Population Rules -/

/-- A population rule specifies a single transition type.
    - update: change in counts for each state (stoichiometry)
    - rate: state-dependent transition rate -/
structure PopRule (Q : Type*) where
  /-- Stoichiometric update: net change in each state's count -/
  update : Q → ℤ
  /-- Rate function: depends on current population state -/
  rate : RateFunction Q

namespace PopRule

variable {Q : Type*} [Fintype Q]

/-- A rule conserves total population iff updates sum to zero. -/
def Conserves (r : PopRule Q) : Prop :=
  ∑ q, r.update q = 0

/-- A rule has non-negative rate on the simplex. -/
def HasNonNegRate (r : PopRule Q) : Prop :=
  r.rate.NonNeg

/-- Apply a rule's update to an empirical measure (for population size N). -/
def applyTo (r : PopRule Q) (x : Q → ℝ) (N : ℕ) : Q → ℝ :=
  fun q => x q + (r.update q : ℝ) / N

/-- Create a rule with constant rate. -/
def withConstRate (update : Q → ℤ) (c : ℝ) : PopRule Q where
  update := update
  rate := RateFunction.const c

/-! ## Boundary Nonnegativity -/

/-- Rule boundary nonnegativity: if a component is zero, this rule's
    contribution is non-negative. -/
def BoundaryNonneg (r : PopRule Q) : Prop :=
  -- At a zero component, the rule cannot push further negative.
  ∀ x ∈ Simplex Q, ∀ q, x q = 0 → 0 ≤ (r.update q : ℝ) * r.rate x

end PopRule

/-! ## Binary Interaction Rules -/

/-- A binary interaction rule: two agents meet and may change state.
    Common pattern: agent in state pre1 meets agent in state pre2,
    they transition to post1 and post2 respectively. -/
structure BinaryRule (Q : Type*) where
  /-- Pre-state of first agent -/
  pre1 : Q
  /-- Pre-state of second agent -/
  pre2 : Q
  /-- Post-state of first agent -/
  post1 : Q
  /-- Post-state of second agent -/
  post2 : Q
  /-- Rate function for this interaction -/
  rate : RateFunction Q

namespace BinaryRule

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Convert a binary rule to a population rule.
    The stoichiometry removes agents from pre-states and adds to post-states. -/
def toPopRule (r : BinaryRule Q) : PopRule Q where
  update := fun q =>
    (if q = r.post1 then 1 else 0) + (if q = r.post2 then 1 else 0)
    - (if q = r.pre1 then 1 else 0) - (if q = r.pre2 then 1 else 0)
  rate := r.rate

/-- Binary rules conserve population (two agents in, two agents out). -/
theorem toPopRule_conserves (r : BinaryRule Q) : r.toPopRule.Conserves := by
  simp only [PopRule.Conserves, toPopRule]
  -- Sum over all q: each +1 is matched by a -1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- Mass-action rate: proportional to product of fractions in pre-states.
    This is the standard rate for well-mixed populations. -/
def massActionRate (r : BinaryRule Q) (k : ℝ) : RateFunction Q :=
  -- Scale by the product of pre-state fractions.
  fun x => k * x r.pre1 * x r.pre2

omit [DecidableEq Q] in
/-- Mass-action rates are non-negative on the simplex when `k ≥ 0`. -/
theorem massActionRate_nonneg (r : BinaryRule Q) (k : ℝ) (hk : 0 ≤ k) :
    RateFunction.NonNeg (massActionRate r k) := by
  -- Use non-negativity of k and simplex components.
  intro x hx
  have h1 : 0 ≤ x r.pre1 := hx.1 _
  have h2 : 0 ≤ x r.pre2 := hx.1 _
  have hmul : 0 ≤ x r.pre1 * x r.pre2 := mul_nonneg h1 h2
  have hnonneg : 0 ≤ k * (x r.pre1 * x r.pre2) := mul_nonneg hk hmul
  simpa [massActionRate, mul_assoc] using hnonneg

/-- Create a binary rule with mass-action kinetics. -/
def withMassAction (pre1 pre2 post1 post2 : Q) (k : ℝ) : BinaryRule Q where
  -- Package the interaction with mass-action rate.
  pre1 := pre1
  pre2 := pre2
  post1 := post1
  post2 := post2
  rate := massActionRate ⟨pre1, pre2, post1, post2, RateFunction.const 0⟩ k

/-! ## Boundary Nonnegativity (Binary Rules) -/

omit [Fintype Q] in
/-- Helper: update is non-negative away from the pre-states. -/
private theorem toPopRule_update_nonneg_of_ne_pre (r : BinaryRule Q)
    {q : Q} (hpre1 : q ≠ r.pre1) (hpre2 : q ≠ r.pre2) :
    0 ≤ (r.toPopRule.update q : ℝ) := by
  -- With pre-terms zero, update is a sum of post indicators.
  have hpost1 :
      0 ≤ (if q = r.post1 then (1 : ℤ) else 0) := by
    -- Indicators are 0 or 1.
    by_cases hpost1 : q = r.post1 <;> simp [hpost1]
  have hpost2 :
      0 ≤ (if q = r.post2 then (1 : ℤ) else 0) := by
    -- Indicators are 0 or 1.
    by_cases hpost2 : q = r.post2 <;> simp [hpost2]
  have hsum : 0 ≤
      (if q = r.post1 then (1 : ℤ) else 0) +
        (if q = r.post2 then 1 else 0) := add_nonneg hpost1 hpost2
  -- Rewrite update using the pre-state assumptions and cast to ℝ.
  have hupdate : (0 : ℤ) ≤ r.toPopRule.update q := by
    simpa [BinaryRule.toPopRule, hpre1, hpre2] using hsum
  exact_mod_cast hupdate

/-- Mass-action binary rules are boundary-nonnegative. -/
theorem withMassAction_boundary_nonneg
    (pre1 pre2 post1 post2 : Q) (k : ℝ) (hk : 0 ≤ k) :
    PopRule.BoundaryNonneg (BinaryRule.toPopRule (withMassAction pre1 pre2 post1 post2 k)) := by
  -- Split on whether `q` is a pre-state; otherwise use nonneg update and rate.
  intro x hx q hq
  by_cases hpre1 : q = pre1
  · subst hpre1
    -- If q is pre1, x q = 0 forces rate = 0.
    simp [BinaryRule.withMassAction, BinaryRule.massActionRate, BinaryRule.toPopRule, hq]
  · by_cases hpre2 : q = pre2
    · subst hpre2
      -- If q is pre2, x q = 0 forces rate = 0.
      simp [BinaryRule.withMassAction, BinaryRule.massActionRate, BinaryRule.toPopRule, hq]
    · have hrate : 0 ≤ (withMassAction pre1 pre2 post1 post2 k).rate x := by
        -- Rate is k * x pre1 * x pre2, non-negative on the simplex.
        have hnonneg :=
          massActionRate_nonneg (r := withMassAction pre1 pre2 post1 post2 k) k hk x hx
        simpa [BinaryRule.withMassAction, BinaryRule.massActionRate] using hnonneg
      have hupdate :
          0 ≤ ((withMassAction pre1 pre2 post1 post2 k).toPopRule.update q : ℝ) := by
        -- Pre-terms vanish since q is not a pre-state.
        exact toPopRule_update_nonneg_of_ne_pre (r := withMassAction pre1 pre2 post1 post2 k)
          hpre1 hpre2
      have hmul : 0 ≤
          ((withMassAction pre1 pre2 post1 post2 k).toPopRule.update q : ℝ) *
            (withMassAction pre1 pre2 post1 post2 k).rate x := mul_nonneg hupdate hrate
      -- Reassociate to match the drift contribution.
      simpa [BinaryRule.withMassAction, BinaryRule.toPopRule] using hmul

end BinaryRule

/-! ## Unary Rules -/

/-- A unary rule: single agent changes state spontaneously. -/
structure UnaryRule (Q : Type*) where
  /-- Pre-state -/
  pre : Q
  /-- Post-state -/
  post : Q
  /-- Rate function -/
  rate : RateFunction Q

namespace UnaryRule

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Convert a unary rule to a population rule. -/
def toPopRule (r : UnaryRule Q) : PopRule Q where
  update := fun q =>
    (if q = r.post then 1 else 0) - (if q = r.pre then 1 else 0)
  rate := r.rate

/-- Unary rules conserve population (one agent in, one agent out). -/
theorem toPopRule_conserves (r : UnaryRule Q) : r.toPopRule.Conserves := by
  -- The +1 and -1 contributions cancel in the sum.
  simp only [PopRule.Conserves, toPopRule]
  simp only [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-! ## Mass-Action Unary Rules -/

/-- Mass-action rate: proportional to the pre-state fraction. -/
def massActionRate (r : UnaryRule Q) (k : ℝ) : RateFunction Q :=
  -- Scale by the pre-state fraction.
  fun x => k * x r.pre

omit [DecidableEq Q] in
/-- Unary mass-action rates are non-negative on the simplex when `k ≥ 0`. -/
theorem massActionRate_nonneg (r : UnaryRule Q) (k : ℝ) (hk : 0 ≤ k) :
    RateFunction.NonNeg (massActionRate r k) := by
  -- Use non-negativity of k and simplex component.
  intro x hx
  have hpre : 0 ≤ x r.pre := hx.1 _
  have hnonneg : 0 ≤ k * x r.pre := mul_nonneg hk hpre
  simpa [massActionRate] using hnonneg

/-- Create a unary rule with mass-action kinetics. -/
def withMassAction (pre post : Q) (k : ℝ) : UnaryRule Q where
  -- Package the unary transition with mass-action rate.
  pre := pre
  post := post
  rate := massActionRate ⟨pre, post, RateFunction.const 0⟩ k

/-! ## Boundary Nonnegativity (Unary Rules) -/

omit [Fintype Q] in
/-- Helper: update is non-negative away from the pre-state. -/
private theorem toPopRule_update_nonneg_of_ne_pre (r : UnaryRule Q)
    {q : Q} (hpre : q ≠ r.pre) :
    0 ≤ (r.toPopRule.update q : ℝ) := by
  -- With the pre-term zero, update is a post-indicator.
  have hsum : 0 ≤ (if q = r.post then (1 : ℤ) else 0) := by
    -- The indicator is 0 or 1.
    by_cases hpost : q = r.post <;> simp [hpost]
  have hupdate : (0 : ℤ) ≤ r.toPopRule.update q := by
    simpa [UnaryRule.toPopRule, hpre] using hsum
  exact_mod_cast hupdate

/-- Mass-action unary rules are boundary-nonnegative. -/
theorem withMassAction_boundary_nonneg
    (pre post : Q) (k : ℝ) (hk : 0 ≤ k) :
    PopRule.BoundaryNonneg (UnaryRule.toPopRule (withMassAction pre post k)) := by
  -- Split on whether `q` is the pre-state; otherwise use nonneg update and rate.
  intro x hx q hq
  by_cases hpre : q = pre
  · subst hpre
    -- If q is pre, x q = 0 forces rate = 0.
    simp [UnaryRule.withMassAction, UnaryRule.massActionRate, UnaryRule.toPopRule, hq]
  · have hrate : 0 ≤ (withMassAction pre post k).rate x := by
      -- Rate is k * x pre, non-negative on the simplex.
      have hnonneg :=
        massActionRate_nonneg (r := withMassAction pre post k) k hk x hx
      simpa [UnaryRule.withMassAction, UnaryRule.massActionRate] using hnonneg
    have hupdate :
        0 ≤ ((withMassAction pre post k).toPopRule.update q : ℝ) := by
      -- Pre-term vanishes since q is not the pre-state.
      exact toPopRule_update_nonneg_of_ne_pre (r := withMassAction pre post k) hpre
    have hmul :
        0 ≤ ((withMassAction pre post k).toPopRule.update q : ℝ) *
          (withMassAction pre post k).rate x := mul_nonneg hupdate hrate
    -- Reassociate to match the drift contribution.
    simpa [UnaryRule.withMassAction, UnaryRule.toPopRule] using hmul

end UnaryRule

/-! ## Helper: List sum lemmas -/

/-- Swap order of summation for list and finset. -/
theorem List.sum_map_sum_map {α β γ : Type*} [AddCommMonoid γ] [Fintype β]
    (l : List α) (f : α → β → γ) :
    (l.map fun a => ∑ b, f a b).sum = ∑ b, (l.map fun a => f a b).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← Finset.sum_add_distrib]

/-! ## Drift from Rules -/

/-- Compute drift function from a list of population rules.
    F(x)_q = Σ_r update_r(q) * rate_r(x) -/
def driftFromRules {Q : Type*} [Fintype Q]
    (rules : List (PopRule Q)) : DriftFunction Q :=
  fun x q => (rules.map fun r => (r.update q : ℝ) * r.rate x).sum

/-! ## Drift Boundary Lemma -/

/-- Drift from rules is boundary-nonnegative if each rule is boundary-nonnegative. -/
theorem driftFromRules_boundary_nonneg {Q : Type*} [Fintype Q]
    (rules : List (PopRule Q)) (hbound : ∀ r ∈ rules, PopRule.BoundaryNonneg r) :
    ∀ x ∈ Simplex Q, ∀ q, x q = 0 → 0 ≤ driftFromRules rules x q := by
  -- Prove by induction over rules, summing non-negative contributions.
  intro x hx q hq
  induction rules with
  | nil =>
    -- Empty list contributes 0.
    simp [driftFromRules]
  | cons r rs ih =>
    -- Split head/tail and use non-negativity of each part.
    have hr : PopRule.BoundaryNonneg r := hbound r (List.Mem.head rs)
    have hrs : ∀ r' ∈ rs, PopRule.BoundaryNonneg r' :=
      fun r' hr' => hbound r' (List.Mem.tail r hr')
    have hhead : 0 ≤ (r.update q : ℝ) * r.rate x := hr x hx q hq
    have htail : 0 ≤ driftFromRules rs x q := ih hrs
    have hsum :
        driftFromRules (r :: rs) x q =
          (r.update q : ℝ) * r.rate x + driftFromRules rs x q := by
      -- Expand the list sum to isolate the head.
      simp [driftFromRules]
    -- Combine the non-negativity of head and tail.
    rw [hsum]
    exact add_nonneg hhead htail

/-- Helper: sum over a single rule is zero if it conserves. -/
theorem rule_sum_zero {Q : Type*} [Fintype Q]
    (r : PopRule Q) (x : Q → ℝ) (hc : r.Conserves) :
    ∑ q, (r.update q : ℝ) * r.rate x = 0 := by
  -- Factor out rate x: = (Σ_q update q) * rate x = 0 * rate x = 0
  rw [← Finset.sum_mul]
  have h1 : (∑ q, (r.update q : ℝ)) = ((∑ q, r.update q) : ℤ) := by
    rw [Int.cast_sum]
  rw [h1, hc, Int.cast_zero, zero_mul]

/-- Drift from conserving rules conserves probability. -/
theorem driftFromRules_conserves {Q : Type*} [Fintype Q]
    (rules : List (PopRule Q)) (hcons : ∀ r ∈ rules, r.Conserves) :
    DriftFunction.Conserves (driftFromRules rules) := by
  intro x _
  simp only [driftFromRules]
  -- Swap order of summation: Σ_q Σ_r = Σ_r Σ_q
  rw [← List.sum_map_sum_map]
  -- Each rule's contribution sums to 0 by rule_sum_zero
  -- Prove by induction that sum of list of zeros is zero
  induction rules with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hr_mem : r ∈ r :: rs := List.Mem.head rs
    have hrs_sub : ∀ r' ∈ rs, r'.Conserves :=
      fun r' hr' => hcons r' (List.Mem.tail r hr')
    rw [rule_sum_zero r x (hcons r hr_mem), ih hrs_sub, add_zero]

/-! ## Choreography from Rules -/

namespace MeanFieldChoreography

variable {Q : Type*} [Fintype Q]

/-- Build a choreography from rules, deriving conservation and boundary properties. -/
def fromRules (rules : List (PopRule Q))
    (hLip : ∃ L, DriftFunction.IsLipschitz (driftFromRules rules) L)
    (hcons : ∀ r ∈ rules, r.Conserves)
    (hbound : ∀ r ∈ rules, PopRule.BoundaryNonneg r) :
    MeanFieldChoreography Q :=
  -- Package drift and invariants derived from the rule list.
  { drift := driftFromRules rules
    drift_lipschitz := hLip
    drift_conserves := driftFromRules_conserves rules hcons
    boundary_nonneg := driftFromRules_boundary_nonneg rules hbound }

end MeanFieldChoreography

end

end Gibbs.MeanField
