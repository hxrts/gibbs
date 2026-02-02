import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Shannon Entropy and KL Divergence

Foundational information-theoretic definitions for finite distributions.
This file is intentionally self-contained (no Gibbs dependencies) so it can
serve as the base layer for channel and consensus bridges.
-/

namespace Gibbs.Hamiltonian.Entropy

noncomputable section

open scoped BigOperators Classical

variable {α : Type} [Fintype α]

/-! ## Distributions -/

/-- Subtype for probability distributions on a finite type. -/
structure Distribution (α : Type*) [Fintype α] where
  pmf : α → ℝ
  nonneg : ∀ a, 0 ≤ pmf a
  sum_one : ∑ a, pmf a = 1

/-! ## Shannon Entropy -/

/-- Shannon entropy: H(p) = -∑ pᵢ log pᵢ with convention 0 log 0 = 0. -/
def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ a, if p a = 0 then 0 else p a * Real.log (p a)

/-- H(p) ≥ 0 for distributions. -/
theorem shannonEntropy_nonneg {α : Type*} [Fintype α]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    0 ≤ shannonEntropy p := by
  classical
  unfold shannonEntropy
  have hterm : ∀ a, (if p a = 0 then 0 else p a * Real.log (p a)) ≤ 0 := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    · have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
      have hpa_le_one : p a ≤ 1 := by
        have hle : p a ≤ ∑ b, p b := by
          have hmem : a ∈ (Finset.univ : Finset α) := by simp
          exact Finset.single_le_sum (f := p) (fun _ _ => hp_nn _) hmem
        simpa [hp_sum] using hle
      have hlog : Real.log (p a) ≤ 0 := by
        have hlog' : Real.log (p a) ≤ Real.log 1 :=
          Real.log_le_log hpa_pos (by simpa using hpa_le_one)
        simpa using hlog'
      have hmul : p a * Real.log (p a) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hp_nn a) hlog
      simpa [hpa] using hmul
  have hsum : ∑ a, (if p a = 0 then 0 else p a * Real.log (p a)) ≤ 0 := by
    simpa using
      (Finset.sum_nonpos (s := (Finset.univ : Finset α)) (fun a _ => hterm a))
  linarith

/-- Entropy of a deterministic distribution is zero. -/
theorem shannonEntropy_deterministic {α : Type*} [Fintype α]
    (p : α → ℝ) (a₀ : α) (hp : ∀ a, p a = if a = a₀ then 1 else 0) :
    shannonEntropy p = 0 := by
  classical
  unfold shannonEntropy
  have hterm : ∀ a, (if p a = 0 then 0 else p a * Real.log (p a)) = 0 := by
    intro a
    by_cases h : a = a₀
    · subst h
      simp [hp]
    · have hp0 : p a = 0 := by simp [hp, h]
      simp [hp0]
  simp [hterm]

/-! ## Binary Entropy -/

/-- Binary entropy H₂(ε) = -ε log ε - (1-ε) log (1-ε). -/
def binaryEntropy (ε : ℝ) : ℝ :=
  - (if ε = 0 then 0 else ε * Real.log ε)
  - (if ε = 1 then 0 else (1 - ε) * Real.log (1 - ε))

/-! ## KL Divergence -/

/-- KL divergence: D_KL(p‖q) = ∑ pᵢ log(pᵢ/qᵢ) with 0 log 0 = 0. -/
def klDivergence {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, if p a = 0 then 0 else p a * Real.log (p a / q a)

/-- Gibbs inequality: D_KL(p‖q) ≥ 0. -/
theorem klDivergence_nonneg {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    0 ≤ klDivergence p q := by
  classical
  have hterm : ∀ a, p a - q a ≤ (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
    intro a
    by_cases hpa : p a = 0
    · have hq : 0 ≤ q a := hq_nn a
      simp [hpa, hq]
    · have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
      have hq_pos : 0 < q a := lt_of_le_of_ne (hq_nn a) (Ne.symm (habs a hpa))
      have hlog : Real.log (q a / p a) ≤ q a / p a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hq_pos hpa_pos)
      have hmul : -p a * Real.log (q a / p a) ≥ -p a * (q a / p a - 1) := by
        have hpneg : -p a ≤ 0 := by linarith [hp_nn a]
        exact mul_le_mul_of_nonpos_left hlog hpneg
      have hleft : -p a * Real.log (q a / p a) = p a * Real.log (p a / q a) := by
        have hlog1 : Real.log (q a / p a) = Real.log (q a) - Real.log (p a) :=
          Real.log_div (habs a hpa) hpa
        have hlog2 : Real.log (p a / q a) = Real.log (p a) - Real.log (q a) :=
          Real.log_div hpa (habs a hpa)
        calc
          -p a * Real.log (q a / p a)
              = -p a * (Real.log (q a) - Real.log (p a)) := by simp [hlog1]
          _ = p a * (Real.log (p a) - Real.log (q a)) := by ring
          _ = p a * Real.log (p a / q a) := by simp [hlog2]
      have hright : -p a * (q a / p a - 1) = p a - q a := by
        calc
          -p a * (q a / p a - 1) = -p a * (q a / p a) + p a := by ring
          _ = -(p a * (q a / p a)) + p a := by ring
          _ = -q a + p a := by field_simp [hpa]
          _ = p a - q a := by ring
      have hineq : p a - q a ≤ p a * Real.log (p a / q a) := by
        -- combine the transformed inequality
        have := hmul
        -- rewrite both sides
        simpa [hleft, hright] using this
      simpa [hpa] using hineq
  have hsum : ∑ a, (p a - q a) ≤ ∑ a, (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
    exact Finset.sum_le_sum (fun a _ => hterm a)
  have hsum_pq : ∑ a, (p a - q a) = 0 := by
    simp [hp_sum, hq_sum]
  have : 0 ≤ ∑ a, (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
    linarith [hsum, hsum_pq]
  simpa [klDivergence] using this

/-- D_KL(p ‖ uniform) = log|α| - H(p). -/
private theorem kl_uniform_eq {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (_hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    klDivergence p (fun _ => 1 / Fintype.card α) =
      Real.log (Fintype.card α) - shannonEntropy p := by
  unfold klDivergence shannonEntropy
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hu_ne : (1 : ℝ) / Fintype.card α ≠ 0 := ne_of_gt (div_pos one_pos hcard)
  -- p(a)/(1/|α|) = p(a)*|α|, so log(p(a)/(1/|α|)) = log(p(a)) + log|α|
  -- Σ p·log(p·|α|) = Σ p·log p + log|α|·Σ p = Σ p·log p + log|α|
  -- RHS = log|α| - (-Σ p·log p) = log|α| + Σ p·log p
  rw [sub_neg_eq_add]
  have hterms : ∀ a, (if p a = 0 then 0 else p a * Real.log (p a / (1 / ↑(Fintype.card α)))) =
      (if p a = 0 then 0 else p a * Real.log (p a)) +
      p a * Real.log (Fintype.card α) := by
    intro a
    by_cases hp : p a = 0
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      rw [div_div_eq_mul_div, div_one,
        Real.log_mul hp (ne_of_gt hcard)]
      ring
  simp_rw [hterms]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp_sum, one_mul, add_comm]

/-- H(p) ≤ log |α| (Shannon bound) via D_KL(p ‖ uniform) ≥ 0. -/
theorem shannonEntropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card α) := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hunif_nn : ∀ a : α, (0 : ℝ) ≤ 1 / Fintype.card α :=
    fun _ => div_nonneg zero_le_one (le_of_lt hcard)
  have hunif_sum : ∑ _ : α, (1 : ℝ) / Fintype.card α = 1 := by
    simp [Finset.card_univ]
  have habs : ∀ a : α, p a ≠ 0 → (1 : ℝ) / Fintype.card α ≠ 0 :=
    fun _ _ => ne_of_gt (div_pos one_pos hcard)
  have hkl := klDivergence_nonneg p _ hp_nn hp_sum hunif_nn hunif_sum habs
  rw [kl_uniform_eq p hp_nn hp_sum] at hkl
  linarith

/-- D_KL(p‖p) = 0: KL divergence of a distribution with itself vanishes. -/
private theorem klDivergence_self_eq_zero {α : Type*} [Fintype α]
    (p : α → ℝ) (_hp_nn : ∀ a, 0 ≤ p a) :
    klDivergence p p = 0 := by
  classical
  -- each term is p(a) * log(p(a)/p(a)) = p(a) * log 1 = 0
  unfold klDivergence
  refine Finset.sum_eq_zero ?_
  intro a _
  by_cases hpa : p a = 0
  · simp [hpa]
  · simp [hpa]

/-- Each KL term satisfies p(a)*log(p(a)/q(a)) ≥ p(a) - q(a). -/
private theorem kl_term_ge_diff {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hq_nn : ∀ a, 0 ≤ q a)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) (a : α) :
    p a - q a ≤ (if p a = 0 then 0 else p a * Real.log (p a / q a)) := by
  classical
  by_cases hpa : p a = 0
  · simp [hpa, hq_nn a]
  · -- log(q/p) ≤ q/p - 1, multiply by -p to flip
    have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
    have hq_pos : 0 < q a := lt_of_le_of_ne (hq_nn a) (Ne.symm (habs a hpa))
    have hlog : Real.log (q a / p a) ≤ q a / p a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hq_pos hpa_pos)
    have hmul : -p a * Real.log (q a / p a) ≥ p a - q a := by
      have hrhs : -p a * (q a / p a - 1) = p a - q a := by field_simp; ring
      linarith [mul_le_mul_of_nonpos_left hlog (by linarith : -p a ≤ 0)]
    -- -p*log(q/p) = p*log(p/q)
    have hflip : -p a * Real.log (q a / p a) = p a * Real.log (p a / q a) := by
      rw [Real.log_div (habs a hpa) hpa, Real.log_div hpa (habs a hpa)]; ring
    simp only [hpa, ↓reduceIte]
    linarith

/-- When D_KL = 0, each KL term equals p(a) - q(a). -/
private theorem kl_term_eq_diff_of_zero {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hkl : klDivergence p q = 0) (a : α) :
    (if p a = 0 then 0 else p a * Real.log (p a / q a)) = p a - q a := by
  classical
  -- Σ terms = 0, Σ(p-q) = 0, each term ≥ p-q, so each gap = 0
  have hkl' : ∑ b, (if p b = 0 then 0 else p b * Real.log (p b / q b)) = 0 := by
    simpa [klDivergence] using hkl
  have hpq : ∑ b, (p b - q b) = 0 := by
    have : ∑ b, p b - ∑ b, q b = 0 := by rw [hp_sum, hq_sum]; ring
    linarith [Finset.sum_sub_distrib (f := p) (g := q) (s := Finset.univ)]
  have hdiff :
      ∑ b, ((if p b = 0 then 0 else p b * Real.log (p b / q b)) - (p b - q b)) = 0 := by
    linarith [Finset.sum_sub_distrib
      (f := fun b => if p b = 0 then 0 else p b * Real.log (p b / q b))
      (g := fun b => p b - q b) (s := Finset.univ)]
  have hnn : ∀ b, 0 ≤
      (if p b = 0 then 0 else p b * Real.log (p b / q b)) - (p b - q b) :=
    fun b => by linarith [kl_term_ge_diff p q hp_nn hq_nn habs b]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn b)).mp hdiff
  linarith [hzero a (Finset.mem_univ a)]

/-- D_KL(p‖q) = 0 implies p = q pointwise. -/
private theorem klDivergence_eq_zero_imp_eq {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0)
    (hkl : klDivergence p q = 0) : p = q := by
  classical
  funext a
  have hterm := kl_term_eq_diff_of_zero p q hp_nn hp_sum hq_nn hq_sum habs hkl a
  by_cases hpa : p a = 0
  · -- term = 0 = p(a) - q(a), so q(a) = 0 = p(a)
    simp [hpa] at hterm; linarith
  · -- p(a)*log(p(a)/q(a)) = p(a) - q(a) implies p = q
    have hpa_pos : 0 < p a := lt_of_le_of_ne (hp_nn a) (Ne.symm hpa)
    have hq_pos : 0 < q a := lt_of_le_of_ne (hq_nn a) (Ne.symm (habs a hpa))
    simp only [hpa, ↓reduceIte] at hterm
    -- divide both sides by p(a) > 0: log(p/q) = 1 - q/p
    have hlog_pq : Real.log (p a / q a) = 1 - q a / p a := by
      have h := div_eq_div_iff (ne_of_gt hpa_pos) (ne_of_gt hpa_pos) |>.mpr (by linarith)
      field_simp at hterm ⊢; linarith
    -- equivalently log(q/p) = q/p - 1
    have hlog_qp : Real.log (q a / p a) = q a / p a - 1 := by
      rw [Real.log_div hpa (habs a hpa)] at hlog_pq
      rw [Real.log_div (habs a hpa) hpa]; linarith
    -- equality in log x ≤ x - 1 iff x = 1
    -- log(q/p) = q/p - 1 with q/p > 0 forces q/p = 1 (strict ineq for x ≠ 1)
    have hqp : q a / p a = 1 := by
      by_contra hne
      exact absurd hlog_qp (ne_of_lt (Real.log_lt_sub_one_of_pos
        (div_pos hq_pos hpa_pos) hne))
    rw [div_eq_one_iff_eq (ne_of_gt hpa_pos)] at hqp; linarith

/-- D_KL(p‖q) = 0 ↔ p = q. -/
theorem klDivergence_eq_zero_iff {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    klDivergence p q = 0 ↔ p = q := by
  constructor
  · -- D_KL = 0 → p = q
    exact klDivergence_eq_zero_imp_eq p q hp_nn hp_sum hq_nn hq_sum habs
  · -- p = q → D_KL = 0
    intro heq; subst heq; exact klDivergence_self_eq_zero p hp_nn

/-- KL divergence decomposes as cross-entropy minus entropy. -/
theorem klDivergence_eq_crossEntropy_sub {α : Type*} [Fintype α]
    (p q : α → ℝ) (_hp_nn : ∀ a, 0 ≤ p a) (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    klDivergence p q =
      (∑ a, if p a = 0 then 0 else - p a * Real.log (q a)) - shannonEntropy p := by
  classical
  unfold klDivergence shannonEntropy
  have hterm : ∀ a,
      (if p a = 0 then 0 else p a * Real.log (p a / q a)) =
        (if p a = 0 then 0 else p a * Real.log (p a)) +
        (if p a = 0 then 0 else - p a * Real.log (q a)) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    · have hqne : q a ≠ 0 := habs a hpa
      have hlog : Real.log (p a / q a) = Real.log (p a) - Real.log (q a) :=
        Real.log_div hpa hqne
      simp [hpa, hlog, mul_add, sub_eq_add_neg]
  calc
    ∑ a, (if p a = 0 then 0 else p a * Real.log (p a / q a))
        = ∑ a, ((if p a = 0 then 0 else p a * Real.log (p a)) +
                (if p a = 0 then 0 else - p a * Real.log (q a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact hterm a
    _ = (∑ a, (if p a = 0 then 0 else p a * Real.log (p a))) +
        (∑ a, (if p a = 0 then 0 else - p a * Real.log (q a))) := by
          simp [Finset.sum_add_distrib]
    _ = (∑ a, (if p a = 0 then 0 else - p a * Real.log (q a))) -
        (-(∑ a, (if p a = 0 then 0 else p a * Real.log (p a)))) := by
          ring
    _ = (∑ a, (if p a = 0 then 0 else - p a * Real.log (q a))) - shannonEntropy p := by
          simp [shannonEntropy]

/-! ## Marginals and Joint Distributions -/

/-- Marginal over the first variable. -/
def marginalFst {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, pXY (a, b)

/-- Marginal over the second variable. -/
def marginalSnd {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, pXY (a, b)

/-! ## Mutual Information -/
def mutualInfo {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : ℝ :=
  shannonEntropy (marginalFst pXY) + shannonEntropy (marginalSnd pXY) - shannonEntropy pXY

/-- Product of marginals is nonneg. -/
private theorem prodMarginals_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) (ab : α × β) :
    0 ≤ marginalFst pXY ab.1 * marginalSnd pXY ab.2 := by
  -- each marginal is a sum of nonneg terms
  exact mul_nonneg
    (Finset.sum_nonneg fun b _ => h_nn (ab.1, b))
    (Finset.sum_nonneg fun a _ => h_nn (a, ab.2))

/-- Product of marginals sums to 1. -/
private theorem prodMarginals_sum_one {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_sum : ∑ ab, pXY ab = 1) :
    ∑ ab : α × β, marginalFst pXY ab.1 * marginalSnd pXY ab.2 = 1 := by
  -- Σ_{a,b} pX(a)*pY(b) = (Σ_a pX(a)) * (Σ_b pY(b)) = 1 * 1
  have hfst : ∑ a, marginalFst pXY a = 1 := by
    simp only [marginalFst]
    rw [show ∑ a, ∑ b, pXY (a, b) = ∑ ab : α × β, pXY ab from
      (Fintype.sum_prod_type _).symm]
    exact h_sum
  have hsnd : ∑ b, marginalSnd pXY b = 1 := by
    simp only [marginalSnd]
    rw [show ∑ b, ∑ a, pXY (a, b) = ∑ ab : α × β, pXY ab from
      (Fintype.sum_prod_type_right _).symm]
    exact h_sum
  -- (Σ_a pX(a)) * (Σ_b pY(b)) = 1*1 = 1
  have hprod : ∑ ab : α × β, marginalFst pXY ab.1 * marginalSnd pXY ab.2 =
      (∑ a, marginalFst pXY a) * (∑ b, marginalSnd pXY b) := by
    have h1 : ∑ ab : α × β, marginalFst pXY ab.1 * marginalSnd pXY ab.2 =
        ∑ a, ∑ b, marginalFst pXY a * marginalSnd pXY b := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [h1]; simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]
  rw [hprod, hfst, hsnd, one_mul]

/-- Absolute continuity: pXY(a,b) > 0 implies pX(a)*pY(b) > 0. -/
private theorem prodMarginals_abs_cont {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) (ab : α × β) :
    pXY ab ≠ 0 → marginalFst pXY ab.1 * marginalSnd pXY ab.2 ≠ 0 := by
  intro hne
  -- pXY(a,b) > 0 ⇒ pX(a) ≥ pXY(a,b) > 0 and pY(b) ≥ pXY(a,b) > 0
  have hpos : 0 < pXY ab := lt_of_le_of_ne (h_nn ab) (Ne.symm hne)
  have hfst : 0 < marginalFst pXY ab.1 :=
    lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun b => pXY (ab.1, b)) (fun _ _ => h_nn _) (Finset.mem_univ ab.2))
  have hsnd : 0 < marginalSnd pXY ab.2 :=
    lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun a => pXY (a, ab.2)) (fun _ _ => h_nn _) (Finset.mem_univ ab.1))
  exact ne_of_gt (mul_pos hfst hsnd)

/-- Rewrite marginal entropy sum as a double sum with joint weights.
    Σ_a [if pX(a)=0 then 0 else pX(a)*log(pX(a))] =
    Σ_{a,b} [if pXY(a,b)=0 then 0 else pXY(a,b)*log(pX(a))]. -/
private theorem entropy_margFst_as_joint {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    (∑ a, if marginalFst pXY a = 0 then 0 else marginalFst pXY a *
      Real.log (marginalFst pXY a)) =
    ∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab *
      Real.log (marginalFst pXY ab.1) := by
  classical
  -- rewrite RHS as double sum
  have h_rhs : (∑ ab : α × β, if pXY ab = 0 then 0
      else pXY ab * Real.log (marginalFst pXY ab.1)) =
      ∑ a, ∑ b, (if pXY (a, b) = 0 then 0
      else pXY (a, b) * Real.log (marginalFst pXY a)) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [h_rhs]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hpa : marginalFst pXY a = 0
  · -- pX(a) = 0 ⇒ all pXY(a,b) = 0
    have hzero : ∀ b, pXY (a, b) = 0 := fun b =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => h_nn (a, b))).mp
        (by simp [marginalFst] at hpa; exact hpa) b (Finset.mem_univ b)
    simp [hpa, hzero]
  · -- pX(a) > 0: Σ_b pXY(a,b)*log(pX(a)) = pX(a)*log(pX(a))
    conv_rhs => rw [show ∑ b, (if pXY (a, b) = 0 then 0
      else pXY (a, b) * Real.log (marginalFst pXY a)) =
      ∑ b, pXY (a, b) * Real.log (marginalFst pXY a) from by
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h : pXY (a, b) = 0 <;> simp [h]]
    rw [← Finset.sum_mul]
    unfold marginalFst at hpa
    split
    · contradiction
    · rfl

/-- Same rewrite for the second marginal. -/
private theorem entropy_margSnd_as_joint {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    (∑ b, if marginalSnd pXY b = 0 then 0 else marginalSnd pXY b *
      Real.log (marginalSnd pXY b)) =
    ∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab *
      Real.log (marginalSnd pXY ab.2) := by
  classical
  have h_rhs : (∑ ab : α × β, if pXY ab = 0 then 0
      else pXY ab * Real.log (marginalSnd pXY ab.2)) =
      ∑ b, ∑ a, (if pXY (a, b) = 0 then 0
      else pXY (a, b) * Real.log (marginalSnd pXY b)) := by
    rw [← Finset.univ_product_univ, Finset.sum_product_right]
  rw [h_rhs]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hpb : marginalSnd pXY b = 0
  · have hzero : ∀ a, pXY (a, b) = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => h_nn (a, b))).mp
        (by simp [marginalSnd] at hpb; exact hpb) a (Finset.mem_univ a)
    simp [hpb, hzero]
  · conv_rhs => rw [show ∑ a, (if pXY (a, b) = 0 then 0
      else pXY (a, b) * Real.log (marginalSnd pXY b)) =
      ∑ a, pXY (a, b) * Real.log (marginalSnd pXY b) from by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : pXY (a, b) = 0 <;> simp [h]]
    rw [← Finset.sum_mul]
    unfold marginalSnd at hpb
    split
    · contradiction
    · rfl

/-- Mutual information equals KL divergence from joint to product of marginals. -/
private theorem mutualInfo_eq_klDivergence {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) :
    mutualInfo pXY = klDivergence pXY
      (fun ab => marginalFst pXY ab.1 * marginalSnd pXY ab.2) := by
  classical
  unfold mutualInfo shannonEntropy klDivergence
  rw [entropy_margFst_as_joint pXY h_nn, entropy_margSnd_as_joint pXY h_nn]
  -- goal: -Σ[pXY·log pX] + -Σ[pXY·log pY] - -Σ[pXY·log pXY] = Σ[pXY·log(pXY/(pX·pY))]
  -- combine into single sum
  rw [sub_neg_eq_add]
  simp only [← Finset.sum_neg_distrib (f := fun ab =>
    if pXY ab = 0 then 0 else pXY ab * Real.log (marginalFst pXY ab.1)),
    ← Finset.sum_neg_distrib (f := fun ab =>
    if pXY ab = 0 then 0 else pXY ab * Real.log (marginalSnd pXY ab.2)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ab _ => ?_
  by_cases h : pXY ab = 0
  · simp [h]
  · have hprod := prodMarginals_abs_cont pXY h_nn ab h
    simp only [h, ↓reduceIte]
    have hfst : marginalFst pXY ab.1 ≠ 0 := left_ne_zero_of_mul hprod
    have hsnd : marginalSnd pXY ab.2 ≠ 0 := right_ne_zero_of_mul hprod
    rw [Real.log_div h hprod, Real.log_mul hfst hsnd]
    ring

/-- Mutual information is nonnegative: I(X;Y) = D_KL(p_XY ‖ p_X ⊗ p_Y) ≥ 0. -/
theorem mutualInfo_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab)
    (h_sum : ∑ ab, pXY ab = 1) :
    0 ≤ mutualInfo pXY := by
  rw [mutualInfo_eq_klDivergence pXY h_nn]
  exact klDivergence_nonneg pXY _ h_nn h_sum
    (fun ab => prodMarginals_nonneg pXY h_nn ab)
    (prodMarginals_sum_one pXY h_sum)
    (fun ab => prodMarginals_abs_cont pXY h_nn ab)

/-! ## Conditional Entropy -/

/-- Conditional entropy H(X|Y) = H(X,Y) - H(Y). -/
def condEntropy {α β : Type*} [Fintype α] [Fintype β] (pXY : α × β → ℝ) : ℝ :=
  shannonEntropy pXY - shannonEntropy (marginalSnd pXY)

/-! ## Conditional Entropy Nonnegativity -/

/-- Conditional entropy is nonnegative. -/
theorem condEntropy_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) (_h_sum : ∑ ab, pXY ab = 1) :
    0 ≤ condEntropy pXY := by
  classical
  let pY : β → ℝ := marginalSnd pXY
  have hpY_nonneg : ∀ y, 0 ≤ pY y := by
    intro y
    unfold pY
    refine Finset.sum_nonneg ?_
    intro x hx
    exact h_nn (x, y)
  have hpXY_le : ∀ x y, pXY (x, y) ≤ pY y := by
    intro x y
    have hmem : x ∈ (Finset.univ : Finset α) := by simp
    have hle : pXY (x, y) ≤ ∑ x', pXY (x', y) := by
      exact Finset.single_le_sum (f := fun x' => pXY (x', y)) (fun _ _ => h_nn _) hmem
    simpa [pY] using hle
  have hpXY_eq_zero_of_pY_eq_zero :
      ∀ y, pY y = 0 → ∀ x, pXY (x, y) = 0 := by
    intro y hy x
    have hsum' : ∑ x', pXY (x', y) = 0 := by
      simpa [pY] using hy
    have hzero : ∀ x' ∈ (Finset.univ : Finset α), pXY (x', y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset α))
        (fun x' _ => h_nn (x', y))).1 hsum'
    exact hzero x (by simp)
  -- rewrite the second entropy term as a sum over (x,y)
  have hsum_log :
      (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) =
        (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) := by
    have hinner :
        (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) =
          ∑ y, ∑ x, if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y) := by
      refine Finset.sum_congr rfl ?_
      intro y hy
      by_cases hpy : pY y = 0
      · have hzero : ∀ x, pXY (x, y) = 0 := hpXY_eq_zero_of_pY_eq_zero y hpy
        simp [hpy, hzero]
      · have hterm :
            ∀ x, (if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y)) =
              pXY (x, y) * Real.log (pY y) := by
            intro x
            by_cases hxy : pXY (x, y) = 0
            · simp [hxy]
            · simp [hxy]
        have hcalc :
            (∑ x, if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y)) =
              pY y * Real.log (pY y) := by
          calc
            (∑ x, if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y))
                = (∑ x, pXY (x, y) * Real.log (pY y)) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    exact hterm x
            _ = (∑ x, pXY (x, y)) * Real.log (pY y) := by
                    simp [Finset.sum_mul]
            _ = pY y * Real.log (pY y) := by rfl
        simpa [hpy] using hcalc.symm
    have hsum_prod :
        (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) =
          ∑ y, ∑ x, if pXY (x, y) = 0 then 0 else pXY (x, y) * Real.log (pY y) := by
      simpa using (Fintype.sum_prod_type_right
        (f := fun ab : α × β => if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)))
    exact hinner.trans hsum_prod.symm
  -- expand conditional entropy and use the rewrite
  unfold condEntropy shannonEntropy
  have hrewrite :
      -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
        (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) =
        (∑ ab : α × β,
          (if pXY ab = 0 then 0
           else pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab)))) := by
    -- fold the Y-sum into a product sum, then combine termwise.
    have hsum_y :
        (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) =
          (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) := by
      simp [hsum_log]
    have hcomb :
        -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
            (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) =
          (∑ ab : α × β,
            (-(if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
              (if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)))) := by
      calc
        -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
            (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2))
            = (∑ ab, -(if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab))) +
                (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) := by
                simp [Finset.sum_neg_distrib]
        _ = (∑ ab : α × β,
              (-(if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
                (if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)))) := by
              simpa using
                (Finset.sum_add_distrib
                  (f := fun ab => -(if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)))
                  (g := fun ab => if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2))).symm
    calc
      -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
          (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y))
          = -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
              (∑ ab : α × β, if pXY ab = 0 then 0 else pXY ab * Real.log (pY ab.2)) := by
                simp [hsum_y]
      _ = (∑ ab : α × β,
            (if pXY ab = 0 then 0
             else pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab)))) := by
            -- combine termwise
            refine (hcomb.trans ?_)
            refine Finset.sum_congr rfl ?_
            intro ab hab
            by_cases hpa : pXY ab = 0
            · simp [hpa]
            ·
              have hring :
                  -(pXY ab * Real.log (pXY ab)) + pXY ab * Real.log (pY ab.2) =
                    pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab)) := by
                ring
              simpa [hpa] using hring
  have hterm_nonneg :
      ∀ ab, 0 ≤
        (if pXY ab = 0 then 0
         else pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab))) := by
    intro ab
    by_cases hpa : pXY ab = 0
    · simp [hpa]
    · have hpa_pos : 0 < pXY ab := lt_of_le_of_ne (h_nn ab) (Ne.symm hpa)
      have hpy_ge : pXY ab ≤ pY ab.2 := hpXY_le ab.1 ab.2
      have hlog_le : Real.log (pXY ab) ≤ Real.log (pY ab.2) :=
        Real.log_le_log hpa_pos hpy_ge
      have hdiff_nonneg : 0 ≤ Real.log (pY ab.2) - Real.log (pXY ab) := by
        linarith
      have hmul_nonneg :
          0 ≤ pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab)) :=
        mul_nonneg (h_nn ab) hdiff_nonneg
      simpa [hpa] using hmul_nonneg
  have hsum_nonneg :
      0 ≤ ∑ ab : α × β,
        (if pXY ab = 0 then 0
         else pXY ab * (Real.log (pY ab.2) - Real.log (pXY ab))) := by
    refine Finset.sum_nonneg ?_
    intro ab hab
    exact hterm_nonneg ab
  -- final inequality
  have : 0 ≤
      -(∑ ab, if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) +
        (∑ y, if pY y = 0 then 0 else pY y * Real.log (pY y)) := by
    simpa [hrewrite] using hsum_nonneg
  linarith

/-- Conditioning reduces entropy: H(X|Y) ≤ H(X). -/
theorem condEntropy_le_entropy {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab)
    (h_sum : ∑ ab, pXY ab = 1) :
    condEntropy pXY ≤ shannonEntropy (marginalFst pXY) := by
  -- This is equivalent to mutual information nonnegativity.
  have hmi : 0 ≤ mutualInfo pXY := by
    exact mutualInfo_nonneg pXY h_nn h_sum
  have hmi' :
      0 ≤ shannonEntropy (marginalFst pXY) + shannonEntropy (marginalSnd pXY) -
            shannonEntropy pXY := by
    simpa [mutualInfo] using hmi
  -- rearrange I(X;Y) = H(X) - H(X|Y)
  unfold condEntropy
  linarith

/-! ## Mutual Information Symmetry -/

/-- I(X;Y) = I(Y;X). -/
theorem mutualInfo_symm {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) :
    mutualInfo pXY = mutualInfo (fun ⟨b, a⟩ => pXY (a, b)) := by
  classical
  let pYX : β × α → ℝ := fun ab => pXY (ab.2, ab.1)
  unfold mutualInfo
  have hfst : marginalFst pYX = marginalSnd pXY := by
    funext b
    change (∑ a, pYX (b, a)) = ∑ a, pXY (a, b)
    simp [pYX]
  have hsnd : marginalSnd pYX = marginalFst pXY := by
    funext a
    change (∑ b, pYX (b, a)) = ∑ b, pXY (a, b)
    simp [pYX]
  have hswap :
      shannonEntropy pYX = shannonEntropy pXY := by
    unfold shannonEntropy
    have hsum :
        ∑ ab : β × α,
          (if pYX ab = 0 then 0 else pYX ab * Real.log (pYX ab)) =
        ∑ ab : α × β,
          (if pXY ab = 0 then 0 else pXY ab * Real.log (pXY ab)) := by
      simpa using (Equiv.sum_comp (Equiv.prodComm α β)
        (fun ab : β × α =>
          if pYX ab = 0 then 0 else pYX ab * Real.log (pYX ab))).symm
    simp [hsum]
  simp [pYX, hfst, hsnd, hswap, add_comm]

/-! ## Data Processing Inequality -/

/-- A Markov kernel (stochastic map) from β to γ. -/
structure MarkovKernel (β γ : Type*) [Fintype β] [Fintype γ] where
  transition : β → γ → ℝ
  nonneg : ∀ b c, 0 ≤ transition b c
  sum_one : ∀ b, ∑ c, transition b c = 1

/-- Push a joint distribution through a kernel on the second variable. -/
def pushforward {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ) : α × γ → ℝ :=
  fun ⟨a, c⟩ => ∑ b, pXY (a, b) * K.transition b c

/-- Data processing inequality: I(X;Z) ≤ I(X;Y) for X → Y → Z Markov. -/
axiom data_processing_inequality {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (pXY : α × β → ℝ) (K : MarkovKernel β γ)
    (h_nn : ∀ ab, 0 ≤ pXY ab) (h_sum : ∑ ab, pXY ab = 1) :
    mutualInfo (pushforward pXY K) ≤ mutualInfo pXY

end

end Gibbs.Hamiltonian.Entropy
