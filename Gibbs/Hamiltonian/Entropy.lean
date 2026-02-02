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

/-- H(p) ≤ log |α| (Shannon bound). -/
axiom shannonEntropy_le_log_card {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card α)

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

/-- D_KL(p‖q) = 0 ↔ p = q. -/
axiom klDivergence_eq_zero_iff {α : Type*} [Fintype α]
    (p q : α → ℝ)
    (hp_nn : ∀ a, 0 ≤ p a) (hp_sum : ∑ a, p a = 1)
    (hq_nn : ∀ a, 0 ≤ q a) (hq_sum : ∑ a, q a = 1)
    (habs : ∀ a, p a ≠ 0 → q a ≠ 0) :
    klDivergence p q = 0 ↔ p = q

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

/-- Mutual information is nonnegative. -/
axiom mutualInfo_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab)
    (h_sum : ∑ ab, pXY ab = 1) :
    0 ≤ mutualInfo pXY

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
