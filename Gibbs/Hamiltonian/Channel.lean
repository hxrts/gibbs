import Gibbs.Hamiltonian.Entropy
import Gibbs.Hamiltonian.PartitionFunction
import Mathlib.Tactic

/-!
# Discrete Memoryless Channels

Defines DMCs, mutual information induced by an input distribution, and channel
capacity as a supremum. Deep coding-theoretic statements are axiomatized.
-/

namespace Gibbs.Hamiltonian.Channel

noncomputable section

open scoped BigOperators

/-! ## Discrete Memoryless Channel -/

/-- A DMC is a stochastic matrix W(y|x). -/
structure DMC (X Y : Type*) [Fintype X] [Fintype Y] where
  transition : X → Y → ℝ
  transition_nonneg : ∀ x y, 0 ≤ transition x y
  transition_sum_one : ∀ x, ∑ y, transition x y = 1

/-! ## Induced Distributions -/

/-- Output distribution induced by input p and channel W. -/
def outputDist {X Y : Type*} [Fintype X] [Fintype Y]
    (W : DMC X Y) (p : X → ℝ) : Y → ℝ :=
  fun y => ∑ x, p x * W.transition x y

/-- Joint distribution p(x,y) = p(x) W(y|x). -/
def jointDist {X Y : Type*} [Fintype X] [Fintype Y]
    (W : DMC X Y) (p : X → ℝ) : X × Y → ℝ :=
  fun ⟨x, y⟩ => p x * W.transition x y

/-- Marginal over X recovers the input distribution. -/
theorem jointDist_marginalFst {X Y : Type*} [Fintype X] [Fintype Y]
    (W : DMC X Y) (p : X → ℝ) :
    Gibbs.Hamiltonian.Entropy.marginalFst (jointDist W p) = p := by
  funext x
  calc
    Gibbs.Hamiltonian.Entropy.marginalFst (jointDist W p) x
        = ∑ y, p x * W.transition x y := rfl
    _ = p x * ∑ y, W.transition x y := by
        simp [Finset.mul_sum]
    _ = p x := by simp [W.transition_sum_one]

/-- Marginal over Y recovers the output distribution. -/
theorem jointDist_marginalSnd {X Y : Type*} [Fintype X] [Fintype Y]
    (W : DMC X Y) (p : X → ℝ) :
    Gibbs.Hamiltonian.Entropy.marginalSnd (jointDist W p) = outputDist W p := by
  funext y
  calc
    Gibbs.Hamiltonian.Entropy.marginalSnd (jointDist W p) y
        = ∑ x, p x * W.transition x y := rfl
    _ = outputDist W p y := rfl

/-! ## Channel Mutual Information and Capacity -/

/-- Mutual information induced by input distribution p and channel W. -/
def channelMutualInfo {X Y : Type*} [Fintype X] [Fintype Y]
    (W : DMC X Y) (p : X → ℝ) : ℝ :=
  Gibbs.Hamiltonian.Entropy.mutualInfo (jointDist W p)

/-- Channel capacity C(W) = sup_p I(p;W). -/
def channelCapacity {X Y : Type*} [Fintype X] [Fintype Y] (W : DMC X Y) : ℝ :=
  ⨆ (d : Gibbs.Hamiltonian.Entropy.Distribution X), channelMutualInfo W d.pmf

/-- Capacity is nonnegative (for nonempty alphabets). -/
theorem channelCapacity_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : DMC X Y) : 0 ≤ channelCapacity W := by
  classical
  -- helper: joint distribution is a valid distribution
  have h_joint_nonneg (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∀ ab, 0 ≤ jointDist W d.pmf ab := by
    rintro ⟨x, y⟩
    exact mul_nonneg (d.nonneg x) (W.transition_nonneg x y)
  have h_joint_sum (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∑ ab, jointDist W d.pmf ab = 1 := by
    calc
      ∑ ab, jointDist W d.pmf ab
          = ∑ x, ∑ y, jointDist W d.pmf (x, y) := by
              simpa using
                (Fintype.sum_prod_type (f := fun ab : X × Y => jointDist W d.pmf ab))
      _ = ∑ x, ∑ y, d.pmf x * W.transition x y := by rfl
      _ = ∑ x, d.pmf x * ∑ y, W.transition x y := by
            simp [Finset.mul_sum]
      _ = ∑ x, d.pmf x := by simp [W.transition_sum_one]
      _ = 1 := d.sum_one
  have h_output_nonneg (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∀ y, 0 ≤ outputDist W d.pmf y := by
    intro y
    refine Finset.sum_nonneg ?_
    intro x hx
    exact mul_nonneg (d.nonneg x) (W.transition_nonneg x y)
  have h_output_sum (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∑ y, outputDist W d.pmf y = 1 := by
    calc
      ∑ y, outputDist W d.pmf y
          = ∑ y, ∑ x, d.pmf x * W.transition x y := by rfl
      _ = ∑ xy : X × Y, d.pmf xy.1 * W.transition xy.1 xy.2 := by
            simpa using (Fintype.sum_prod_type_right'
              (f := fun x y => d.pmf x * W.transition x y)).symm
      _ = ∑ ab, jointDist W d.pmf ab := by rfl
      _ = 1 := h_joint_sum d
  have h_bound (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      channelMutualInfo W d.pmf ≤
        Real.log (Fintype.card X) + Real.log (Fintype.card Y) := by
    have hHx :
        Gibbs.Hamiltonian.Entropy.shannonEntropy d.pmf ≤
          Real.log (Fintype.card X) := by
      exact Gibbs.Hamiltonian.Entropy.shannonEntropy_le_log_card d.pmf d.nonneg d.sum_one
    have hHy :
        Gibbs.Hamiltonian.Entropy.shannonEntropy (outputDist W d.pmf) ≤
          Real.log (Fintype.card Y) := by
      exact Gibbs.Hamiltonian.Entropy.shannonEntropy_le_log_card
        (outputDist W d.pmf) (h_output_nonneg d) (h_output_sum d)
    have hHxy :
        0 ≤ Gibbs.Hamiltonian.Entropy.shannonEntropy (jointDist W d.pmf) :=
      Gibbs.Hamiltonian.Entropy.shannonEntropy_nonneg (jointDist W d.pmf)
        (h_joint_nonneg d) (h_joint_sum d)
    unfold channelMutualInfo Gibbs.Hamiltonian.Entropy.mutualInfo
    have hle1 :
        Gibbs.Hamiltonian.Entropy.shannonEntropy (Gibbs.Hamiltonian.Entropy.marginalFst (jointDist W d.pmf)) +
            Gibbs.Hamiltonian.Entropy.shannonEntropy (Gibbs.Hamiltonian.Entropy.marginalSnd (jointDist W d.pmf)) -
            Gibbs.Hamiltonian.Entropy.shannonEntropy (jointDist W d.pmf)
          ≤
        Gibbs.Hamiltonian.Entropy.shannonEntropy (Gibbs.Hamiltonian.Entropy.marginalFst (jointDist W d.pmf)) +
            Gibbs.Hamiltonian.Entropy.shannonEntropy (Gibbs.Hamiltonian.Entropy.marginalSnd (jointDist W d.pmf)) := by
      linarith
    have hle2 :
        Gibbs.Hamiltonian.Entropy.shannonEntropy (Gibbs.Hamiltonian.Entropy.marginalFst (jointDist W d.pmf)) +
            Gibbs.Hamiltonian.Entropy.shannonEntropy (Gibbs.Hamiltonian.Entropy.marginalSnd (jointDist W d.pmf))
          ≤
        Real.log (Fintype.card X) + Real.log (Fintype.card Y) := by
      -- replace marginals with input/output distributions
      have hfst : Gibbs.Hamiltonian.Entropy.marginalFst (jointDist W d.pmf) = d.pmf :=
        jointDist_marginalFst W d.pmf
      have hsnd : Gibbs.Hamiltonian.Entropy.marginalSnd (jointDist W d.pmf) = outputDist W d.pmf :=
        jointDist_marginalSnd W d.pmf
      simpa [hfst, hsnd] using add_le_add hHx hHy
    exact le_trans hle1 hle2
  have hB : BddAbove (Set.range (fun d : Gibbs.Hamiltonian.Entropy.Distribution X =>
      channelMutualInfo W d.pmf)) := by
    refine ⟨Real.log (Fintype.card X) + Real.log (Fintype.card Y), ?_⟩
    rintro _ ⟨d', rfl⟩
    exact h_bound d'
  -- choose a deterministic distribution to witness nonnegativity
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  let d0 : Gibbs.Hamiltonian.Entropy.Distribution X :=
    { pmf := fun x => if x = x0 then 1 else 0
      nonneg := by
        intro x
        by_cases h : x = x0
        · simp [h]
        · simp [h]
      sum_one := by
        simp }
  have hmi : 0 ≤ Gibbs.Hamiltonian.Entropy.mutualInfo (jointDist W d0.pmf) :=
    Gibbs.Hamiltonian.Entropy.mutualInfo_nonneg (jointDist W d0.pmf)
      (h_joint_nonneg d0) (h_joint_sum d0)
  have hle : channelMutualInfo W d0.pmf ≤ channelCapacity W := by
    exact le_ciSup hB d0
  exact le_trans hmi hle

/-! ## Mutual Information Bounds via Conditional Entropy -/

/-- I(X;Y) ≤ H(X): mutual info bounded by first marginal entropy.
    Follows from H(X,Y) ≥ H(Y) (conditional entropy nonneg). -/
private theorem mutualInfo_le_shannonEntropy_marginalFst {X Y : Type*}
    [Fintype X] [Fintype Y]
    (pXY : X × Y → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) (h_sum : ∑ ab, pXY ab = 1) :
    Gibbs.Hamiltonian.Entropy.mutualInfo pXY ≤
      Gibbs.Hamiltonian.Entropy.shannonEntropy
        (Gibbs.Hamiltonian.Entropy.marginalFst pXY) := by
  -- condEntropy_nonneg gives 0 ≤ H(X,Y) - H(Y), i.e. H(Y) ≤ H(X,Y)
  have hcond := Gibbs.Hamiltonian.Entropy.condEntropy_nonneg pXY h_nn h_sum
  -- mutual info = H(X) + H(Y) - H(X,Y), so I ≤ H(X) iff H(Y) ≤ H(X,Y)
  unfold Gibbs.Hamiltonian.Entropy.mutualInfo Gibbs.Hamiltonian.Entropy.condEntropy at *
  linarith

/-- I(X;Y) ≤ H(Y): mutual info bounded by second marginal entropy.
    Uses I(X;Y) = H(X) + H(Y) - H(X,Y) and H(X,Y) ≥ H(X) via condEntropy on swapped. -/
private theorem mutualInfo_le_shannonEntropy_marginalSnd {X Y : Type*}
    [Fintype X] [Fintype Y]
    (pXY : X × Y → ℝ) (h_nn : ∀ ab, 0 ≤ pXY ab) (h_sum : ∑ ab, pXY ab = 1) :
    Gibbs.Hamiltonian.Entropy.mutualInfo pXY ≤
      Gibbs.Hamiltonian.Entropy.shannonEntropy
        (Gibbs.Hamiltonian.Entropy.marginalSnd pXY) := by
  -- use symmetry: I(X;Y) = I(Y;X) ≤ H(margFst(pYX)) = H(margSnd(pXY))
  have hsymm := Gibbs.Hamiltonian.Entropy.mutualInfo_symm pXY
  -- pYX = fun (y,x) => pXY(x,y); mutualInfo_symm gives I(pXY) = I(pYX)
  let pYX : Y × X → ℝ := fun ⟨y, x⟩ => pXY (x, y)
  have h_nn' : ∀ ab, 0 ≤ pYX ab := by rintro ⟨y, x⟩; exact h_nn (x, y)
  -- swapped sum equals 1
  have h_sum' : ∑ ab, pYX ab = 1 := by
    -- expand both as double sums, then swap summation order
    have lhs : ∑ ab : Y × X, pYX ab = ∑ y, ∑ x, pXY (x, y) := by
      simp [pYX, Fintype.sum_prod_type]
    have rhs : ∑ ab : X × Y, pXY ab = ∑ x, ∑ y, pXY (x, y) := by
      simp [Fintype.sum_prod_type]
    rw [lhs, Finset.sum_comm, ← rhs]; exact h_sum
  -- apply the margFst bound to the swapped distribution
  have hbound := mutualInfo_le_shannonEntropy_marginalFst pYX h_nn' h_sum'
  -- marginalFst pYX = marginalSnd pXY
  have hfst_eq : Gibbs.Hamiltonian.Entropy.marginalFst pYX =
      Gibbs.Hamiltonian.Entropy.marginalSnd pXY := by
    funext y; simp [Gibbs.Hamiltonian.Entropy.marginalFst,
      Gibbs.Hamiltonian.Entropy.marginalSnd, pYX]
  rw [hfst_eq] at hbound
  -- mutualInfo pXY = mutualInfo pYX by symmetry
  have : Gibbs.Hamiltonian.Entropy.mutualInfo pXY =
      Gibbs.Hamiltonian.Entropy.mutualInfo pYX := by
    exact hsymm
  linarith

/-! ## Capacity Bounds -/

/-- Capacity bounded by log of output alphabet size: C(W) ≤ log |Y|.
    Each I(d;W) ≤ H(Y) ≤ log |Y| by conditional entropy nonneg + Shannon bound. -/
theorem channelCapacity_le_log_output {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : DMC X Y) :
    channelCapacity W ≤ Real.log (Fintype.card Y) := by
  -- reuse helpers from channelCapacity_nonneg for joint dist validity
  have h_joint_nonneg (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∀ ab, 0 ≤ jointDist W d.pmf ab := by
    rintro ⟨x, y⟩; exact mul_nonneg (d.nonneg x) (W.transition_nonneg x y)
  have h_joint_sum (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∑ ab, jointDist W d.pmf ab = 1 := by
    calc ∑ ab, jointDist W d.pmf ab
        = ∑ x, ∑ y, jointDist W d.pmf (x, y) := by
          simpa using Fintype.sum_prod_type (f := fun ab : X × Y => jointDist W d.pmf ab)
      _ = ∑ x, ∑ y, d.pmf x * W.transition x y := rfl
      _ = ∑ x, d.pmf x * ∑ y, W.transition x y := by simp [Finset.mul_sum]
      _ = 1 := by simp [W.transition_sum_one, d.sum_one]
  have h_output_nonneg (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∀ y, 0 ≤ outputDist W d.pmf y := by
    intro y; exact Finset.sum_nonneg fun x _ => mul_nonneg (d.nonneg x) (W.transition_nonneg x y)
  have h_output_sum (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∑ y, outputDist W d.pmf y = 1 := by
    calc ∑ y, outputDist W d.pmf y
        = ∑ ab, jointDist W d.pmf ab := by
          simpa using (Fintype.sum_prod_type_right'
            (f := fun x y => d.pmf x * W.transition x y)).symm
      _ = 1 := h_joint_sum d
  -- each I(d;W) ≤ H(output) ≤ log |Y|
  have h_bound (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      channelMutualInfo W d.pmf ≤ Real.log (Fintype.card Y) := by
    -- I ≤ H(margSnd) = H(output)
    have hI_le := mutualInfo_le_shannonEntropy_marginalSnd
      (jointDist W d.pmf) (h_joint_nonneg d) (h_joint_sum d)
    -- margSnd of joint = output
    have hsnd := jointDist_marginalSnd W d.pmf
    rw [hsnd] at hI_le
    -- H(output) ≤ log |Y|
    have hH_le := Gibbs.Hamiltonian.Entropy.shannonEntropy_le_log_card
      (outputDist W d.pmf) (h_output_nonneg d) (h_output_sum d)
    exact le_trans hI_le hH_le
  -- witness for Nonempty (Distribution X) needed by ciSup_le
  classical
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  haveI : Nonempty (Gibbs.Hamiltonian.Entropy.Distribution X) :=
    ⟨{ pmf := fun x => if x = x0 then 1 else 0
       nonneg := fun x => by split <;> norm_num
       sum_one := by simp }⟩
  exact ciSup_le fun d => h_bound d

/-- Capacity bounded by log of input alphabet size: C(W) ≤ log |X|.
    Each I(d;W) ≤ H(X) ≤ log |X| by conditional entropy nonneg + Shannon bound. -/
theorem channelCapacity_le_log_input {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : DMC X Y) :
    channelCapacity W ≤ Real.log (Fintype.card X) := by
  have h_joint_nonneg (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∀ ab, 0 ≤ jointDist W d.pmf ab := by
    rintro ⟨x, y⟩; exact mul_nonneg (d.nonneg x) (W.transition_nonneg x y)
  have h_joint_sum (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      ∑ ab, jointDist W d.pmf ab = 1 := by
    calc ∑ ab, jointDist W d.pmf ab
        = ∑ x, ∑ y, jointDist W d.pmf (x, y) := by
          simpa using Fintype.sum_prod_type (f := fun ab : X × Y => jointDist W d.pmf ab)
      _ = ∑ x, ∑ y, d.pmf x * W.transition x y := rfl
      _ = ∑ x, d.pmf x * ∑ y, W.transition x y := by simp [Finset.mul_sum]
      _ = 1 := by simp [W.transition_sum_one, d.sum_one]
  -- each I(d;W) ≤ H(margFst) = H(input) ≤ log |X|
  have h_bound (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
      channelMutualInfo W d.pmf ≤ Real.log (Fintype.card X) := by
    have hI_le := mutualInfo_le_shannonEntropy_marginalFst
      (jointDist W d.pmf) (h_joint_nonneg d) (h_joint_sum d)
    have hfst := jointDist_marginalFst W d.pmf
    rw [hfst] at hI_le
    have hH_le := Gibbs.Hamiltonian.Entropy.shannonEntropy_le_log_card
      d.pmf d.nonneg d.sum_one
    exact le_trans hI_le hH_le
  -- witness for Nonempty (Distribution X) needed by ciSup_le
  classical
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  haveI : Nonempty (Gibbs.Hamiltonian.Entropy.Distribution X) :=
    ⟨{ pmf := fun x => if x = x0 then 1 else 0
       nonneg := fun x => by split <;> norm_num
       sum_one := by simp }⟩
  exact ciSup_le fun d => h_bound d

/-! ## DMC Joint Entropy Decomposition -/

/-- Joint entropy of a DMC decomposes as H(X) + Σ_x p(x) H(W(·|x)).

    For the DMC joint p(x,y) = p(x)W(y|x), the joint entropy splits into
    the input entropy plus the conditional entropy, where H(Y|X) for a DMC
    is Σ_x p(x) H(W(·|x)). -/
private theorem dmc_joint_entropy_eq {X Y : Type*} [Fintype X] [Fintype Y]
    (W : DMC X Y) (p : X → ℝ) (hp_nn : ∀ x, 0 ≤ p x) :
    Gibbs.Hamiltonian.Entropy.shannonEntropy (jointDist W p) =
      Gibbs.Hamiltonian.Entropy.shannonEntropy p +
      ∑ x, p x *
        Gibbs.Hamiltonian.Entropy.shannonEntropy (fun y => W.transition x y) := by
  classical
  unfold Gibbs.Hamiltonian.Entropy.shannonEntropy jointDist
  -- rewrite product sum as double sum
  have hprod : ∀ f : X × Y → ℝ,
      ∑ ab : X × Y, f ab = ∑ x, ∑ y, f (x, y) := by
    intro f; exact Fintype.sum_prod_type f
  rw [hprod]
  -- for each x, split the inner sum
  have hterm : ∀ x,
      ∑ y, (if p x * W.transition x y = 0 then 0
        else p x * W.transition x y * Real.log (p x * W.transition x y)) =
      (if p x = 0 then 0 else p x * Real.log (p x)) +
      p x * ∑ y, (if W.transition x y = 0 then 0
        else W.transition x y * Real.log (W.transition x y)) := by
    intro x
    by_cases hpx : p x = 0
    · -- p(x) = 0: all joint terms vanish
      simp [hpx]
    · -- p(x) > 0: split log(p*W) = log p + log W
      have hpx_pos : 0 < p x :=
        lt_of_le_of_ne (hp_nn x) (Ne.symm hpx)
      simp only [hpx, ↓reduceIte]
      -- Σ_y [if p*W=0 then 0 else p*W*(log p + log W)]
      have hinner : ∀ y,
          (if p x * W.transition x y = 0 then 0
            else p x * W.transition x y *
              Real.log (p x * W.transition x y)) =
          p x * W.transition x y * Real.log (p x) +
          p x * (if W.transition x y = 0 then 0
            else W.transition x y * Real.log (W.transition x y)) := by
        intro y
        by_cases hwy : W.transition x y = 0
        · simp [hwy]
        · have hwy_pos : 0 < W.transition x y :=
            lt_of_le_of_ne (W.transition_nonneg x y) (Ne.symm hwy)
          have hne : p x * W.transition x y ≠ 0 :=
            ne_of_gt (mul_pos hpx_pos hwy_pos)
          simp only [hne, hwy, ↓reduceIte]
          rw [Real.log_mul (ne_of_gt hpx_pos) (ne_of_gt hwy_pos)]
          ring
      simp_rw [hinner, Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, W.transition_sum_one, mul_one]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp [Finset.mul_sum, Finset.sum_neg_distrib]
  ring

/-- Mutual information for a DMC: I(X;Y) = H(Y) - Σ_x p(x) H(W(·|x)).

    Uses the identity I = H(X) + H(Y) - H(X,Y) and the DMC joint entropy
    decomposition H(X,Y) = H(X) + Σ_x p(x) H(W(·|x)). -/
private theorem dmc_mutualInfo_eq {X Y : Type*} [Fintype X] [Fintype Y]
    (W : DMC X Y) (d : Gibbs.Hamiltonian.Entropy.Distribution X) :
    channelMutualInfo W d.pmf =
      Gibbs.Hamiltonian.Entropy.shannonEntropy (outputDist W d.pmf) -
      ∑ x, d.pmf x *
        Gibbs.Hamiltonian.Entropy.shannonEntropy (fun y => W.transition x y) := by
  unfold channelMutualInfo Gibbs.Hamiltonian.Entropy.mutualInfo
  rw [jointDist_marginalFst W d.pmf, jointDist_marginalSnd W d.pmf,
    dmc_joint_entropy_eq W d.pmf d.nonneg]
  ring

/-! ## Capacity as Free-Energy Dual -/

/-- Capacity as a variational free-energy dual.

    Rewrites C(W) = sup_d I(d;W) using the DMC identity
    I = H(output) - Σ_x d(x) H(W(·|x)). -/
theorem capacity_as_free_energy_dual {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : DMC X Y) :
    channelCapacity W =
      ⨆ (d : Gibbs.Hamiltonian.Entropy.Distribution X),
        Gibbs.Hamiltonian.Entropy.shannonEntropy (outputDist W d.pmf) -
        ∑ x, d.pmf x *
          Gibbs.Hamiltonian.Entropy.shannonEntropy (fun y => W.transition x y) := by
  unfold channelCapacity
  congr 1
  funext d
  exact dmc_mutualInfo_eq W d

/-! ## Binary Symmetric Channel -/

/-- Binary symmetric channel with crossover probability ε. -/
def BSC (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) : DMC Bool Bool where
  transition := fun x y => if x = y then 1 - ε else ε
  transition_nonneg := by
    intro x y
    by_cases hxy : x = y
    · simp [hxy, hε₁, sub_nonneg]
    · simp [hxy, hε₀]
  transition_sum_one := by
    intro x; cases x <;> simp [add_comm]

/-- Each BSC row has Shannon entropy equal to binary entropy. -/
private lemma bsc_row_entropy (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (x : Bool) :
    Gibbs.Hamiltonian.Entropy.shannonEntropy
      (fun y => (BSC ε hε₀ hε₁).transition x y) =
    Gibbs.Hamiltonian.Entropy.binaryEntropy ε := by
  classical
  unfold Gibbs.Hamiltonian.Entropy.shannonEntropy
    Gibbs.Hamiltonian.Entropy.binaryEntropy BSC
  -- rewrite (1 - ε = 0) ↔ (ε = 1) for if-condition matching
  have h1e : (1 - ε = 0) = (ε = 1) :=
    propext ⟨by intro h; linarith, by intro h; linarith⟩
  cases x <;> simp [Fintype.univ_bool, h1e] <;> ring

/-- BSC conditional entropy sum: Σ_x d(x) H(W(·|x)) = H₂(ε). -/
private lemma bsc_condEntropy_sum (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (d : Gibbs.Hamiltonian.Entropy.Distribution Bool) :
    ∑ x, d.pmf x *
      Gibbs.Hamiltonian.Entropy.shannonEntropy
        (fun y => (BSC ε hε₀ hε₁).transition x y) =
    Gibbs.Hamiltonian.Entropy.binaryEntropy ε := by
  simp_rw [bsc_row_entropy]
  rw [← Finset.sum_mul, d.sum_one, one_mul]

/-- Uniform output from BSC with uniform input. -/
private lemma bsc_uniform_output (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    outputDist (BSC ε hε₀ hε₁) (fun _ : Bool => 1/2) =
      fun _ : Bool => 1/2 := by
  funext y; unfold outputDist BSC
  cases y <;> simp [Fintype.univ_bool] <;> ring

/-- Shannon entropy of uniform Bool is log 2. -/
private lemma shannonEntropy_uniform_bool :
    Gibbs.Hamiltonian.Entropy.shannonEntropy (fun _ : Bool => (1 : ℝ)/2) =
      Real.log 2 := by
  unfold Gibbs.Hamiltonian.Entropy.shannonEntropy
  simp [Fintype.univ_bool, Real.log_inv]

/-- Helper: BSC output distribution sums to 1. -/
private lemma bsc_output_sum (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (d : Gibbs.Hamiltonian.Entropy.Distribution Bool) :
    ∑ y, outputDist (BSC ε hε₀ hε₁) d.pmf y = 1 := by
  simp [outputDist, BSC, Fintype.univ_bool]
  have hsum := d.sum_one
  simp [Fintype.univ_bool] at hsum
  linarith

/-- Helper: BSC output distribution is nonneg. -/
private lemma bsc_output_nonneg (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (d : Gibbs.Hamiltonian.Entropy.Distribution Bool) :
    ∀ y, 0 ≤ outputDist (BSC ε hε₀ hε₁) d.pmf y :=
  fun y => Finset.sum_nonneg fun x _ =>
    mul_nonneg (d.nonneg x) ((BSC ε hε₀ hε₁).transition_nonneg x y)

/-- BSC capacity formula: C = log 2 - H₂(ε). -/
theorem bsc_capacity (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    channelCapacity (BSC ε hε₀ hε₁) =
      Real.log 2 - Gibbs.Hamiltonian.Entropy.binaryEntropy ε := by
  classical
  -- Rewrite via free-energy dual: C = sup_d [H(output) - Σ_x d(x) H(W(·|x))]
  rw [capacity_as_free_energy_dual]
  -- Simplify conditional entropy to H₂(ε)
  have hsimpl (d : Gibbs.Hamiltonian.Entropy.Distribution Bool) :
      Gibbs.Hamiltonian.Entropy.shannonEntropy
          (outputDist (BSC ε hε₀ hε₁) d.pmf) -
        ∑ x, d.pmf x * Gibbs.Hamiltonian.Entropy.shannonEntropy
          (fun y => (BSC ε hε₀ hε₁).transition x y) =
      Gibbs.Hamiltonian.Entropy.shannonEntropy
          (outputDist (BSC ε hε₀ hε₁) d.pmf) -
        Gibbs.Hamiltonian.Entropy.binaryEntropy ε := by
    rw [bsc_condEntropy_sum]
  simp_rw [hsimpl]
  -- need Nonempty instance for ciSup
  haveI : Nonempty (Gibbs.Hamiltonian.Entropy.Distribution Bool) :=
    ⟨{ pmf := fun _ => 1/2, nonneg := by intro _; norm_num,
       sum_one := by simp [Fintype.univ_bool] }⟩
  apply le_antisymm
  · -- upper bound: H(output) ≤ log |Bool| = log 2
    apply ciSup_le; intro d
    have hle := Gibbs.Hamiltonian.Entropy.shannonEntropy_le_log_card
      (outputDist (BSC ε hε₀ hε₁) d.pmf)
      (bsc_output_nonneg ε hε₀ hε₁ d) (bsc_output_sum ε hε₀ hε₁ d)
    have hcard : (Fintype.card Bool : ℝ) = 2 := by
      simp [Fintype.card_bool]
    linarith [hcard ▸ hle]
  · -- lower bound: uniform input achieves log 2
    let d0 : Gibbs.Hamiltonian.Entropy.Distribution Bool :=
      { pmf := fun _ => 1/2
        nonneg := by intro _; norm_num
        sum_one := by simp [Fintype.univ_bool] }
    have hout : outputDist (BSC ε hε₀ hε₁) d0.pmf = fun _ => 1/2 :=
      bsc_uniform_output ε hε₀ hε₁
    -- bdd above witness for ciSup
    have hbdd : BddAbove (Set.range fun d : Gibbs.Hamiltonian.Entropy.Distribution Bool =>
        Gibbs.Hamiltonian.Entropy.shannonEntropy
          (outputDist (BSC ε hε₀ hε₁) d.pmf) -
        Gibbs.Hamiltonian.Entropy.binaryEntropy ε) := by
      refine ⟨Real.log 2 - Gibbs.Hamiltonian.Entropy.binaryEntropy ε, ?_⟩
      rintro _ ⟨d', rfl⟩
      have hle := Gibbs.Hamiltonian.Entropy.shannonEntropy_le_log_card
        (outputDist (BSC ε hε₀ hε₁) d'.pmf)
        (bsc_output_nonneg ε hε₀ hε₁ d') (bsc_output_sum ε hε₀ hε₁ d')
      have hcard : (Fintype.card Bool : ℝ) = 2 := by
        simp [Fintype.card_bool]
      linarith [hcard ▸ hle]
    exact le_ciSup_of_le hbdd d0 (by rw [hout, shannonEntropy_uniform_bool])

/-- BSC capacity at ε = 1/2 is zero. -/
theorem bsc_capacity_half :
    channelCapacity (BSC (1/2) (by linarith) (by linarith)) = 0 := by
  rw [bsc_capacity]
  unfold Gibbs.Hamiltonian.Entropy.binaryEntropy
  have h : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  norm_num [h]; ring

end

end Gibbs.Hamiltonian.Channel
