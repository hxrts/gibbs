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
    intro x
    cases x <;> simp [add_comm]

/-- BSC capacity formula: C = log 2 - H₂(ε). -/
axiom bsc_capacity (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    channelCapacity (BSC ε hε₀ hε₁) =
      Real.log 2 - Gibbs.Hamiltonian.Entropy.binaryEntropy ε

/-- BSC capacity at ε = 1/2 is zero. -/
axiom bsc_capacity_half :
    channelCapacity (BSC (1/2) (by linarith) (by linarith)) = 0

/-! ## Capacity as Free-Energy Dual -/

/-- Capacity as a variational free-energy dual. -/
axiom capacity_as_free_energy_dual {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : DMC X Y) :
    channelCapacity W =
      ⨆ (d : Gibbs.Hamiltonian.Entropy.Distribution X),
        Gibbs.Hamiltonian.Entropy.shannonEntropy (outputDist W d.pmf) -
        ∑ x, d.pmf x *
          Gibbs.Hamiltonian.Entropy.shannonEntropy (fun y => W.transition x y)

end

end Gibbs.Hamiltonian.Channel
