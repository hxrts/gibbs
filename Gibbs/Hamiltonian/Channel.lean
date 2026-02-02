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

/-- Capacity bounded by log of output alphabet size. -/
axiom channelCapacity_le_log_output {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty Y] (W : DMC X Y) :
    channelCapacity W ≤ Real.log (Fintype.card Y)

/-- Capacity bounded by log of input alphabet size. -/
axiom channelCapacity_le_log_input {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] (W : DMC X Y) :
    channelCapacity W ≤ Real.log (Fintype.card X)

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
