import Gibbs.Hamiltonian.Channel
import Gibbs.Consensus.Gap
import Gibbs.Consensus.CodingBridge
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Channel Capacity as a Consensus Phase Boundary

States the noisy channel coding theorem as a gap/phase transition and
connects the capacity threshold to consensus-style safety gaps.
-/

namespace Gibbs.Consensus.ChannelThreshold

noncomputable section

open scoped BigOperators

/-! ## Channel Energy Gap -/

/-- Energy gap between capacity and rate. -/
def channelEnergyGap {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ) : ℝ :=
  Gibbs.Hamiltonian.Channel.channelCapacity W - R

/-- Reliable communication iff positive gap. -/
theorem reliable_iff_positive_gap {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ) :
    R < Gibbs.Hamiltonian.Channel.channelCapacity W ↔ 0 < channelEnergyGap W R := by
  constructor
  · intro h
    unfold channelEnergyGap
    linarith
  · intro h
    unfold channelEnergyGap at h
    linarith

/-! ## Error Probability -/

/-- Average error probability for a code over a DMC. -/
def avgErrorProb {M X Y : Type*} [Fintype M] [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (enc : M → X) (dec : Y → Option M) : ℝ :=
  by
    classical
    exact (1 / (Fintype.card M : ℝ)) * ∑ m : M, ∑ y : Y,
      W.transition (enc m) y * (if dec y = some m then 0 else 1)

/-- Axiomatized n-fold memoryless extension of a DMC. -/
def blockChannel {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (n : ℕ) :
    Gibbs.Hamiltonian.Channel.DMC (Fin n → X) (Fin n → Y) where
  transition := fun x y => ∏ i, W.transition (x i) (y i)
  transition_nonneg := by
    intro x y
    classical
    exact Finset.prod_nonneg (fun i _ => W.transition_nonneg (x i) (y i))
  transition_sum_one := by
    intro x
    classical
    -- Product of per-coordinate sums equals 1.
    -- Sum over all functions factors into a product of sums.
    have hsum :
        (∑ y : Fin n → Y, ∏ i, W.transition (x i) (y i)) =
          ∏ i, ∑ y, W.transition (x i) y := by
      have hpi :
          (∑ y : Fin n → Y, ∏ i, W.transition (x i) (y i)) =
            ∑ y ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Y)),
              ∏ i, W.transition (x i) (y i) := by
        simp [Finset.sum_univ_pi]
      have hprod :
          ∑ y ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Y)),
              ∏ i, W.transition (x i) (y i) =
            ∏ i, ∑ y ∈ (Finset.univ : Finset Y), W.transition (x i) y := by
        simp using
          (Finset.sum_prod_piFinset (s := (Finset.univ : Finset Y))
            (g := fun i y => W.transition (x i) y))
      -- remove the `∈ univ` binder
      have hprod' :
          (∏ i, ∑ y ∈ (Finset.univ : Finset Y), W.transition (x i) y) =
            ∏ i, ∑ y, W.transition (x i) y := by
        simp
      simpa [hpi, hprod, hprod']
    -- Each per-coordinate sum is 1.
    simpa [hsum, W.transition_sum_one]

/-! ## Noisy Channel Coding Theorem (Statements) -/

/-- Achievability: rates below capacity admit arbitrarily small error. -/
axiom channel_coding_achievability {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R ε : ℝ)
    (hR : R < Gibbs.Hamiltonian.Channel.channelCapacity W) (hε : 0 < ε) :
    ∃ (n : ℕ) (M : Type) (_ : Fintype M)
      (enc : M → (Fin n → X)) (dec : (Fin n → Y) → Option M),
      (Real.log (Fintype.card M) / (n : ℝ) ≥ R) ∧
      avgErrorProb (blockChannel W n) enc dec ≤ ε

/-- Converse: rates above capacity incur error approaching 1. -/
axiom channel_coding_converse {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ)
    (hR : Gibbs.Hamiltonian.Channel.channelCapacity W < R) :
    ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0,
      ∀ (M : Type) (_ : Fintype M) (enc : M → (Fin n → X)) (dec : (Fin n → Y) → Option M),
        Real.log (Fintype.card M) / (n : ℝ) ≥ R →
        1 - ε ≤ avgErrorProb (blockChannel W n) enc dec

/-! ## Capacity as Phase Boundary -/

/-- Coding safety: error can be driven arbitrarily small. -/
def CodingSafe {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ) : Prop :=
  ∀ ε > 0, ∃ (n : ℕ) (M : Type) (_ : Fintype M)
    (enc : M → (Fin n → X)) (dec : (Fin n → Y) → Option M),
    Real.log (Fintype.card M) / (n : ℝ) ≥ R ∧
    avgErrorProb (blockChannel W n) enc dec ≤ ε

/-- Safety iff positive gap (axiomatized coding theorem). -/
axiom codingSafe_iff_positive_gap {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ) :
    CodingSafe W R ↔ 0 < channelEnergyGap W R

/-! ## Noisy Consensus -/

/-- Byzantine consensus over a noisy channel. -/
structure NoisyConsensus where
  /-- Number of participants. -/
  numParticipants : ℕ
  /-- Fraction of messages corrupted. -/
  corruptionRate : ℝ
  /-- Corruption rate is a valid probability. -/
  rate_nonneg : 0 ≤ corruptionRate
  rate_le_one : corruptionRate ≤ 1

/-- Effective adversary channel (BSC). -/
def NoisyConsensus.adversaryChannel (nc : NoisyConsensus) :
    Gibbs.Hamiltonian.Channel.DMC Bool Bool :=
  Gibbs.Hamiltonian.Channel.BSC nc.corruptionRate nc.rate_nonneg nc.rate_le_one

/-- Consensus requires positive capacity (ε < 1/2 for BSC). -/
axiom consensus_requires_positive_capacity (nc : NoisyConsensus)
    (h : nc.corruptionRate < 1/2) :
    0 < Gibbs.Hamiltonian.Channel.channelCapacity nc.adversaryChannel

/-- Corruption threshold f = 1/2 is zero capacity for the BSC. -/
theorem corruption_threshold_is_zero_capacity :
    Gibbs.Hamiltonian.Channel.channelCapacity
      (Gibbs.Hamiltonian.Channel.BSC (1/2) (by linarith) (by linarith)) = 0 := by
  simpa using Gibbs.Hamiltonian.Channel.bsc_capacity_half

end

end Gibbs.Consensus.ChannelThreshold
