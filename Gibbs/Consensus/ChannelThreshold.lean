import Gibbs.Hamiltonian
import Gibbs.Consensus.Gap
import Gibbs.Consensus.CodingBridge
import Mathlib.Tactic

/-!
# Channel Capacity as a Consensus Phase Boundary

States the noisy channel coding theorem as a gap/phase transition and
connects the capacity threshold to consensus-style safety gaps.
-/

namespace Gibbs.Consensus.ChannelThreshold

noncomputable section

open scoped BigOperators
open Gibbs.Hamiltonian.Coding
open Gibbs.Axioms

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

/-! ## Capacity as Phase Boundary -/

/-- Coding safety: error can be driven arbitrarily small at all large blocklengths.

    Stronger than requiring a code at just one blocklength, here we demand
    good codes exist at every sufficiently large n. This matches the standard
    formulation of Shannon's coding theorem and enables the converse. -/
def CodingSafe {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ) : Prop :=
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ (M : Type) (_ : Fintype M)
      (enc : M → (Fin n → X)) (dec : (Fin n → Y) → Option M),
      Real.log (Fintype.card M) / (n : ℝ) ≥ R ∧
      avgErrorProb (blockChannel W n) enc dec ≤ ε

/-- Achievability implies coding safety: R < C implies CodingSafe W R. -/
private theorem codingSafe_of_positive_gap {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ)
    (hgap : 0 < channelEnergyGap W R) : CodingSafe W R := by
  have hR : R < Gibbs.Hamiltonian.Channel.channelCapacity W := by
    unfold channelEnergyGap at hgap; linarith
  intro ε hε
  exact channel_coding_achievability W R ε hR hε

/-- Converse: CodingSafe is impossible when C <= R.

    The strong converse at epsilon = 1/4 gives n₀ with error >= 3/4 for all
    n >= n₀ at rate >= R, contradicting CodingSafe at epsilon = 1/4. -/
private theorem not_codingSafe_of_capacity_le {X Y : Type*}
    [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ)
    (hR : Gibbs.Hamiltonian.Channel.channelCapacity W ≤ R) :
    ¬ CodingSafe W R := by
  intro hsafe
  -- CodingSafe at epsilon = 1/4 gives codes with error <= 1/4 for all large n
  obtain ⟨n₁, hn₁⟩ := hsafe (1/4) (by norm_num)
  -- converse at epsilon = 1/4 gives error >= 3/4 for all large n at rate >= R
  obtain ⟨n₀, hn₀⟩ := channel_coding_converse W R hR (1/4) (by norm_num)
  -- at n = max(n₀, n₁), both apply
  obtain ⟨M, hfin, enc, dec, hrate, herr⟩ := hn₁ (max n₀ n₁) (le_max_right _ _)
  have hconv := hn₀ (max n₀ n₁) (le_max_left _ _) M hfin enc dec hrate
  linarith

/-- Safety iff positive gap: CodingSafe W R iff R < C.

    Backward: achievability gives codes at all large blocklengths.
    Forward: strong converse contradicts CodingSafe when C <= R. -/
theorem codingSafe_iff_positive_gap {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ) :
    CodingSafe W R ↔ 0 < channelEnergyGap W R := by
  constructor
  · intro hsafe
    by_contra hle
    push_neg at hle
    unfold channelEnergyGap at hle
    exact not_codingSafe_of_capacity_le W R (by linarith) hsafe
  · exact codingSafe_of_positive_gap W R

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

/-- Consensus requires positive capacity (epsilon < 1/2 for BSC).

    By `bsc_capacity`, C = log 2 - H₂(epsilon). Since epsilon < 1/2 implies
    epsilon != 1/2, `binaryEntropy_lt_log_two` gives H₂(epsilon) < log 2,
    hence C > 0. -/
theorem consensus_requires_positive_capacity (nc : NoisyConsensus)
    (h : nc.corruptionRate < 1/2) :
    0 < Gibbs.Hamiltonian.Channel.channelCapacity nc.adversaryChannel := by
  unfold NoisyConsensus.adversaryChannel
  rw [Gibbs.Hamiltonian.Channel.bsc_capacity]
  have hne : nc.corruptionRate ≠ 1/2 := ne_of_lt h
  have hlt := Gibbs.Hamiltonian.Entropy.binaryEntropy_lt_log_two
    nc.corruptionRate nc.rate_nonneg nc.rate_le_one hne
  linarith

/-- Corruption threshold f = 1/2 is zero capacity for the BSC. -/
theorem corruption_threshold_is_zero_capacity :
    Gibbs.Hamiltonian.Channel.channelCapacity
      (Gibbs.Hamiltonian.Channel.BSC (1/2) (by linarith) (by linarith)) = 0 := by
  simpa using Gibbs.Hamiltonian.Channel.bsc_capacity_half

end

end Gibbs.Consensus.ChannelThreshold
