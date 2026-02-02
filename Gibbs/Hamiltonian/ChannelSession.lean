import Gibbs.Hamiltonian.Channel
import Gibbs.Session
import Mathlib.Tactic

/-!
# Channel Constraints for Session Types

Equips session-type edges with channel models and connects protocol feasibility
with information-theoretic capacity.
-/

namespace Gibbs.Hamiltonian.ChannelSession

noncomputable section

/-! ## Typed Channels -/

/-- A communication edge equipped with a channel model. -/
structure TypedChannel (X Y : Type*) [Fintype X] [Fintype Y] where
  /-- The session-type edge. -/
  edge : Gibbs.Edge
  /-- The noisy channel on this edge. -/
  channel : Gibbs.Hamiltonian.Channel.DMC X Y

/-- Capacity of a typed channel. -/
def TypedChannel.capacity {X Y : Type*} [Fintype X] [Fintype Y]
    (tc : TypedChannel X Y) : ℝ :=
  Gibbs.Hamiltonian.Channel.channelCapacity tc.channel

/-! ## Protocol Information Cost -/

/-- Entropy cost of a branching distribution. -/
def branchEntropy {L : Type*} [Fintype L] (labelDist : L → ℝ) : ℝ :=
  Gibbs.Hamiltonian.Entropy.shannonEntropy labelDist

/-- A protocol step carries a message at a given information rate. -/
structure ProtocolStep (X Y : Type*) [Fintype X] [Fintype Y] where
  /-- The typed channel used for this step. -/
  channel : TypedChannel X Y
  /-- Information rate (nats per use). -/
  rate : ℝ

/-- Protocol feasibility: each step fits within channel capacity. -/
def ProtocolFeasible {X Y : Type*} [Fintype X] [Fintype Y]
    (steps : List (ProtocolStep X Y)) : Prop :=
  ∀ s ∈ steps, s.rate ≤ s.channel.capacity

/-- Identify the first infeasible step (if any). -/
def bottleneck {X Y : Type*} [Fintype X] [Fintype Y]
    (steps : List (ProtocolStep X Y)) : Option (ProtocolStep X Y) :=
  steps.find? (fun s => decide (s.channel.capacity < s.rate))

/-! ## Projection as Marginalization -/

/-- Information lost when projecting from joint (X,Y) to marginal X.
    This is H(Y|X) = H(X,Y) - H(X). -/
def projectionInfoLoss {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) : ℝ :=
  Gibbs.Hamiltonian.Entropy.shannonEntropy pXY -
    Gibbs.Hamiltonian.Entropy.shannonEntropy (Gibbs.Hamiltonian.Entropy.marginalFst pXY)

/-- Information retained after projection (mutual information). -/
def projectionInfoRetained {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) : ℝ :=
  Gibbs.Hamiltonian.Entropy.mutualInfo pXY

/-- Projection decomposes total information: H(X,Y) = H(X) + H(Y|X). -/
theorem projection_decomposition {α β : Type*} [Fintype α] [Fintype β]
    (pXY : α × β → ℝ) :
    Gibbs.Hamiltonian.Entropy.shannonEntropy pXY =
      Gibbs.Hamiltonian.Entropy.shannonEntropy (Gibbs.Hamiltonian.Entropy.marginalFst pXY) +
        projectionInfoLoss pXY := by
  unfold projectionInfoLoss
  ring

/-- Feasibility under projection is inherited by each step. -/
theorem projection_preserves_feasibility {X Y : Type*} [Fintype X] [Fintype Y]
    {steps : List (ProtocolStep X Y)} (hf : ProtocolFeasible steps)
    (s : ProtocolStep X Y) (hs : s ∈ steps) :
    s.rate ≤ s.channel.capacity := hf s hs

end

end Gibbs.Hamiltonian.ChannelSession
