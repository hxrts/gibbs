import Gibbs.Consensus.Basic
import Mathlib.Data.Set.Basic
import Gibbs.Hamiltonian.PartitionFunction

/-!
# Partition function over executions

The Boltzmann partition function `Z = Σ_ω exp(-β H(ω))` summed over
executions, where `H(ω)` is the total inconsistency energy (conflict + delay +
fault penalties). The inverse temperature `β` interpolates between analysis
regimes. As `β → ∞` only minimum-energy executions survive, recovering
worst-case analysis. At finite `β` executions are weighted probabilistically,
giving average-case behavior.

The restricted variants `partitionFunctionOn` and `freeEnergyOn` sum only
over an admissible subset `Ω`, modelling the adversary's constraint on which
executions are reachable.
-/

namespace Gibbs.Consensus

noncomputable section

open Gibbs.Hamiltonian.PartitionFunction

/-! ## Partition Function on Executions -/

/-- Partition function specialized to consensus executions. -/
abbrev partitionFunction {Exec : Type} [Fintype Exec]
    (H : Exec → ℝ) (β : ℝ) : ℝ :=
  Gibbs.Hamiltonian.PartitionFunction.partitionFunction H β

/-- Free energy specialized to consensus executions. -/
abbrev freeEnergy {Exec : Type} [Fintype Exec]
    (H : Exec → ℝ) (β : ℝ) : ℝ :=
  Gibbs.Hamiltonian.PartitionFunction.freeEnergy H β

/-- Nonnegativity of the partition function (consensus specialization). -/
theorem partitionFunction_nonneg {Exec : Type} [Fintype Exec]
    (H : Exec → ℝ) (β : ℝ) : 0 ≤ partitionFunction H β := by
  -- Delegate to the physics-first lemma.
  exact Gibbs.Hamiltonian.PartitionFunction.partitionFunction_nonneg H β

/-- Partition function specialized to finite-horizon executions. -/
abbrev executionPartitionFunction {N : ℕ} {S : Type} {T : ℕ}
    [Fintype (Execution N S T)] (H : Execution N S T → ℝ) (β : ℝ) : ℝ :=
  partitionFunction H β

/-- Free energy specialized to finite-horizon executions. -/
abbrev executionFreeEnergy {N : ℕ} {S : Type} {T : ℕ}
    [Fintype (Execution N S T)] (H : Execution N S T → ℝ) (β : ℝ) : ℝ :=
  freeEnergy H β

/-! ## Partition Function on Execution Subsets -/

/-- Partition function restricted to an admissible execution set `Ω`. -/
def partitionFunctionOn {Exec : Type} [Fintype Exec] [DecidableEq Exec]
    (H : Exec → ℝ) (β : ℝ) (Ω : Set Exec) : ℝ := by
  classical
  exact ∑ ω, (if ω ∈ Ω then Real.exp (-β * H ω) else 0)

/-- Free energy on an admissible execution set `Ω`. -/
def freeEnergyOn {Exec : Type} [Fintype Exec] [DecidableEq Exec]
    (H : Exec → ℝ) (β : ℝ) (Ω : Set Exec) : ℝ := by
  classical
  exact - (1 / β) * Real.log (partitionFunctionOn H β Ω)

end

end Gibbs.Consensus
