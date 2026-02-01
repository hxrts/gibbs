import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Basic
import Gibbs.Hamiltonian.EnergyGap
import Gibbs.Consensus.PartitionFunction
import Gibbs.Consensus.InteractiveDistance

/-!
# Gaps, safety, and finality

The gap between ordered and disordered phases determines whether a protocol
has *finality*. A positive energy gap between good (agreement) and bad
(disagreement) execution sets means the adversary must pay a macroscopic cost
to push the system from one phase to the other. This is deterministic safety.

A positive *free-energy* gap `ΔF > 0` provides exponential suppression of
unsafe outcomes, with reversal probability scaling as `exp(-ΔF)`. When `ΔF`
grows with `N` the system has finality in the thermodynamic limit. When
`ΔF = 0` (no gap) competing histories coexist and only probabilistic finality
is possible. This is the Nakamoto regime.
-/

namespace Gibbs.Consensus

open scoped ENNReal

noncomputable section

open Gibbs.Hamiltonian
open scoped BigOperators

/-! ## Energy Gaps on Executions -/

/-- Energy gap between two execution sets, using the physics-first definition. -/
abbrev energyGap {Exec : Type} [EnergyDistance Exec] (A B : Set Exec) : ℝ≥0∞ :=
  Gibbs.Hamiltonian.energyGap A B

/-- A pair of execution sets has a positive energy gap. -/
abbrev HasEnergyGap {Exec : Type} [EnergyDistance Exec] (A B : Set Exec) : Prop :=
  Gibbs.Hamiltonian.HasEnergyGap A B

/-! ## Free-Energy Gaps -/

/-- Partition function restricted to a subset of executions. -/
def restrictedPartitionFunction {Exec : Type} [Fintype Exec] [DecidableEq Exec]
    (H : Exec → ℝ) (β : ℝ) (A : Set Exec) : ℝ := by
  classical
  -- Sum the Boltzmann weights only over the subset.
  exact ∑ ω, (if ω ∈ A then Real.exp (-β * H ω) else 0)

/-- Free energy restricted to a subset of executions. -/
def restrictedFreeEnergy {Exec : Type} [Fintype Exec] [DecidableEq Exec]
    (H : Exec → ℝ) (β : ℝ) (A : Set Exec) : ℝ := by
  classical
  -- Apply the usual `-(1/β) log` definition on the restricted partition function.
  exact - (1 / β) * Real.log (restrictedPartitionFunction H β A)

/-- Restricted partition functions agree with the subset partition function. -/
theorem partitionFunctionOn_eq_restricted {Exec : Type} [Fintype Exec] [DecidableEq Exec]
    (H : Exec → ℝ) (β : ℝ) (A : Set Exec) :
    Gibbs.Consensus.partitionFunctionOn H β A = restrictedPartitionFunction H β A := by
  rfl

/-- Free-energy gap between two subsets (B relative to A). -/
def freeEnergyGap {Exec : Type} [Fintype Exec] [DecidableEq Exec]
    (H : Exec → ℝ) (β : ℝ) (A B : Set Exec) : ℝ := by
  -- Positive values mean B is higher free energy than A.
  exact restrictedFreeEnergy H β B - restrictedFreeEnergy H β A

/-! ## Safety and Finality -/

/-- The set of executions that realize a given macrostate. -/
def Macroset {Exec M : Type} (dec : Exec → M) (m : M) : Set Exec := by
  -- Reuse the macrostate-set definition.
  exact macrostateSet dec m

/-- Safety: no execution realizes a bad macrostate. -/
def IsSafe {Exec M : Type} (dec : Exec → M) (Bad : Set M) : Prop := by
  -- Bad macrostates are forbidden.
  exact ∀ ω, dec ω ∈ Bad → False

/-- Safety gap in terms of interactive distance between good and bad macrostates. -/
def HasSafetyGap {Exec M : Type} (d : Exec → Exec → ℝ≥0∞)
    (dec : Exec → M) (Good Bad : Set M) (b : ℝ≥0∞) : Prop := by
  -- Any good macrostate is more than `b` away from any bad macrostate.
  exact ∀ m ∈ Good, ∀ m' ∈ Bad, b < interactiveDistance d dec m m'

/-- Finality: a safety gap that scales (parameterized by a function of N). -/
def HasFinality {Exec M : Type} (d : Exec → Exec → ℝ≥0∞)
    (dec : Exec → M) (Good Bad : Set M) (b : ℝ≥0∞) : Prop := by
  -- This definition reuses the safety-gap predicate for now.
  exact HasSafetyGap d dec Good Bad b

/-- Probabilistic finality: no hard gap but a positive free-energy difference. -/
def HasProbabilisticFinality {Exec : Type} [Fintype Exec] [DecidableEq Exec]
    (H : Exec → ℝ) (β : ℝ) (A B : Set Exec) : Prop := by
  -- Positive free-energy gap provides exponential suppression.
  exact 0 < freeEnergyGap H β A B

end

end Gibbs.Consensus
