import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Consensus Hamiltonian decomposition

The effective Hamiltonian for consensus decomposes into three physical terms:

- `H_conflict` penalizes conflicting decisions (the "anti-ferromagnetic"
  energy that consensus must overcome).
- `H_delay` penalizes prolonged indecision, driving the system toward a
  decided state (analogous to an external field that breaks symmetry).
- `H_fault` encodes adversarial or crash behavior, raising the energy of
  executions where faulty processes disrupt communication.

Safety invariants correspond to *forbidden regions* of execution space where
the total energy is `+∞`. These regions have zero Boltzmann weight and are
automatically excluded from partition-function sums, ensuring that no
thermodynamic average ever crosses a safety boundary.
-/

namespace Gibbs.Consensus

open scoped ENNReal

noncomputable section

/-! ## Hamiltonian Decomposition -/

/-- A consensus Hamiltonian decomposed into conflict, delay, and fault terms. -/
structure ConsensusHamiltonian (Exec : Type) where
  /-- Penalizes conflicting decisions. -/
  conflict : Exec → ℝ
  /-- Penalizes prolonged indecision / delay. -/
  delay : Exec → ℝ
  /-- Encodes adversarial or faulty behavior. -/
  fault : Exec → ℝ

/-- Total energy as the sum of the three consensus components. -/
def totalEnergy {Exec : Type} (H : ConsensusHamiltonian Exec) : Exec → ℝ := by
  exact fun ω => H.conflict ω + H.delay ω + H.fault ω

/-! ## Forbidden Regions -/

/-- Lift an energy function by assigning `∞` to a forbidden execution set. -/
def forbiddenEnergy {Exec : Type} (E : Exec → ℝ≥0∞) (Bad : Set Exec) :
    Exec → ℝ≥0∞ := by
  classical
  exact fun ω => if ω ∈ Bad then ∞ else E ω

/-- Convert a (possibly infinite) energy into a Boltzmann weight. -/
def energyWeight (β : ℝ) (E : ℝ≥0∞) : ℝ := by
  exact if E = ∞ then 0 else Real.exp (-β * E.toReal)

/-- Forbidden executions carry zero Boltzmann weight. -/
theorem energyWeight_forbidden {Exec : Type} {E : Exec → ℝ≥0∞}
    {Bad : Set Exec} (β : ℝ) {ω : Exec} (hω : ω ∈ Bad) :
    energyWeight β (forbiddenEnergy E Bad ω) = 0 := by
  classical
  simp [energyWeight, forbiddenEnergy, hω]

/-- Allowed executions keep their original weights. -/
theorem energyWeight_allowed {Exec : Type} {E : Exec → ℝ≥0∞}
    {Bad : Set Exec} (β : ℝ) {ω : Exec} (hω : ω ∉ Bad) :
    energyWeight β (forbiddenEnergy E Bad ω) = energyWeight β (E ω) := by
  classical
  simp [energyWeight, forbiddenEnergy, hω]

end

end Gibbs.Consensus
