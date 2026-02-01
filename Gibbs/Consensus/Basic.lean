import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Consensus execution model

The degrees of freedom of a consensus system. A system of `N` processes, each
carrying a local state from some type `S`, evolves through a finite sequence of
global configurations. This is the "microstate space" over which partition
functions, distances, and order parameters are later defined.

Keeping the execution horizon finite (`Fin (T+1)` time steps) ensures all
configuration spaces are `Fintype`, so Boltzmann sums are ordinary finite sums
and no measure theory is needed at this level.
-/

namespace Gibbs.Consensus

/-! ## Processes and Executions -/

/-- Process indices for a system with `N` processes. -/
abbrev Process (N : ℕ) : Type := Fin N

/-- Global configuration: a local state per process. -/
abbrev Config (N : ℕ) (S : Type) : Type := Process N → S

/-- Finite-horizon execution as a sequence of configurations. -/
abbrev Execution (N : ℕ) (S : Type) (T : ℕ) : Type := Fin (T + 1) → Config N S

/-- The initial configuration of a finite-horizon execution. -/
def initialConfig {N : ℕ} {S : Type} {T : ℕ} (ω : Execution N S T) : Config N S := by
  -- Index the execution at time 0.
  exact ω ⟨0, Nat.succ_pos _⟩

end Gibbs.Consensus
