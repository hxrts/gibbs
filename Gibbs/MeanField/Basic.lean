import Gibbs.Core

/-
The Problem. We need foundational types for mean-field theory:
population states over finite type spaces, empirical measures
(fractional distributions), and the probability simplex.

These types bridge discrete agent counts with continuous ODEs.
The key insight is that as population size N → ∞, the empirical
measure (counts/N) converges to a point in the simplex.

Solution Structure.
1. PopulationState: integer counts over a finite state space Q
2. Empirical measure: normalized fractions in [0,1]
3. Simplex: the space of valid probability distributions
4. TwoState: canonical two-element type for Ising-like models
5. Magnetization: order parameter m = 2x - 1 for two-state systems
-/

namespace Gibbs.MeanField

open scoped Classical

noncomputable section

/-! ## Population State -/

/-- A population state assigns counts to each state in Q.
    Tracks how many agents are in each local type continuation. -/
structure PopulationState (Q : Type*) [Fintype Q] where
  /-- Count of agents in each state -/
  counts : Q → ℕ
  /-- Total population size -/
  total : ℕ
  /-- Counts sum to total -/
  total_eq : (∑ q, counts q) = total
  /-- Population is non-empty -/
  total_pos : total > 0

namespace PopulationState

variable {Q : Type*} [Fintype Q]

/-- Create a population state from counts, computing total automatically. -/
def mk' (counts : Q → ℕ) (h : ∑ q, counts q > 0) : PopulationState Q where
  counts := counts
  total := ∑ q, counts q
  total_eq := rfl
  total_pos := h

/-- The population size as a positive natural number. -/
def size (s : PopulationState Q) : ℕ+ := ⟨s.total, s.total_pos⟩

/-- Count in a specific state. -/
def countAt (s : PopulationState Q) (q : Q) : ℕ := s.counts q

end PopulationState

/-! ## Empirical Measure -/

/-- The empirical measure maps counts to fractions in [0,1].
    This is the key bridge between discrete and continuous descriptions. -/
def empirical {Q : Type*} [Fintype Q] (s : PopulationState Q) : Q → ℝ :=
  fun q => (s.counts q : ℝ) / s.total

/-- Each component of the empirical measure is non-negative. -/
theorem empirical_nonneg {Q : Type*} [Fintype Q] (s : PopulationState Q) (q : Q) :
    0 ≤ empirical s q := by
  -- Division of non-negative numbers is non-negative
  simp only [empirical]
  apply div_nonneg
  · exact Nat.cast_nonneg (s.counts q)
  · exact Nat.cast_nonneg s.total

/-- The empirical measure sums to 1 (probability conservation). -/
theorem empirical_sum_one {Q : Type*} [Fintype Q] (s : PopulationState Q) :
    ∑ q, empirical s q = 1 := by
  -- Pull division out of sum, use total_eq
  simp only [empirical, ← Finset.sum_div]
  rw [← Nat.cast_sum]
  rw [s.total_eq]
  -- Now: (total : ℝ) / total = 1, using total > 0
  have h : (s.total : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt s.total_pos)
  exact div_self h

/-! ## Probability Simplex -/

/-- The probability simplex over Q: non-negative vectors summing to 1.
    This is the natural state space for mean-field ODEs. -/
def Simplex (Q : Type*) [Fintype Q] : Set (Q → ℝ) :=
  { x | (∀ q, 0 ≤ x q) ∧ ∑ q, x q = 1 }

namespace Simplex

variable {Q : Type*} [Fintype Q]

/-- A point is in the simplex iff it's a valid probability distribution. -/
theorem mem_iff (x : Q → ℝ) : x ∈ Simplex Q ↔ (∀ q, 0 ≤ x q) ∧ ∑ q, x q = 1 :=
  Iff.rfl

/-- The empirical measure of any population state lies in the simplex. -/
theorem empirical_mem (s : PopulationState Q) : empirical s ∈ Simplex Q := by
  constructor
  · exact empirical_nonneg s
  · exact empirical_sum_one s

/-- Each component of a simplex point is at most 1. -/
theorem le_one {x : Q → ℝ} (hx : x ∈ Simplex Q) (q : Q) : x q ≤ 1 := by
  -- x q ≤ sum of all = 1
  have hsum := hx.2
  have hnonneg := hx.1
  calc x q ≤ ∑ q', x q' := Finset.single_le_sum (fun q' _ => hnonneg q') (Finset.mem_univ q)
       _ = 1 := hsum

end Simplex

/-! ## Two-State Systems -/

/-- Canonical two-state type for Ising-like models.
    Represents spin up/down, occupied/empty, active/inactive, etc. -/
inductive TwoState where
  | up : TwoState
  | down : TwoState
  deriving DecidableEq, Repr

namespace TwoState

instance : Fintype TwoState where
  elems := {up, down}
  complete := fun x => by cases x <;> simp

/-- The two states are distinct. -/
theorem up_ne_down : up ≠ down := by decide

/-- Enumeration of all two states. -/
def all : List TwoState := [up, down]

theorem all_complete : ∀ s : TwoState, s ∈ all := by
  intro s; cases s <;> simp [all]

end TwoState

/-! ## Magnetization -/

/-- Fraction of population in the "up" state. -/
def fractionUp (s : PopulationState TwoState) : ℝ :=
  empirical s TwoState.up

/-- Magnetization: the order parameter m = 2x - 1 where x is fraction up.
    - m = +1 when all spins up
    - m = -1 when all spins down
    - m = 0 when evenly split -/
def magnetization (s : PopulationState TwoState) : ℝ :=
  2 * fractionUp s - 1

/-- Magnetization computed directly from an empirical measure. -/
def magnetizationOf (x : TwoState → ℝ) : ℝ :=
  2 * x TwoState.up - 1

/-- Magnetization via PopulationState equals magnetizationOf applied to empirical. -/
theorem magnetization_eq_of (s : PopulationState TwoState) :
    magnetization s = magnetizationOf (empirical s) := by
  simp [magnetization, magnetizationOf, fractionUp]

/-! ## Magnetization Properties -/

/-- Magnetization is bounded: -1 ≤ m ≤ 1 for points in the simplex. -/
theorem magnetizationOf_bounded {x : TwoState → ℝ} (hx : x ∈ Simplex TwoState) :
    -1 ≤ magnetizationOf x ∧ magnetizationOf x ≤ 1 := by
  -- m = 2*x_up - 1, and 0 ≤ x_up ≤ 1
  have h_nonneg := hx.1 TwoState.up
  have h_le_one := Simplex.le_one hx TwoState.up
  constructor
  · -- -1 ≤ 2*x_up - 1 iff 0 ≤ x_up
    simp only [magnetizationOf]
    linarith
  · -- 2*x_up - 1 ≤ 1 iff x_up ≤ 1
    simp only [magnetizationOf]
    linarith

/-- Inverse: recover fraction up from magnetization. -/
def fractionUpOf (m : ℝ) : ℝ := (m + 1) / 2

/-- Round-trip: magnetization and fractionUp are inverses. -/
theorem fractionUpOf_magnetizationOf (x : TwoState → ℝ) :
    fractionUpOf (magnetizationOf x) = x TwoState.up := by
  simp only [fractionUpOf, magnetizationOf]
  ring

end

end Gibbs.MeanField
