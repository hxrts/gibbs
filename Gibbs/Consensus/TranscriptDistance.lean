import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ENNReal.Basic
import Gibbs.Consensus.Basic
import Gibbs.Consensus.Adversary

/-!
# Transcript distance

The metric on executions that measures how many processes were corrupted.
Two executions are close if they differ on few processes' local traces. This
is the Hamming distance lifted from codeword positions to process identities.

In coding theory, Hamming distance determines the error-correction radius.
Here it plays the same role. If the adversary can corrupt at most `f`
processes, the adversary ball has radius `f` in this metric, and safety holds
when the distance between good and bad macrostates exceeds `f`. The
pseudometric properties (reflexivity, symmetry, triangle inequality) are
proved so this distance plugs into the energy-distance framework from the
Hamiltonian layer.
-/

namespace Gibbs.Consensus

open scoped ENNReal

noncomputable section

open scoped BigOperators

/-! ## Hamming Distance -/

/-- The finite set of indices where two functions disagree. -/
def diffSet {ι α : Type} [Fintype ι] [DecidableEq α]
    (x y : ι → α) : Finset ι := by
  -- Filter the index set by disagreement.
  exact Finset.univ.filter (fun i => x i ≠ y i)

/-- Hamming distance as an `ℝ≥0∞`-valued sum of disagreement indicators. -/
def hammingDistance {ι α : Type} [Fintype ι] [DecidableEq α]
    (x y : ι → α) : ℝ≥0∞ := by
  -- Sum the per-index indicators in `ℝ≥0∞`.
  exact ∑ i, (if x i = y i then (0 : ℝ≥0∞) else 1)

/-- Hamming distance is zero on identical inputs. -/
theorem hammingDistance_self {ι α : Type} [Fintype ι] [DecidableEq α]
    (x : ι → α) : hammingDistance x x = 0 := by
  classical
  -- Each indicator is zero.
  simp [hammingDistance]

/-- Hamming distance is symmetric. -/
theorem hammingDistance_comm {ι α : Type} [Fintype ι] [DecidableEq α]
    (x y : ι → α) : hammingDistance x y = hammingDistance y x := by
  classical
  -- Swap the arguments inside the indicator.
  simp [hammingDistance, eq_comm]

/-- Hamming distance satisfies the triangle inequality. -/
theorem hammingDistance_triangle {ι α : Type} [Fintype ι] [DecidableEq α]
    (x y z : ι → α) :
    hammingDistance x z ≤ hammingDistance x y + hammingDistance y z := by
  classical
  -- Prove the pointwise indicator bound and sum over indices.
  have hpoint : ∀ i, (if x i = z i then (0 : ℝ≥0∞) else 1) ≤
      (if x i = y i then (0 : ℝ≥0∞) else 1) +
      (if y i = z i then (0 : ℝ≥0∞) else 1) := by
    intro i
    by_cases hxz : x i = z i
    · -- If equal, the left indicator is zero.
      simp [hxz]
    · -- Otherwise at least one of the two comparisons must differ.
      by_cases hxy : x i = y i
      ·
        have hyz : y i ≠ z i := by
          intro hyz
          apply hxz
          simp [hxy, hyz]
        simp [hxy, hyz]
      ·
        simp [hxz, hxy]
  -- Sum the pointwise inequality by induction over the finite index set.
  let f : ι → ℝ≥0∞ := fun i => if x i = z i then 0 else 1
  let g : ι → ℝ≥0∞ := fun i =>
    (if x i = y i then 0 else 1) + (if y i = z i then 0 else 1)
  have hsum' : ∑ i, f i ≤ ∑ i, g i := by
    classical
    -- Induction on the finite index set `Finset.univ`.
    refine Finset.induction_on (Finset.univ : Finset ι) ?base ?step
    · simp
    · intro a s ha hs
      have hfa : f a ≤ g a := hpoint a
      have hsum_step : f a + Finset.sum s f ≤ g a + Finset.sum s g := by
        exact add_le_add hfa hs
      simpa [Finset.sum_insert, ha] using hsum_step
  -- Split the sum of pointwise sums.
  have hsum :
      ∑ i, (if x i = z i then (0 : ℝ≥0∞) else 1) ≤
        ∑ i, (if x i = y i then (0 : ℝ≥0∞) else 1) +
          ∑ i, (if y i = z i then (0 : ℝ≥0∞) else 1) := by
    simpa [f, g, Finset.sum_add_distrib] using hsum'
  simpa [hammingDistance] using hsum

/-! ## Process-Corruption Distance -/

/-- The local trace of a process across an execution. -/
def localTrace {N : ℕ} {S : Type} {T : ℕ}
    (ω : Execution N S T) (i : Process N) : Fin (T + 1) → S := by
  -- Read the configuration component at index `i` for each time.
  exact fun t => ω t i

/-- Process-corruption distance: count processes with differing local traces. -/
def processDistance {N : ℕ} {S : Type} {T : ℕ} [DecidableEq S]
    (ω ω' : Execution N S T) : ℝ≥0∞ := by
  -- Apply Hamming distance to the per-process traces.
  exact hammingDistance (fun i => localTrace ω i) (fun i => localTrace ω' i)

/-- Process distance is symmetric. -/
theorem processDistance_comm {N : ℕ} {S : Type} {T : ℕ} [DecidableEq S]
    (ω ω' : Execution N S T) : processDistance ω ω' = processDistance ω' ω := by
  -- Inherit symmetry from Hamming distance.
  exact hammingDistance_comm _ _

/-- Process distance is zero on identical executions. -/
theorem processDistance_self {N : ℕ} {S : Type} {T : ℕ} [DecidableEq S]
    (ω : Execution N S T) : processDistance ω ω = 0 := by
  -- Inherit reflexivity from Hamming distance.
  exact hammingDistance_self _

/-- Process distance satisfies the triangle inequality. -/
theorem processDistance_triangle {N : ℕ} {S : Type} {T : ℕ} [DecidableEq S]
    (ω ω' ω'' : Execution N S T) :
    processDistance ω ω'' ≤ processDistance ω ω' + processDistance ω' ω'' := by
  -- Inherit triangle inequality from Hamming distance.
  exact hammingDistance_triangle _ _ _

/-! ## Adversary Ball vs Distance Ball -/

/-- A distance ball for an arbitrary execution distance. -/
def distanceBall {Exec : Type} (d : Exec → Exec → ℝ≥0∞)
    (ω : Exec) (r : ℝ≥0∞) : Set Exec := by
  -- Points within distance `r` of `ω`.
  exact { ω' | d ω ω' ≤ r }

/-- If each allowed transform stays within budget, adversary balls are distance balls. -/
theorem adversaryBall_subset_distanceBall {Exec : Type}
    (A : AdversaryClass Exec) (d : Exec → Exec → ℝ≥0∞) (ω : Exec)
    (h : ∀ T ∈ A.allowed, ∀ ω, d ω (T ω) ≤ A.budget) :
    adversaryBall A ω ⊆ distanceBall d ω A.budget := by
  -- Unpack the witness transform and apply the budget hypothesis.
  intro ω' hω'
  rcases hω' with ⟨T, hT, rfl⟩
  exact h T hT ω


end

end Gibbs.Consensus
