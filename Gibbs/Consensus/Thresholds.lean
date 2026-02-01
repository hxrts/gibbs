import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Gibbs.Consensus.Quorum
import Gibbs.Consensus.InteractiveDistance

/-!
# Byzantine thresholds from distance conditions

The classic `2f+1` and `3f+1` bounds are not protocol artifacts but phase
boundaries. The `2f+1` threshold comes from static unique decoding: a
repetition code of length `N` corrects `f` errors iff `N > 2f`, i.e.
the code distance exceeds twice the error budget. The `3f+1` threshold
comes from interactive distance: quorum intersection guarantees that
conflicting certificates require corrupting more than `f` processes,
but only when `N ≥ 3f+1`.

The fraction bounds show that these thresholds correspond to corruption
fractions `α < 1/2` (static) and `α < 1/3` (interactive).
-/

namespace Gibbs.Consensus

open scoped ENNReal

noncomputable section

/-! ## Thresholds from Distance Conditions -/

/-- Static threshold for repetition code: if `N ≥ 2f+1` then `N > 2f`. -/
theorem repetition_threshold {N f : ℕ} (hN : N ≥ 2 * f + 1) : N > 2 * f := by
  -- Immediate arithmetic.
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (2 * f)) hN

/-- Quorum intersection threshold specialized to `N = 3f+1`. -/
theorem quorum_threshold {N f : ℕ} {Q Q' : Finset (Fin N)}
    (hN : N = 3 * f + 1)
    (hQ : Q.card = 2 * f + 1) (hQ' : Q'.card = 2 * f + 1) :
    (Q ∩ Q').card ≥ f + 1 := by
  -- Reuse the specialized intersection lemma.
  exact quorum_intersection_3f1 (N := N) (f := f) hN hQ hQ'

/-- Gap condition implied by the quorum intersection bound. -/
theorem quorum_gap_implies {N f : ℕ} {Q Q' : Finset (Fin N)}
    (hN : N = 3 * f + 1)
    (hQ : Q.card = 2 * f + 1) (hQ' : Q'.card = 2 * f + 1) :
    f + 1 ≤ (Q ∩ Q').card := by
  -- Restate the previous lemma in the requested inequality direction.
  exact quorum_intersection_3f1 (N := N) (f := f) hN hQ hQ'

/-! ## Fraction Bounds -/

/-- Corruption fraction `f / N` as a real number. -/
def corruptionFraction (f N : ℕ) : ℝ := (f : ℝ) / N

/-- Static decoding bound: `⌊(N-1)/2⌋ / N < 1/2` for `N > 0`. -/
theorem static_fraction_bound {N : ℕ} (hN : 0 < N) :
    corruptionFraction ((N - 1) / 2) N < (1 : ℝ) / 2 := by
  have h2t : 2 * ((N - 1) / 2) < N := by
    have hle : 2 * ((N - 1) / 2) ≤ N - 1 :=
      by simpa [Nat.mul_comm] using (Nat.mul_div_le (N - 1) 2)
    have hN1 : 1 ≤ N := Nat.succ_le_iff.mpr hN
    have hltN : N - 1 < N := Nat.sub_lt_of_pos_le (by decide : 0 < 1) hN1
    exact lt_of_le_of_lt hle hltN
  have h2t' : (2 : ℝ) * ((N - 1) / 2 : ℕ) < (N : ℝ) := by
    exact_mod_cast h2t
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : ((N - 1) / 2 : ℕ) < (1 / 2 : ℝ) * N := by
    nlinarith [h2t']
  have hdiv : ((N - 1) / 2 : ℕ) / (N : ℝ) < (1 : ℝ) / 2 := by
    exact (div_lt_iff₀ hNpos).2 (by simpa [mul_comm] using ht)
  simpa [corruptionFraction] using hdiv

/-- Interactive bound at `N = 3f + 1`: corruption fraction is below `1/3`. -/
theorem interactive_fraction_bound {f : ℕ} :
    corruptionFraction f (3 * f + 1) < (1 : ℝ) / 3 := by
  have hpos : (0 : ℝ) < (3 * f + 1 : ℝ) := by nlinarith
  have hf : (f : ℝ) < (1 / 3 : ℝ) * (3 * f + 1) := by nlinarith
  have hdiv : (f : ℝ) / (3 * f + 1 : ℝ) < (1 : ℝ) / 3 := by
    exact (div_lt_iff₀ hpos).2 (by simpa [mul_comm] using hf)
  simpa [corruptionFraction] using hdiv

end

end Gibbs.Consensus
