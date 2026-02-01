import Mathlib.Data.Finset.Card
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import Gibbs.Consensus.TranscriptDistance

/-!
# Repetition code example

The simplest gapped phase in the consensus/coding framework. Encoding one
bit as `N` identical copies is the coding-theory analogue of a fully
aligned Ising ferromagnet, and majority-vote decoding is the analogue of
measuring the magnetization sign.

The code distance is `N` (all positions must differ between the two
codewords), so majority decoding corrects up to `⌊(N-1)/2⌋` errors.
This matches the `2f+1` static threshold: you need `N ≥ 2f+1` to
tolerate `f` corruptions, and the gap is `N - 2f > 0`.
-/

namespace Gibbs.Consensus.Examples

/-! ## Repetition Code -/

/-- A codeword of length `N` over bits. -/
abbrev Codeword (N : ℕ) : Type := Fin N → Bool

/-- Repetition encoding: repeat the input bit across all positions. -/
def repetitionEncode {N : ℕ} (b : Bool) : Codeword N := by
  -- Every coordinate stores the same bit.
  exact fun _ => b

/-- Count the number of `true` bits in a codeword. -/
def countTrue {N : ℕ} (w : Codeword N) : Nat := by
  -- Filter the indices where the bit is true.
  exact (Finset.univ.filter (fun i => w i)).card

/-- Majority decoding: choose `true` if it appears at least half the time. -/
def majorityDecode {N : ℕ} (w : Codeword N) : Bool := by
  -- Break ties in favor of `true`.
  exact decide (2 * countTrue w ≥ N)

/-- Error count relative to a transmitted bit. -/
def errorCount {N : ℕ} (b : Bool) (w : Codeword N) : Nat := by
  -- Count positions that differ from the transmitted bit.
  exact (Finset.univ.filter (fun i => w i ≠ b)).card

/-- Correctness up to a radius `t`. -/
def CorrectsUpTo {N : ℕ} (t : Nat) : Prop := by
  -- All words with at most `t` errors decode to the original bit.
  exact ∀ b w, errorCount (N := N) b w ≤ t → majorityDecode w = b

/-! ## Counting Lemmas -/

/-- Error count for `false` equals the number of `true` bits. -/
lemma countTrue_eq_errorCount_false {N : ℕ} (w : Codeword N) :
    countTrue w = errorCount (N := N) false w := by
  classical
  simp [countTrue, errorCount]

/-- The number of `true` bits plus the `true`-error count equals `N`. -/
lemma countTrue_add_errorCount_true {N : ℕ} (w : Codeword N) :
    countTrue w + errorCount (N := N) true w = N := by
  classical
  have hcard :
      (Finset.univ.filter (fun i => w i)).card +
        (Finset.univ.filter (fun i => ¬ w i)).card =
          (Finset.univ : Finset (Fin N)).card := by
    simpa using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin N))) (p := fun i => w i))
  have hfilter :
      Finset.univ.filter (fun i => ¬ w i) =
        Finset.univ.filter (fun i => w i ≠ true) := by
    classical
    ext i
    by_cases hwi : w i <;> simp [hwi]
  calc
    countTrue w + errorCount (N := N) true w
        = (Finset.univ.filter (fun i => w i)).card +
            (Finset.univ.filter (fun i => ¬ w i)).card := by
            simp [countTrue, errorCount]
    _ = (Finset.univ : Finset (Fin N)).card := hcard
    _ = N := by simp

/-- The standard `2 * ((N-1)/2)` bound. -/
lemma two_mul_div_le_pred (N : ℕ) :
    2 * ((N - 1) / 2) ≤ N - 1 := by
  simpa [Nat.mul_comm] using (Nat.mul_div_le (N - 1) 2)

/-! ## Majority Decode Helpers -/

/-- If `2 * countTrue < N`, majority decoding returns `false`. -/
lemma majorityDecode_false_of_lt {N : ℕ} (w : Codeword N)
    (h : 2 * countTrue w < N) : majorityDecode w = false := by
  have hdec : decide (2 * countTrue w ≥ N) = false :=
    decide_eq_false_iff_not.mpr (Nat.not_le.mpr h)
  simp [majorityDecode, hdec]

/-- If `N ≤ 2 * countTrue`, majority decoding returns `true`. -/
lemma majorityDecode_true_of_le {N : ℕ} (w : Codeword N)
    (h : N ≤ 2 * countTrue w) : majorityDecode w = true := by
  have hdec : decide (2 * countTrue w ≥ N) = true :=
    decide_eq_true_iff.mpr h
  simp [majorityDecode, hdec]

/-- Error bound for `false` implies `2 * countTrue < N`. -/
lemma countTrue_lt_of_errorCount_false {N : ℕ} (hN : 0 < N) {w : Codeword N}
    (hErr : errorCount (N := N) false w ≤ (N - 1) / 2) :
    2 * countTrue w < N := by
  have hcount : countTrue w ≤ (N - 1) / 2 := by
    simpa [countTrue_eq_errorCount_false] using hErr
  have hle1 : 2 * countTrue w ≤ 2 * ((N - 1) / 2) :=
    Nat.mul_le_mul_left 2 hcount
  have hle2 : 2 * ((N - 1) / 2) ≤ N - 1 :=
    two_mul_div_le_pred N
  have hle : 2 * countTrue w ≤ N - 1 := le_trans hle1 hle2
  have hN1 : 1 ≤ N := Nat.succ_le_iff.mpr hN
  have hltN : N - 1 < N := Nat.sub_lt_of_pos_le (by decide : 0 < 1) hN1
  exact lt_of_le_of_lt hle hltN

/-- Error bound for `true` implies `N ≤ 2 * countTrue`. -/
lemma countTrue_ge_of_errorCount_true {N : ℕ} {w : Codeword N}
    (hErr : errorCount (N := N) true w ≤ (N - 1) / 2) :
    N ≤ 2 * countTrue w := by
  set t : ℕ := (N - 1) / 2
  have hsum : countTrue w + errorCount (N := N) true w = N :=
    countTrue_add_errorCount_true w
  have hcount_eq : countTrue w = N - errorCount (N := N) true w :=
    Nat.eq_sub_of_add_eq hsum
  have hcount_ge : N - t ≤ countTrue w := by
    have hle : N - t ≤ N - errorCount (N := N) true w :=
      Nat.sub_le_sub_left hErr N
    simpa [hcount_eq, t] using hle
  have h2t_le : 2 * t ≤ N - 1 := two_mul_div_le_pred N
  have h2t_leN : 2 * t ≤ N := le_trans h2t_le (Nat.sub_le _ _)
  have ht_le : t ≤ N := by
    have ht_le' : t ≤ N - 1 := Nat.div_le_self (N - 1) 2
    exact le_trans ht_le' (Nat.sub_le _ _)
  have h2t_le2N : 2 * t ≤ 2 * N := Nat.mul_le_mul_left 2 ht_le
  have hNle : N ≤ 2 * N - 2 * t := by
    have hle : N + 2 * t ≤ 2 * N := by
      simpa [two_mul] using (Nat.add_le_add_left h2t_leN N)
    exact (Nat.le_sub_iff_add_le (n := N) (m := 2 * N) (k := 2 * t) h2t_le2N).2 hle
  have hNle' : N ≤ 2 * (N - t) := by
    simpa [Nat.mul_sub_left_distrib, t] using hNle
  have hcount' : 2 * (N - t) ≤ 2 * countTrue w :=
    Nat.mul_le_mul_left 2 hcount_ge
  exact le_trans hNle' hcount'

/-- On an uncorrupted repetition codeword, majority decoding returns the bit. -/
theorem majorityDecode_repetition {N : ℕ} (hN : 0 < N) (b : Bool) :
    majorityDecode (repetitionEncode (N := N) b) = b := by
  classical
  -- Compute the count of `true` bits for each case.
  cases b
  · -- b = false
    have hcount : countTrue (repetitionEncode (N := N) false) = 0 := by
      simp [countTrue, repetitionEncode]
    have hlt : 2 * countTrue (repetitionEncode (N := N) false) < N := by
      -- `N` is positive, so `0 < N`.
      simpa [hcount] using hN
    have hnot : ¬ (2 * countTrue (repetitionEncode (N := N) false) ≥ N) := by
      exact Nat.not_le.mpr hlt
    have hdec : decide (2 * countTrue (repetitionEncode (N := N) false) ≥ N) = false :=
      decide_eq_false_iff_not.mpr hnot
    simpa [majorityDecode] using hdec
  · -- b = true
    have hcount : countTrue (repetitionEncode (N := N) true) = N := by
      simp [countTrue, repetitionEncode]
    have hge : 2 * countTrue (repetitionEncode (N := N) true) ≥ N := by
      have hle : N ≤ 2 * N := Nat.le_mul_of_pos_left N (by decide : 0 < (2:Nat))
      simpa [hcount, Nat.mul_comm] using hle
    have hdec : decide (2 * countTrue (repetitionEncode (N := N) true) ≥ N) = true :=
      decide_eq_true_iff.mpr hge
    simpa [majorityDecode] using hdec

/-! ## Error-Correction Radius -/

/-- Majority decoding corrects `⌊(N-1)/2⌋` errors for the repetition code. -/
theorem repetition_corrects_up_to {N : ℕ} (hN : 0 < N) :
    CorrectsUpTo (N := N) ((N - 1) / 2) := by
  intro b w hErr
  cases b
  · exact
      majorityDecode_false_of_lt w
        (countTrue_lt_of_errorCount_false hN hErr)
  · exact
      majorityDecode_true_of_le w
        (countTrue_ge_of_errorCount_true hErr)

end Gibbs.Consensus.Examples
