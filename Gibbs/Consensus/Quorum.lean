import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Quorum systems

Quorums are the stabilizing interactions of BFT consensus, analogous to the
coupling constants in a ferromagnet. Any two quorums of size `q` in a system
of `N` processes must overlap in at least `2q - N` members (by inclusion-
exclusion on a finite set). Setting `q = 2f+1` and `N = 3f+1` yields an
overlap of at least `f+1`, strictly more than the adversary's budget `f`.
This honest majority in every intersection is what creates the energy barrier
(gap) between agreement and disagreement macrostates.
-/

namespace Gibbs.Consensus

/-! ## Quorums -/

/-- A quorum is a finite subset of processes of a given size. -/
def IsQuorum {N : ℕ} (q : ℕ) (Q : Finset (Fin N)) : Prop :=
  Q.card = q

/-- General intersection lower bound for equal-size quorums. -/
theorem quorum_intersection_lower {N q : ℕ} {Q Q' : Finset (Fin N)}
    (hQ : Q.card = q) (hQ' : Q'.card = q) :
    (Q ∩ Q').card ≥ q + q - N := by
  -- Bound the union by the total number of processes.
  have hcard_union : (Q ∪ Q').card ≤ N := by
    simpa using (Finset.card_le_univ (s := Q ∪ Q'))
  -- Express the intersection size via inclusion–exclusion.
  have hcard_inter : (Q ∩ Q').card = Q.card + Q'.card - (Q ∪ Q').card := by
    simpa using (Finset.card_inter Q Q')
  -- Substitute the quorum sizes.
  have hcard_inter' : (Q ∩ Q').card = q + q - (Q ∪ Q').card := by
    simpa [hQ, hQ'] using hcard_inter
  -- Use monotonicity of subtraction.
  have hsub : q + q - N ≤ q + q - (Q ∪ Q').card := by
    exact Nat.sub_le_sub_left hcard_union (q + q)
  -- Conclude the lower bound.
  have : q + q - N ≤ (Q ∩ Q').card := by
    simpa [hcard_inter'] using hsub
  exact this

/-- Standard BFT intersection bound at `N = 3f + 1` and `q = 2f + 1`. -/
theorem quorum_intersection_3f1 {N f : ℕ} {Q Q' : Finset (Fin N)}
    (hN : N = 3 * f + 1)
    (hQ : Q.card = 2 * f + 1) (hQ' : Q'.card = 2 * f + 1) :
    (Q ∩ Q').card ≥ f + 1 := by
  -- Start from the general lower bound.
  have hlower : (Q ∩ Q').card ≥ (2 * f + 1) + (2 * f + 1) - N := by
    simpa [hQ, hQ'] using (quorum_intersection_lower (N := N) (q := 2 * f + 1) hQ hQ')
  -- Simplify the right-hand side using `N = 3f + 1`.
  have hcalc : (2 * f + 1) + (2 * f + 1) - N = f + 1 := by
    have hsum : (2 * f + 1) + (2 * f + 1) = 3 * f + 1 + (f + 1) := by
      -- Pure arithmetic on naturals.
      ring
    calc
      (2 * f + 1) + (2 * f + 1) - N
          = (3 * f + 1 + (f + 1)) - (3 * f + 1) := by
              simp [hN, hsum]
      _ = f + 1 := by
          exact Nat.add_sub_cancel_left (3 * f + 1) (f + 1)
  -- Finish with the simplified bound.
  simpa [hcalc] using hlower

end Gibbs.Consensus
