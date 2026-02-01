import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Gibbs.Consensus.Quorum
import Gibbs.Consensus.Thresholds

/-!
# Quorum-based BFT example

Instantiates the framework at `N = 3f+1` with quorum size `q = 2f+1`,
the standard BFT setting. The key result is that any two quorums intersect
in at least `f+1` processes, which exceeds the adversary budget `f`. This
honest majority in every intersection is the energy barrier that makes the
system gapped (Class II).

The gap-collapse construction at `N = 3f` exhibits three disjoint blocks
of size `f` and shows that two quorums of size `2f` can intersect in
exactly `f` processes, matching the adversary budget. At this point the
barrier vanishes and safety can no longer be guaranteed. This is the phase
boundary `α = 1/3`.
-/

namespace Gibbs.Consensus.Examples

/-! ## Quorum-Based BFT Example -/

/-- In a 3f+1 system with 2f+1 quorums, any two quorums intersect in ≥ f+1. -/
theorem quorum_intersection_example {N f : ℕ} {Q Q' : Finset (Fin N)}
    (hN : N = 3 * f + 1)
    (hQ : Q.card = 2 * f + 1) (hQ' : Q'.card = 2 * f + 1) :
    (Q ∩ Q').card ≥ f + 1 := by
  -- Reuse the consensus quorum threshold lemma.
  exact Gibbs.Consensus.quorum_threshold (N := N) (f := f) hN hQ hQ'

/-! ## Gap Collapse at `N = 3f` -/

/-- Explicit quorums witnessing the collapse of the gap at `N = 3f`. -/
theorem quorum_gap_collapse {f : ℕ} :
    ∃ Q Q' : Finset (Fin (3 * f)),
      Q.card = 2 * f ∧ Q'.card = 2 * f ∧ (Q ∩ Q').card = f := by
  classical
  -- Define three disjoint blocks of size `f` by explicit embeddings into `Fin (3f)`.
  have hle_f_3f : f ≤ 3 * f :=
    Nat.le_mul_of_pos_left f (by decide : 0 < (3:Nat))
  have hle_2f_3f : 2 * f ≤ 3 * f :=
    Nat.mul_le_mul_right f (by decide : (2:Nat) ≤ 3)
  let embedA : Fin f → Fin (3 * f) :=
    fun i => ⟨i.1, lt_of_lt_of_le i.is_lt hle_f_3f⟩
  let embedB : Fin f → Fin (3 * f) :=
    fun i =>
      ⟨f + i.1,
        by
          have hlt : f + i.1 < f + f :=
            Nat.add_lt_add_left i.is_lt f
          have hle : f + f ≤ 3 * f := by
            have hle' : 2 * f ≤ 3 * f := hle_2f_3f
            rw [two_mul] at hle'
            exact hle'
          exact lt_of_lt_of_le hlt hle⟩
  let embedC : Fin f → Fin (3 * f) :=
    fun i =>
      ⟨2 * f + i.1,
        by
          -- `i < f` implies `2f + i < 2f + f = 3f`.
          have hlt : 2 * f + i.1 < 2 * f + f :=
            Nat.add_lt_add_left i.is_lt (2 * f)
          have hle : 2 * f + f ≤ 3 * f := by
            have hsum : 3 * f = 2 * f + f := by ring
            simp [hsum]
          exact lt_of_lt_of_le hlt hle⟩
  let A : Finset (Fin (3 * f)) :=
    (Finset.univ : Finset (Fin f)).image embedA
  let B : Finset (Fin (3 * f)) :=
    (Finset.univ : Finset (Fin f)).image embedB
  let C : Finset (Fin (3 * f)) :=
    (Finset.univ : Finset (Fin f)).image embedC
  let Q : Finset (Fin (3 * f)) := A ∪ B
  let Q' : Finset (Fin (3 * f)) := B ∪ C

  -- Cardinalities of the blocks.
  have hcardA : A.card = f := by
    have hAinj : Function.Injective embedA := by
      intro i j h
      apply Fin.ext
      simpa [embedA] using congrArg Fin.val h
    simpa [A] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin f))) hAinj)
  have hcardB : B.card = f := by
    have hBinj : Function.Injective embedB := by
      intro i j h
      apply Fin.ext
      have hval : f + (i : ℕ) = f + (j : ℕ) := by
        simpa [embedB] using congrArg Fin.val h
      exact Nat.add_left_cancel hval
    simpa [B] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin f))) hBinj)
  have hcardC : C.card = f := by
    have hCinj : Function.Injective embedC := by
      intro i j h
      apply Fin.ext
      have hval : 2 * f + (i : ℕ) = 2 * f + (j : ℕ) := by
        simpa [embedC] using congrArg Fin.val h
      exact Nat.add_left_cancel hval
    simpa [C] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin f))) hCinj)

  -- Pairwise disjointness of the blocks.
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.2 ?_
    intro x hxA hxB
    rcases Finset.mem_image.mp hxA with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hxB with ⟨j, _, hEq⟩
    have hlt : (i : ℕ) < f := i.is_lt
    have hge : f ≤ f + (j : ℕ) := Nat.le_add_right _ _
    have hneq : (i : ℕ) ≠ f + (j : ℕ) := ne_of_lt (lt_of_lt_of_le hlt hge)
    exact hneq (by simpa [embedA, embedB] using (congrArg Fin.val hEq).symm)
  have hAC : Disjoint A C := by
    refine Finset.disjoint_left.2 ?_
    intro x hxA hxC
    rcases Finset.mem_image.mp hxA with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hxC with ⟨j, _, hEq⟩
    have hlt : (i : ℕ) < f := i.is_lt
    have hle : f ≤ 2 * f :=
      Nat.le_mul_of_pos_left f (by decide : 0 < (2:Nat))
    have hge : 2 * f ≤ 2 * f + (j : ℕ) := Nat.le_add_right _ _
    have hlt' : (i : ℕ) < 2 * f + (j : ℕ) := by
      exact lt_of_lt_of_le hlt (Nat.le_trans hle hge)
    have hneq : (i : ℕ) ≠ 2 * f + (j : ℕ) := ne_of_lt hlt'
    exact hneq (by simpa [embedA, embedC] using (congrArg Fin.val hEq).symm)
  have hBC : Disjoint B C := by
    refine Finset.disjoint_left.2 ?_
    intro x hxB hxC
    rcases Finset.mem_image.mp hxB with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hxC with ⟨j, _, hEq⟩
    have hlt : (i : ℕ) < f := i.is_lt
    have hlt' : f + (i : ℕ) < 2 * f := by
      -- `i < f` implies `f + i < f + f`.
      rw [two_mul]
      exact Nat.add_lt_add_left hlt f
    have hge : 2 * f ≤ 2 * f + (j : ℕ) := Nat.le_add_right _ _
    have hneq : f + (i : ℕ) ≠ 2 * f + (j : ℕ) := ne_of_lt (lt_of_lt_of_le hlt' hge)
    exact hneq (by simpa [embedB, embedC] using (congrArg Fin.val hEq).symm)

  -- Intersection is exactly the middle block.
  have h_inter : Q ∩ Q' = B := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxQ, hxQ'⟩
      rcases Finset.mem_union.mp hxQ with hxA | hxB
      · rcases Finset.mem_union.mp hxQ' with hxB | hxC
        · exact (Finset.disjoint_left.mp hAB hxA hxB).elim
        · exact (Finset.disjoint_left.mp hAC hxA hxC).elim
      · exact hxB
    · intro hxB
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr hxB),
        Finset.mem_union.mpr (Or.inl hxB)⟩

  -- Assemble the result.
  refine ⟨Q, Q', ?_, ?_, ?_⟩
  · -- card Q
    have hcardQ : Q.card = A.card + B.card := by
      simpa [Q] using (Finset.card_union_of_disjoint hAB)
    simpa [hcardA, hcardB, two_mul] using hcardQ
  · -- card Q'
    have hcardQ' : Q'.card = B.card + C.card := by
      simpa [Q'] using (Finset.card_union_of_disjoint hBC)
    simpa [hcardB, hcardC, two_mul] using hcardQ'
  · -- card intersection
    simp [h_inter, hcardB]

end Gibbs.Consensus.Examples
