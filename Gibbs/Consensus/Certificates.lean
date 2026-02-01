import Mathlib.Data.Finset.Card
import Gibbs.Consensus.Basic
import Gibbs.Consensus.Quorum

/-!
# Certificates and quorum consistency

A *certificate* is a quorum all of whose members vote for the same value.
When two quorums intersect, any process in the intersection has cast a vote
that appears in both certificates. If each process votes only once, the two
certificates must agree on the value.

This is the mechanism that creates the energy barrier in BFT consensus.
Producing two conflicting certificates requires corrupting every process in
the intersection, which exceeds the adversary's budget when quorums are large
enough. The quorum-size intersection bound from `Quorum.lean` gives the
quantitative threshold.
-/

namespace Gibbs.Consensus

/-! ## Certificates -/

/-- A quorum certifies a value if all its members vote for that value. -/
def IsCertificate {N : ℕ} {V : Type} (vote : Process N → V)
    (Q : Finset (Process N)) (v : V) : Prop :=
  ∀ i ∈ Q, vote i = v

/-- Intersecting certificates must certify the same value. -/
theorem certificates_agree_of_intersection {N : ℕ} {V : Type}
    {vote : Process N → V} {Q Q' : Finset (Process N)} {v v' : V}
    (hQ : IsCertificate vote Q v) (hQ' : IsCertificate vote Q' v')
    (hinter : (Q ∩ Q').Nonempty) :
    v = v' := by
  rcases hinter with ⟨i, hi⟩
  have hiQ : i ∈ Q := (Finset.mem_inter.mp hi).1
  have hiQ' : i ∈ Q' := (Finset.mem_inter.mp hi).2
  have hv : vote i = v := hQ i hiQ
  have hv' : vote i = v' := hQ' i hiQ'
  exact hv.symm.trans hv'

/-- Quorum-size intersection implies certificate agreement. -/
theorem certificates_agree_of_quorum_intersection {N q : ℕ} {V : Type}
    {vote : Process N → V} {Q Q' : Finset (Process N)} {v v' : V}
    (hQ : Q.card = q) (hQ' : Q'.card = q) (hsize : N < q + q)
    (hcert : IsCertificate vote Q v) (hcert' : IsCertificate vote Q' v') :
    v = v' := by
  have hcard :
      (Finset.univ : Finset (Process N)).card < Q.card + Q'.card := by
    simpa [hQ, hQ'] using hsize
  have hinter : (Q ∩ Q').Nonempty := by
    refine Finset.inter_nonempty_of_card_lt_card_add_card (s := Finset.univ) ?_ ?_ ?_
    · intro x hx; simp
    · intro x hx; simp
    · simpa using hcard
  exact certificates_agree_of_intersection hcert hcert' hinter

end Gibbs.Consensus
