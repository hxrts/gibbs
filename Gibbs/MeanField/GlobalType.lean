import Gibbs.MeanField.Choreography
import Gibbs.MeanField.Rules
import SessionTypes.GlobalType.Core

/-!
# Mean-Field Choreography → Global Session Type

Encodes a `MeanFieldChoreography` as a Telltale `GlobalType`. Since mean-field
models have no intrinsic roles, a `MeanFieldRoleAssignment` must be provided to
partition species among roles. Coupling between roles is passed as an explicit
predicate (drift function dependencies are opaque).

One time step is: all concentration exchanges between coupled roles, wrapped in
`mu "step"` for iteration.
-/

namespace Gibbs.MeanField

open SessionTypes.GlobalType (GlobalType PayloadSort allVarsBoundBranches
  allCommsNonEmptyBranches noSelfCommBranches isProductiveBranches)

/-- Telltale label (disambiguated from Gibbs.Label). -/
abbrev TLabel := SessionTypes.GlobalType.Label

/-! ## Role Assignment -/

/-- Assignment of species to roles for mean-field encoding. -/
structure MeanFieldRoleAssignment (Q : Type*) [Fintype Q] where
  /-- Role names. -/
  roles : List Gibbs.Role
  /-- Species tracked by each role. -/
  assignment : Gibbs.Role → Finset Q
  /-- Every species is covered by some role. -/
  covers : ∀ q, ∃ r ∈ roles, q ∈ assignment r

/-! ## Helper: chain communications -/

/-- Chain a list of `(sender, receiver, label)` triples into nested `comm` nodes,
    ending with the given continuation. -/
private def chainComms (comms : List (String × String × String)) (cont : GlobalType) : GlobalType :=
  comms.foldr (fun (s, r, l) acc =>
    .comm s r [({ name := l, sort := .nat : TLabel }, acc)]) cont

/-! ## Encoding -/

/-- Build directed coupling pairs from role list and coupling predicate. -/
def coupledPairs (roleNames : List Gibbs.Role) (coupled : Gibbs.Role → Gibbs.Role → Bool) :
    List (Gibbs.Role × Gibbs.Role) :=
  roleNames.flatMap fun a =>
    (roleNames.filter fun b => a != b && coupled a b).map fun b => (a, b)

/-- All pairs in `coupledPairs` have distinct components. -/
theorem coupledPairs_noSelfComm (roleNames : List Gibbs.Role)
    (coupled : Gibbs.Role → Gibbs.Role → Bool) :
    ∀ p ∈ coupledPairs roleNames coupled, p.1 ≠ p.2 := by
  intro ⟨a, b⟩ hmem
  simp only [coupledPairs, List.mem_flatMap, List.mem_map, List.mem_filter] at hmem
  obtain ⟨a', _, b', ⟨_, hfilt⟩, heq⟩ := hmem
  simp only [Bool.and_eq_true, bne_iff_ne] at hfilt
  have hpair := heq.symm
  have := Prod.mk.inj hpair
  rw [this.1, this.2]
  exact hfilt.1

/-- Encode a mean-field choreography as a `GlobalType`.

    The coupling predicate `coupled A B` should be `true` when role B's drift
    depends on species tracked by role A.

    The encoding produces one time step: for each coupled pair (A, B),
    A sends its concentration vector to B, then recurse. -/
def MeanFieldChoreography.toGlobalType {Q : Type*} [Fintype Q]
    (_C : MeanFieldChoreography Q)
    (ra : MeanFieldRoleAssignment Q)
    (coupled : Gibbs.Role → Gibbs.Role → Bool) : GlobalType :=
  let pairs := coupledPairs ra.roles coupled
  let comms := pairs.map fun (a, b) => (a, b, "concentration")
  let body := comms.foldr (fun (s, r, l) acc =>
    .comm s r [({ name := l, sort := .nat : TLabel }, acc)]) (.var "step")
  .mu "step" body

/-! ## Well-formedness helpers -/

private theorem chainComms_allVarsBound (comms : List (String × String × String))
    (cont : GlobalType) (bound : List String)
    (hcont : cont.allVarsBound bound = true) :
    (chainComms comms cont).allVarsBound bound = true := by
  induction comms with
  | nil => exact hcont
  | cons hd tl ih =>
    obtain ⟨s, r, l⟩ := hd
    simp only [chainComms, List.foldr_cons]
    simp only [GlobalType.allVarsBound, allVarsBoundBranches, Bool.and_true]
    exact ih

private theorem chainComms_allCommsNonEmpty (comms : List (String × String × String))
    (cont : GlobalType) (hcont : cont.allCommsNonEmpty = true) :
    (chainComms comms cont).allCommsNonEmpty = true := by
  induction comms with
  | nil => exact hcont
  | cons hd tl ih =>
    obtain ⟨s, r, l⟩ := hd
    simp only [chainComms, List.foldr_cons]
    simp only [GlobalType.allCommsNonEmpty, List.isEmpty, allCommsNonEmptyBranches,
      Bool.and_true]
    exact ih

private theorem chainComms_noSelfComm (comms : List (String × String × String))
    (cont : GlobalType) (hcont : cont.noSelfComm = true)
    (h_distinct : ∀ c ∈ comms, c.1 ≠ c.2.1) :
    (chainComms comms cont).noSelfComm = true := by
  induction comms with
  | nil => exact hcont
  | cons hd tl ih =>
    obtain ⟨s, r, l⟩ := hd
    simp only [chainComms, List.foldr_cons]
    have h_ne : s ≠ r := h_distinct (s, r, l) (List.mem_cons.mpr (Or.inl rfl))
    have h_rest : ∀ c ∈ tl, c.1 ≠ c.2.1 :=
      fun c hc => h_distinct c (List.mem_cons.mpr (Or.inr hc))
    simp only [GlobalType.noSelfComm, bne_iff_ne, ne_eq, noSelfCommBranches,
      Bool.and_true, Bool.and_eq_true]
    exact ⟨h_ne, ih h_rest⟩

private theorem chainComms_isProductive_empty (comms : List (String × String × String))
    (cont : GlobalType) (hcont : cont.isProductive [] = true) :
    (chainComms comms cont).isProductive [] = true := by
  induction comms with
  | nil => exact hcont
  | cons hd tl ih =>
    obtain ⟨s, r, l⟩ := hd
    simp only [chainComms, List.foldr_cons]
    simp only [GlobalType.isProductive, isProductiveBranches, Bool.and_true]
    exact ih

/-! ## Well-formedness -/

theorem MeanFieldChoreography.toGlobalType_wellFormed
    {Q : Type*} [Fintype Q] (C : MeanFieldChoreography Q)
    (ra : MeanFieldRoleAssignment Q)
    (coupled : Gibbs.Role → Gibbs.Role → Bool)
    (h_pairs : (coupledPairs ra.roles coupled).length > 0)
    (_h_nodup : ra.roles.Nodup) :
    let g := C.toGlobalType ra coupled
    g.allVarsBound = true
    ∧ g.allCommsNonEmpty = true
    ∧ g.noSelfComm = true
    ∧ g.isProductive = true := by
  simp only [MeanFieldChoreography.toGlobalType]
  set pairs := coupledPairs ra.roles coupled
  set comms := pairs.map fun (a, b) => (a, b, "concentration")
  have h_comms_pos : comms.length > 0 := by
    simp only [comms, List.length_map]
    exact h_pairs
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- allVarsBound
    simp only [GlobalType.allVarsBound]
    exact chainComms_allVarsBound comms (.var "step") ["step"]
      (by simp [GlobalType.allVarsBound])
  · -- allCommsNonEmpty
    simp only [GlobalType.allCommsNonEmpty]
    exact chainComms_allCommsNonEmpty comms (.var "step")
      (by simp [GlobalType.allCommsNonEmpty])
  · -- noSelfComm
    simp only [GlobalType.noSelfComm]
    apply chainComms_noSelfComm comms (.var "step") (by simp [GlobalType.noSelfComm])
    intro c hmem
    simp only [comms, List.mem_map] at hmem
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := hmem
    exact coupledPairs_noSelfComm ra.roles coupled ⟨a, b⟩ hp
  · -- isProductive: mu adds "step" to unguarded, first comm resets to []
    simp only [GlobalType.isProductive]
    obtain ⟨hd, tl, h_eq⟩ := List.exists_cons_of_length_pos h_comms_pos
    rw [h_eq]
    obtain ⟨s, r, l⟩ := hd
    simp only [List.foldr_cons, GlobalType.isProductive,
      isProductiveBranches, Bool.and_true]
    exact chainComms_isProductive_empty tl (.var "step")
      (by simp [GlobalType.isProductive])

end Gibbs.MeanField
