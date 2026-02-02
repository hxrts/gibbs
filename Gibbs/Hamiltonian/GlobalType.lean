import Gibbs.Hamiltonian.Choreography
import SessionTypes.GlobalType.Core
import Choreography.Projection.Trans.Core

/-!
# Hamiltonian Choreography → Global Session Type

Encodes a `HamiltonianChoreography` as a Telltale `GlobalType`. The encoding
extracts the communication topology from coordinate coupling: role A sends its
position to role B whenever B's force computation depends on A's coordinates.

One time step is: all position exchanges, then all force exchanges, wrapped in
`mu "step"` for iteration.
-/

namespace Gibbs.Hamiltonian

open SessionTypes.GlobalType (GlobalType PayloadSort allVarsBoundBranches
  allCommsNonEmptyBranches noSelfCommBranches isProductiveBranches)
open Choreography.Projection.Trans (trans)

/-- Telltale label (disambiguated from Gibbs.Label). -/
abbrev TLabel := SessionTypes.GlobalType.Label

/-! ## Helper: chain a list of communications into a GlobalType -/

/-- Chain a list of `(sender, receiver, label)` triples into nested `comm` nodes,
    ending with the given continuation. -/
def chainComms (comms : List (String × String × String)) (cont : GlobalType) : GlobalType :=
  comms.foldr (fun (s, r, l) acc =>
    .comm s r [({ name := l, sort := .nat : TLabel }, acc)]) cont

/-! ## Encoding -/

/-- Build the list of directed edges from the coupling predicate. -/
def coupledPairs (roleNames : List Role) (coupled : Role → Role → Bool) :
    List (Role × Role) :=
  roleNames.flatMap fun a =>
    (roleNames.filter fun b => a != b && coupled a b).map fun b => (a, b)

/-- All pairs in `coupledPairs` have distinct components. -/
theorem coupledPairs_noSelfComm (roleNames : List Role) (coupled : Role → Role → Bool) :
    ∀ p ∈ coupledPairs roleNames coupled, p.1 ≠ p.2 := by
  intro ⟨a, b⟩ hmem
  simp only [coupledPairs, List.mem_flatMap, List.mem_map, List.mem_filter] at hmem
  obtain ⟨a', _, b', ⟨_, hfilt⟩, heq⟩ := hmem
  simp only [Bool.and_eq_true, bne_iff_ne] at hfilt
  have hpair := heq.symm
  have := Prod.mk.inj hpair
  rw [this.1, this.2]
  exact hfilt.1

/-- Encode a Hamiltonian choreography as a `GlobalType`.

    The coupling predicate `coupled A B` should be `true` when role B's dynamics
    depend on role A's coordinates (i.e., A must send data to B).

    The encoding produces one time step:
    1. Position exchange: for each coupled pair (A, B), A sends position to B
    2. Force exchange: for each coupled pair (A, B), A sends force to B
    3. Recurse via `var "step"` -/
def HamiltonianChoreography.toGlobalType (_C : HamiltonianChoreography n)
    (roleNames : List Role)
    (coupled : Role → Role → Bool) : GlobalType :=
  let pairs := coupledPairs roleNames coupled
  let posComms := pairs.map fun (a, b) => (a, b, "position")
  let forceComms := pairs.map fun (a, b) => (a, b, "force")
  .mu "step" (chainComms (posComms ++ forceComms) (.var "step"))

/-! ## Well-formedness helpers for chainComms -/

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

/-- The encoded global type is well-formed when there is at least one coupled pair
    and all role names are distinct. -/
theorem HamiltonianChoreography.toGlobalType_wellFormed
    {n : ℕ} (C : HamiltonianChoreography n)
    (roleNames : List Role) (coupled : Role → Role → Bool)
    (h_pairs : (coupledPairs roleNames coupled).length > 0)
    (_h_nodup : roleNames.Nodup) :
    let g := C.toGlobalType roleNames coupled
    g.allVarsBound = true
    ∧ g.allCommsNonEmpty = true
    ∧ g.noSelfComm = true
    ∧ g.isProductive = true := by
  simp only [HamiltonianChoreography.toGlobalType]
  set pairs := coupledPairs roleNames coupled
  set comms := pairs.map (fun (a, b) => (a, b, "position")) ++
    pairs.map (fun (a, b) => (a, b, "force"))
  have h_comms_pos : comms.length > 0 := by
    simp only [comms, List.length_append, List.length_map]
    omega
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
    simp only [comms, List.mem_append, List.mem_map] at hmem
    rcases hmem with ⟨⟨a, b⟩, hp, rfl⟩ | ⟨⟨a, b⟩, hp, rfl⟩ <;>
      exact coupledPairs_noSelfComm roleNames coupled ⟨a, b⟩ hp
  · -- isProductive: mu adds "step" to unguarded, first comm resets to []
    simp only [GlobalType.isProductive]
    obtain ⟨hd, tl, h_eq⟩ := List.exists_cons_of_length_pos h_comms_pos
    rw [h_eq]
    obtain ⟨s, r, l⟩ := hd
    simp only [chainComms, List.foldr_cons, GlobalType.isProductive,
      isProductiveBranches, Bool.and_true]
    exact chainComms_isProductive_empty tl (.var "step")
      (by simp [GlobalType.isProductive])

/-! ## Projection example -/

section ProjectionTest

private def exampleGT : GlobalType :=
  chainComms [("A", "B", "position"), ("B", "A", "position"),
              ("A", "B", "force"), ("B", "A", "force")] (.var "step")
  |> GlobalType.mu "step"

#eval! toString (repr exampleGT)
#eval! toString (repr (trans exampleGT "A"))
#eval! toString (repr (trans exampleGT "B"))

end ProjectionTest

end Gibbs.Hamiltonian
