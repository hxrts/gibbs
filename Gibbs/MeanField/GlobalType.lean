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

open SessionTypes.GlobalType (GlobalType PayloadSort)

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

/-! ## Encoding -/

/-- Build directed coupling pairs from role list and coupling predicate. -/
def coupledPairs (roleNames : List Gibbs.Role) (coupled : Gibbs.Role → Gibbs.Role → Bool) :
    List (Gibbs.Role × Gibbs.Role) :=
  roleNames.flatMap fun a =>
    (roleNames.filter fun b => a != b && coupled a b).map fun b => (a, b)

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

/-! ## Well-formedness -/

theorem MeanFieldChoreography.toGlobalType_wellFormed
    {Q : Type*} [Fintype Q] (C : MeanFieldChoreography Q)
    (ra : MeanFieldRoleAssignment Q)
    (coupled : Gibbs.Role → Gibbs.Role → Bool)
    (h_pairs : (coupledPairs ra.roles coupled).length > 0)
    (h_nodup : ra.roles.Nodup) :
    let g := C.toGlobalType ra coupled
    g.allVarsBound = true
    ∧ g.allCommsNonEmpty = true
    ∧ g.noSelfComm = true
    ∧ g.isProductive = true := by
  sorry

end Gibbs.MeanField
