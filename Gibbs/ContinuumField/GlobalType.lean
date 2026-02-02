import Gibbs.ContinuumField.EffectsIntegration
import SessionTypes.GlobalType.Core

/-!
# Continuum Field → Global Session Type

Encodes a spatial field interaction as a Telltale `GlobalType`. Each role
occupies a spatial location; nonlocal kernel coupling between locations becomes
communication. The coupling predicate abstracts kernel support (continuous
kernels may have full support, requiring a threshold or discretization).

One time step is: all field exchanges between coupled roles, wrapped in
`mu "step"` for iteration.
-/

namespace Gibbs.ContinuumField

open SessionTypes.GlobalType (GlobalType PayloadSort)

/-- Telltale label (disambiguated from Gibbs.Label). -/
abbrev TLabel := SessionTypes.GlobalType.Label

/-! ## Encoding -/

/-- Build directed coupling pairs from role list and coupling predicate. -/
def coupledPairs (roleNames : List Gibbs.Role) (coupled : Gibbs.Role → Gibbs.Role → Bool) :
    List (Gibbs.Role × Gibbs.Role) :=
  roleNames.flatMap fun a =>
    (roleNames.filter fun b => a != b && coupled a b).map fun b => (a, b)

/-- Encode spatial field interactions as a `GlobalType`.

    The coupling predicate `coupled A B` should be `true` when role B needs
    field values from role A's location (i.e., the kernel `K(loc A, loc B)` is
    nonzero or above threshold).

    The encoding produces one time step: for each coupled pair (A, B),
    A sends its field value to B, then recurse. -/
def kernelToGlobalType (roleNames : List Gibbs.Role)
    (coupled : Gibbs.Role → Gibbs.Role → Bool) : GlobalType :=
  let pairs := coupledPairs roleNames coupled
  let comms := pairs.map fun (a, b) => (a, b, "field")
  let body := comms.foldr (fun (s, r, l) acc =>
    .comm s r [({ name := l, sort := .nat : TLabel }, acc)]) (.var "step")
  .mu "step" body

/-! ## Well-formedness -/

theorem kernelToGlobalType_wellFormed
    (roleNames : List Gibbs.Role)
    (coupled : Gibbs.Role → Gibbs.Role → Bool)
    (h_pairs : (coupledPairs roleNames coupled).length > 0)
    (h_nodup : roleNames.Nodup) :
    let g := kernelToGlobalType roleNames coupled
    g.allVarsBound = true
    ∧ g.allCommsNonEmpty = true
    ∧ g.noSelfComm = true
    ∧ g.isProductive = true := by
  sorry

end Gibbs.ContinuumField
