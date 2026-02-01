import Gibbs.Session

/-!
# Spatial model mirror

Lightweight replica of the Telltale/Effects spatial model so the continuum-
field layer can compile without importing Effects directly. Mirrors three
components: `SpatialReq` (a small language of spatial constraints like
colocation, reliable edges, and site capabilities), `Topology` (a deployment
descriptor mapping roles to sites), and `Satisfies` (a propositional
judgment that a topology meets a requirement, with a decidable boolean
counterpart). Kept in sync with `Effects.Spatial` by convention.
-/

namespace Gibbs.ContinuumField

open scoped Classical

/-! ## Spatial Requirements (Mirror) -/

/-- A site represents a deployment location. -/
abbrev Site := String

/-- A role name in the protocol (uses Gibbs.Role). -/
abbrev RoleName := Role

/-- Spatial requirements (mirrors Effects.SpatialReq). -/
inductive SpatialReq where
  | netCapable : Site → SpatialReq
  | timeoutCapable : Site → SpatialReq
  | colocated : RoleName → RoleName → SpatialReq
  | reliableEdge : RoleName → RoleName → SpatialReq
  | conj : SpatialReq → SpatialReq → SpatialReq
  | top : SpatialReq
  | bot : SpatialReq
  deriving Inhabited, Repr, DecidableEq, BEq

namespace SpatialReq

/-- Conjunction notation for spatial requirements. -/
instance : HAnd SpatialReq SpatialReq SpatialReq where
  hAnd := conj

/-- Check if a requirement is trivially satisfied. -/
def isTop : SpatialReq → Bool
  | top => true
  | _ => false

/-- Check if a requirement is trivially unsatisfiable. -/
def isBot : SpatialReq → Bool
  | bot => true
  | _ => false

/-- Flatten nested conjunctions into a list of atomic requirements. -/
partial def atoms : SpatialReq → List SpatialReq
  | conj r₁ r₂ => atoms r₁ ++ atoms r₂
  | top => []
  | r => [r]

/-- Build a conjunction from a list of requirements. -/
def fromList : List SpatialReq → SpatialReq
  | [] => top
  | [r] => r
  | r :: rs => conj r (fromList rs)

end SpatialReq

/-! ## Topology (Mirror) -/

/-- Site capability flags. -/
structure SiteCapabilities where
  /-- Site has network connectivity. -/
  hasNetwork : Bool := true
  /-- Site can fire timeouts. -/
  hasTimeout : Bool := true
  deriving Inhabited, Repr, DecidableEq, BEq

/-- Deployment topology: role-to-site assignment and reliable edges. -/
structure Topology where
  /-- Declared sites. -/
  sites : List Site
  /-- Role-to-site assignment. -/
  assign : RoleName → Site
  /-- Reliable edges between sites. -/
  edges : List (Site × Site)
  /-- Per-site capability flags. -/
  capabilities : Site → SiteCapabilities := fun _ => default
  deriving Inhabited

namespace Topology

/-- Default topology with identity assignment. -/
def trivial : Topology where
  sites := []
  assign := id
  edges := []

/-- Check if two sites have a reliable edge. -/
def hasEdge (topo : Topology) (s₁ s₂ : Site) : Bool :=
  -- Allow symmetry in edge declarations.
  (s₁, s₂) ∈ topo.edges || (s₂, s₁) ∈ topo.edges

/-- Check if a site has network capability. -/
def siteHasNetwork (topo : Topology) (s : Site) : Bool :=
  (topo.capabilities s).hasNetwork

/-- Check if a site has timeout capability. -/
def siteHasTimeout (topo : Topology) (s : Site) : Bool :=
  (topo.capabilities s).hasTimeout

/-- Get the site for a role. -/
def siteOf (topo : Topology) (role : RoleName) : Site :=
  topo.assign role

/-- Check if two roles are colocated. -/
def rolesColocated (topo : Topology) (r₁ r₂ : RoleName) : Bool :=
  topo.siteOf r₁ == topo.siteOf r₂

end Topology

/-! ## Satisfaction (Mirror) -/

/-- Satisfaction judgment: topology satisfies a spatial requirement. -/
def Satisfies (topo : Topology) : SpatialReq → Prop
  | .netCapable s => topo.siteHasNetwork s = true
  | .timeoutCapable s => topo.siteHasTimeout s = true
  | .colocated r₁ r₂ => topo.siteOf r₁ = topo.siteOf r₂
  | .reliableEdge r₁ r₂ => topo.hasEdge (topo.siteOf r₁) (topo.siteOf r₂) = true
  | .conj r₁ r₂ => Satisfies topo r₁ ∧ Satisfies topo r₂
  | .top => True
  | .bot => False

/-! ## Boolean Satisfaction (Mirror) -/

/-- Boolean satisfaction predicate mirroring Effects. -/
def satisfiesBool (topo : Topology) : SpatialReq → Bool
  | .netCapable s => topo.siteHasNetwork s
  | .timeoutCapable s => topo.siteHasTimeout s
  | .colocated r₁ r₂ => topo.rolesColocated r₁ r₂
  | .reliableEdge r₁ r₂ => topo.hasEdge (topo.siteOf r₁) (topo.siteOf r₂)
  | .conj r₁ r₂ => satisfiesBool topo r₁ && satisfiesBool topo r₂
  | .top => true
  | .bot => false

/-- Boolean satisfaction is equivalent to propositional satisfaction. -/
theorem satisfiesBool_iff_Satisfies (topo : Topology) (req : SpatialReq) :
    satisfiesBool topo req = true ↔ Satisfies topo req := by
  induction req with
  | netCapable s => simp [satisfiesBool, Satisfies]
  | timeoutCapable s => simp [satisfiesBool, Satisfies]
  | colocated r₁ r₂ =>
      simp only [satisfiesBool, Satisfies, Topology.rolesColocated]
      constructor
      · intro h; exact beq_iff_eq.mp h
      · intro h; exact beq_iff_eq.mpr h
  | reliableEdge r₁ r₂ => simp [satisfiesBool, Satisfies]
  | conj r₁ r₂ ih₁ ih₂ =>
      simp only [satisfiesBool, Satisfies, Bool.and_eq_true]
      constructor
      · intro ⟨h₁, h₂⟩; exact ⟨ih₁.mp h₁, ih₂.mp h₂⟩
      · intro ⟨h₁, h₂⟩; exact ⟨ih₁.mpr h₁, ih₂.mpr h₂⟩
  | top => simp [satisfiesBool, Satisfies]
  | bot => simp [satisfiesBool, Satisfies]

end Gibbs.ContinuumField
