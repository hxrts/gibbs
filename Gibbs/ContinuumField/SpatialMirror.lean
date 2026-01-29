import Gibbs.Core

/-
The Problem. We need a lightweight mirror of the Effects spatial model so the
continuum-field layer can compile without pulling the full Effects dependency.
This module mirrors the key types and predicates we rely on: SpatialReq,
Topology, and Satisfies.

The difficulty is staying aligned with Effects while keeping scope minimal.
We therefore copy only the definitions needed by EffectsBridge.

Solution Structure.
1. SpatialReq language (colocation + reliability + capability stubs)
2. Topology with role-to-site assignment
3. Satisfies judgment
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

end Gibbs.ContinuumField
