import Gibbs.ContinuumField.TimeBridge
import Effects.Spatial

/-
The Problem. We want to align the continuum-field space bridge with the
Effects spatial type system. Effects provides `SpatialReq`, `Topology`, and
`Satisfies`, but does not encode metric distances. We therefore connect
colocation directly and make distance bounds a user-supplied requirement.

The difficulty is ensuring that role locations in continuous space respect
Effects' site assignment. We express this as an alignment predicate and
use it to build a `SpatialBridge` instance.

Solution Structure.
1. AlignedRoleLoc: role locations respect topo site equality
2. effectsSpatialBridge: build a SpatialBridge with Effects types
-/

namespace Gibbs.ContinuumField

open scoped Classical

/-! ## Alignment Predicate -/

/-- Role locations are consistent with the topology's site equality. -/
def AlignedRoleLoc {X : Type*} [PseudoMetricSpace X]
    (roleLoc : RoleLoc X) (topo : Topology) : Prop :=
  -- equal sites imply equal locations
  ∀ r1 r2, topo.siteOf r1 = topo.siteOf r2 → roleLoc r1 = roleLoc r2

/-! ## Effects Adapter -/

/-- Build a SpatialBridge using Effects' SpatialReq and Topology. -/
def effectsSpatialBridge {X : Type*} [PseudoMetricSpace X]
    (roleLoc : RoleLoc X)
    (withinReq : Role → Role → ℝ → SpatialReq)
    (align : ∀ topo : Topology, AlignedRoleLoc roleLoc topo)
    (within_sound :
      ∀ topo r1 r2 d, Satisfies topo (withinReq r1 r2 d) →
        Within roleLoc r1 r2 d) :
    SpatialBridge X Topology SpatialReq := by
  -- package the required fields and proofs
  refine
    { roleLoc := roleLoc
      satisfies := Satisfies
      reqColocated := SpatialReq.colocated
      reqWithin := withinReq
      colocated_sound := ?_
      within_sound := ?_ }
  · -- colocation uses Effects' site equality + alignment
    intro topo r1 r2 hsat
    have hsite : topo.siteOf r1 = topo.siteOf r2 := by
      -- Satisfies for colocated is definitional
      simpa [Satisfies] using hsat
    exact (align topo) r1 r2 hsite
  · -- distance requirement is delegated to caller
    intro topo r1 r2 d hsat
    exact within_sound topo r1 r2 d hsat

end Gibbs.ContinuumField
