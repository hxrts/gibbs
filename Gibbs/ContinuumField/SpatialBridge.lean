import Gibbs.ContinuumField.TimeBridge
import Gibbs.ContinuumField.SpatialMirror

/-!
# Spatial bridge to Telltale

Aligns the continuum-field role-location map with Telltale's spatial type
system. The `AlignedRoleLoc` predicate requires that roles assigned to the
same site by the deployment topology receive the same continuous-space
location. Given this alignment, `effectsSpatialBridge` constructs a
`SpatialBridge` that translates Telltale's colocation and distance
requirements into the continuum-field predicates `Colocated` and `Within`.

Uses the `SpatialMirror` definitions so the layer compiles without a direct
Telltale dependency.
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
