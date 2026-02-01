import Gibbs.Session
import Gibbs.ContinuumField.Basic
import Mathlib

/-!
# Space and time bridge

Connects the discrete role-based world of choreographies to the continuous
space-time of field theory. Each protocol role is assigned a location in a
continuous space `X` via a `RoleLoc` map. Colocation and distance predicates
express spatial constraints between roles.

On the time side, a `SamplingSchedule` maps discrete step indices to real
times, and a `RemoteClockSampler` abstracts over possible clock dependence.
The key property is `ClockIndependent`: samplers built from a local schedule
ignore remote clock inputs, ensuring that field observations depend only on
the local sampling times.
-/

namespace Gibbs.ContinuumField

open scoped Classical

/-! ## Space Bridge -/

/-- A role-location map into a continuous space X. -/
abbrev RoleLoc (X : Type*) := Role → X  -- roles have spatial positions

/-- A space model packages the role-location map. -/
structure SpaceModel (X : Type*) where
  /-- Role-to-location assignment. -/
  roleLoc : RoleLoc X

/-- Colocation: two roles share the same location. -/
def Colocated {X : Type*} (loc : RoleLoc X) (r1 r2 : Role) : Prop :=
  -- same location means colocated
  loc r1 = loc r2

/-- Distance-bounded: two roles are within distance d. -/
def Within {X : Type*} [PseudoMetricSpace X]
    (loc : RoleLoc X) (r1 r2 : Role) (d : ℝ) : Prop :=
  -- bound the distance between role locations
  dist (loc r1) (loc r2) ≤ d

/-! ## Spatial Alignment -/

/-- A lightweight bridge to Effects-style spatial requirements. -/
structure SpatialBridge (X : Type*) (Topology : Type*) (SpatialReq : Type*)
    [PseudoMetricSpace X] where
  /-- Role-to-location assignment. -/
  roleLoc : RoleLoc X
  /-- Satisfaction relation (from Effects). -/
  satisfies : Topology → SpatialReq → Prop
  /-- Requirement: colocation. -/
  reqColocated : Role → Role → SpatialReq
  /-- Requirement: distance bound. -/
  reqWithin : Role → Role → ℝ → SpatialReq
  /-- Soundness of colocation requirement. -/
  colocated_sound :
    ∀ topo r1 r2, satisfies topo (reqColocated r1 r2) → Colocated roleLoc r1 r2
  /-- Soundness of distance requirement. -/
  within_sound :
    ∀ topo r1 r2 d, satisfies topo (reqWithin r1 r2 d) → Within roleLoc r1 r2 d

namespace SpatialBridge

variable {X Topology SpatialReq : Type*} [PseudoMetricSpace X]

/-- If the topology satisfies colocation, the locations coincide. -/
theorem satisfies_colocated (B : SpatialBridge X Topology SpatialReq)
    (topo : Topology) (r1 r2 : Role) :
    B.satisfies topo (B.reqColocated r1 r2) → Colocated B.roleLoc r1 r2 := by
  -- unpack the soundness field
  intro hsat
  exact B.colocated_sound topo r1 r2 hsat

/-- If the topology satisfies a distance bound, roles are within d. -/
theorem satisfies_within (B : SpatialBridge X Topology SpatialReq)
    (topo : Topology) (r1 r2 : Role) (d : ℝ) :
    B.satisfies topo (B.reqWithin r1 r2 d) → Within B.roleLoc r1 r2 d := by
  -- unpack the soundness field
  intro hsat
  exact B.within_sound topo r1 r2 d hsat

end SpatialBridge

/-! ## Time Bridge -/

/-- A sampling schedule maps step indices to real time. -/
structure SamplingSchedule where
  /-- Step index ↦ sample time. -/
  sampleTime : ℕ → ℝ

/-- A sampler that might depend on a remote clock value. -/
structure RemoteClockSampler (A : Type*) where
  /-- Given step and remote time, return a sample. -/
  sample : ℕ → ℝ → A

/-- Clock-independence: the sample ignores remote clock inputs. -/
def ClockIndependent {A : Type*} (s : RemoteClockSampler A) : Prop :=
  -- remote time does not affect the sample
  ∀ k t₁ t₂, s.sample k t₁ = s.sample k t₂

/-- Build a sampler from a schedule and a time-indexed field. -/
def mkSampler {A : Type*} (sched : SamplingSchedule) (f : ℝ → A) : RemoteClockSampler A :=
  -- ignore remote time, sample only at sched.sampleTime k
  { sample := fun k _t => f (sched.sampleTime k) }

/-- Sample a time-indexed field at a discrete step. -/
def sampleAtStep {A : Type*} (sched : SamplingSchedule) (f : ℝ → A) (k : ℕ) : A :=
  -- sampling depends only on the schedule and step index
  f (sched.sampleTime k)

/-- The sampled time series as a function of step index. -/
def sampleSeries {A : Type*} (sched : SamplingSchedule) (f : ℝ → A) : ℕ → A :=
  -- package sampleAtStep as a sequence
  fun k => sampleAtStep sched f k

/-- Sampling from a schedule is clock-independent. -/
theorem mkSampler_clockIndependent {A : Type*}
    (sched : SamplingSchedule) (f : ℝ → A) : ClockIndependent (mkSampler sched f) := by
  -- the sampler ignores its remote time argument
  intro k t₁ t₂
  rfl

/-- The sampler agrees with sampleAtStep, for any remote time. -/
theorem mkSampler_sampleAtStep {A : Type*}
    (sched : SamplingSchedule) (f : ℝ → A) (k : ℕ) (t : ℝ) :
    (mkSampler sched f).sample k t = sampleAtStep sched f k := by
  -- remote time is ignored by mkSampler
  rfl

end Gibbs.ContinuumField
