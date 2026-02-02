import Gibbs.Hamiltonian.Channel
import Gibbs.ContinuumField.TimeBridge
import Mathlib.Tactic

/-!
# Spatial Capacity Bridge

Connects spatial distance to information-theoretic channel capacity.
-/

namespace Gibbs.ContinuumField.CapacityBridge

noncomputable section

open scoped BigOperators

/-! ## Distance-Dependent Channels -/

/-- A spatial channel model with distance-dependent noise. -/
structure SpatialChannelModel (X : Type*) [PseudoMetricSpace X] where
  /-- Signal power. -/
  signalPower : ℝ
  /-- Signal power is positive. -/
  signalPower_pos : 0 < signalPower
  /-- Noise power as a function of distance. -/
  noisePower : ℝ → ℝ
  /-- Noise is positive. -/
  noisePower_pos : ∀ d, 0 < noisePower d
  /-- Noise increases with distance. -/
  noisePower_monotone : Monotone noisePower

/-- Capacity at a given distance using the Gaussian formula. -/
def spatialCapacity {X : Type*} [PseudoMetricSpace X]
    (sc : SpatialChannelModel X) (d : ℝ) : ℝ :=
  (1/2) * Real.log (1 + sc.signalPower / sc.noisePower d)

/-- Capacity decreases with distance. -/
theorem spatialCapacity_antitone {X : Type*} [PseudoMetricSpace X]
    (sc : SpatialChannelModel X) : Antitone (spatialCapacity sc) := by
  intro d1 d2 h
  have hnoise : sc.noisePower d1 ≤ sc.noisePower d2 := sc.noisePower_monotone h
  have hrecip : (1 / sc.noisePower d2) ≤ (1 / sc.noisePower d1) :=
    one_div_le_one_div_of_le (sc.noisePower_pos d1) (by simpa using hnoise)
  have hdiv : sc.signalPower / sc.noisePower d2 ≤ sc.signalPower / sc.noisePower d1 := by
    have hPnonneg : 0 ≤ sc.signalPower := le_of_lt sc.signalPower_pos
    simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_left hrecip hPnonneg)
  have harg : 1 + sc.signalPower / sc.noisePower d2 ≤ 1 + sc.signalPower / sc.noisePower d1 := by
    linarith
  have hpos1 : 0 < 1 + sc.signalPower / sc.noisePower d1 := by
    have : 0 ≤ sc.signalPower / sc.noisePower d1 :=
      div_nonneg (le_of_lt sc.signalPower_pos) (le_of_lt (sc.noisePower_pos d1))
    linarith
  have hpos2 : 0 < 1 + sc.signalPower / sc.noisePower d2 := by
    have : 0 ≤ sc.signalPower / sc.noisePower d2 :=
      div_nonneg (le_of_lt sc.signalPower_pos) (le_of_lt (sc.noisePower_pos d2))
    linarith
  have hlog : Real.log (1 + sc.signalPower / sc.noisePower d2) ≤
      Real.log (1 + sc.signalPower / sc.noisePower d1) :=
    Real.log_le_log hpos2 harg
  have hhalf : 0 ≤ (1/2 : ℝ) := by norm_num
  exact mul_le_mul_of_nonneg_left hlog hhalf

/-- Capacity is positive at finite distance. -/
theorem spatialCapacity_pos {X : Type*} [PseudoMetricSpace X]
    (sc : SpatialChannelModel X) (d : ℝ) : 0 < spatialCapacity sc d := by
  unfold spatialCapacity
  have hratio_pos : 0 < sc.signalPower / sc.noisePower d :=
    div_pos sc.signalPower_pos (sc.noisePower_pos d)
  have harg : 1 < 1 + sc.signalPower / sc.noisePower d := by linarith
  have hlog : 0 < Real.log (1 + sc.signalPower / sc.noisePower d) :=
    Real.log_pos harg
  have hhalf : 0 < (1/2 : ℝ) := by norm_num
  exact mul_pos hhalf hlog

/-! ## Capacity Constraints on Role Pairs -/

/-- Capacity between two roles determined by distance. -/
def roleCapacity {X : Type*} [PseudoMetricSpace X]
    (sc : SpatialChannelModel X) (loc : RoleLoc X) (r1 r2 : Role) : ℝ :=
  spatialCapacity sc (dist (loc r1) (loc r2))

/-- Colocated roles have maximum capacity (distance 0). -/
theorem colocated_max_capacity {X : Type*} [PseudoMetricSpace X]
    (sc : SpatialChannelModel X) (loc : RoleLoc X) (r1 r2 : Role)
    (h : Colocated loc r1 r2) :
    roleCapacity sc loc r1 r2 = spatialCapacity sc 0 := by
  unfold roleCapacity
  have hloc : loc r1 = loc r2 := by
    simpa [Colocated] using h
  simp [hloc]

/-- Roles within distance d have capacity ≥ spatialCapacity d. -/
theorem within_capacity_bound {X : Type*} [PseudoMetricSpace X]
    (sc : SpatialChannelModel X) (loc : RoleLoc X) (r1 r2 : Role) (d : ℝ)
    (hw : Within loc r1 r2 d) :
    spatialCapacity sc d ≤ roleCapacity sc loc r1 r2 := by
  have hanti := spatialCapacity_antitone sc
  have hcap : spatialCapacity sc d ≤ spatialCapacity sc (dist (loc r1) (loc r2)) := by
    exact hanti hw
  simpa [roleCapacity] using hcap

/-! ## Protocol Feasibility with Spatial Constraints -/

/-- A spatial protocol with per-edge rates. -/
structure SpatialProtocol (X : Type*) [PseudoMetricSpace X] where
  /-- Role-to-location assignment. -/
  roleLoc : RoleLoc X
  /-- Spatial channel model. -/
  channelModel : SpatialChannelModel X
  /-- Protocol edges with required rates. -/
  edges : List (Gibbs.Edge × ℝ)

/-- Feasibility: each edge fits within its spatial capacity. -/
def SpatialProtocol.isFeasible {X : Type*} [PseudoMetricSpace X]
    (sp : SpatialProtocol X) : Prop :=
  ∀ er ∈ sp.edges,
    er.2 ≤ roleCapacity sp.channelModel sp.roleLoc er.1.sender er.1.receiver

end

end Gibbs.ContinuumField.CapacityBridge
