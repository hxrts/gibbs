import Gibbs.MeanField.Choreography
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz Bridge to Mathlib ODE Infrastructure

Mathlib's Picard-Lindelof and Gronwall theorems require globally Lipschitz
functions on normed spaces, but our drift is defined only on the simplex. This
file bridges the gap: it converts the simplex-local Lipschitz predicate to
Mathlib's `LipschitzOnWith`, extends the drift to the ambient space while
preserving the Lipschitz constant, and wraps time-dependent and choreography
drifts for direct use with Mathlib's ODE solvers.
-/

namespace Gibbs.MeanField

open scoped Classical NNReal

noncomputable section

variable {Q : Type*} [Fintype Q]

/-! ## Converting to Mathlib's LipschitzOnWith -/

/-- Our Lipschitz condition implies Mathlib's LipschitzOnWith on the simplex. -/
theorem DriftFunction.toLipschitzOnWith (F : DriftFunction Q) (K : ℝ≥0)
    (hLip : DriftFunction.IsLipschitz F K) :
    LipschitzOnWith K F (Simplex Q) := by
  intro x hx y hy
  have h := hLip x y hx hy
  simp only [edist_dist, dist_eq_norm]
  calc ENNReal.ofReal ‖F x - F y‖
      ≤ ENNReal.ofReal (K * ‖x - y‖) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal K * ENNReal.ofReal ‖x - y‖ := ENNReal.ofReal_mul K.2
    _ = ↑K * ENNReal.ofReal ‖x - y‖ := by rw [ENNReal.ofReal_coe_nnreal]

/-! ## Extending Drift to Whole Space -/

/-- Extend a drift function from the simplex to the whole space.
    Uses Mathlib's `LipschitzOnWith.extend_pi`. -/
def DriftFunction.extend (F : DriftFunction Q) (K : ℝ≥0)
    (hLip : DriftFunction.IsLipschitz F K) : DriftFunction Q :=
  (DriftFunction.toLipschitzOnWith F K hLip).extend_pi.choose

/-- The extended drift is globally Lipschitz. -/
theorem DriftFunction.extend_lipschitz (F : DriftFunction Q) (K : ℝ≥0)
    (hLip : DriftFunction.IsLipschitz F K) :
    LipschitzWith K (DriftFunction.extend F K hLip) :=
  (DriftFunction.toLipschitzOnWith F K hLip).extend_pi.choose_spec.1

/-- The extended drift agrees with F on the simplex. -/
theorem DriftFunction.extend_eqOn (F : DriftFunction Q) (K : ℝ≥0)
    (hLip : DriftFunction.IsLipschitz F K) :
    Set.EqOn F (DriftFunction.extend F K hLip) (Simplex Q) :=
  (DriftFunction.toLipschitzOnWith F K hLip).extend_pi.choose_spec.2

/-- For points in the simplex, extended drift equals original drift. -/
@[simp]
theorem DriftFunction.extend_apply (F : DriftFunction Q) (K : ℝ≥0)
    (hLip : DriftFunction.IsLipschitz F K) (x : Q → ℝ) (hx : x ∈ Simplex Q) :
    DriftFunction.extend F K hLip x = F x :=
  (DriftFunction.extend_eqOn F K hLip hx).symm

/-! ## Converting Real Lipschitz to NNReal Lipschitz -/

/-- If F is Lipschitz with real constant L, it's also Lipschitz with max L 0. -/
theorem DriftFunction.isLipschitz_max (F : DriftFunction Q) (L : ℝ)
    (hLip : DriftFunction.IsLipschitz F L) :
    DriftFunction.IsLipschitz F (max L 0) := by
  intro x y hx hy
  have h := hLip x y hx hy
  calc ‖F x - F y‖
      ≤ L * ‖x - y‖ := h
    _ ≤ max L 0 * ‖x - y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- Convert a real Lipschitz constant to NNReal. -/
def toNNRealLipschitz (L : ℝ) : ℝ≥0 := ⟨max L 0, le_max_right _ _⟩

/-- A drift with real Lipschitz constant is also Lipschitz with the NNReal version. -/
theorem DriftFunction.isLipschitz_nnreal (F : DriftFunction Q) (L : ℝ)
    (hLip : DriftFunction.IsLipschitz F L) :
    DriftFunction.IsLipschitz F (toNNRealLipschitz L) :=
  DriftFunction.isLipschitz_max F L hLip

/-! ## Time-Dependent Wrapper -/

/-- Wrap autonomous drift as time-dependent for Mathlib ODE theorems. -/
def toTimeDep (F : DriftFunction Q) : ℝ → (Q → ℝ) → (Q → ℝ) :=
  fun _t x => F x

/-- The time-dependent wrapper of extended drift is globally Lipschitz at each time. -/
theorem toTimeDep_lipschitz (F : DriftFunction Q) (K : ℝ≥0)
    (hLip : DriftFunction.IsLipschitz F K) (t : ℝ) :
    LipschitzWith K (toTimeDep (DriftFunction.extend F K hLip) t) :=
  DriftFunction.extend_lipschitz F K hLip

/-! ## Choreography Integration -/

/-- Extract a non-negative Lipschitz constant from a choreography. -/
def MeanFieldChoreography.lipschitzConstNNReal (C : MeanFieldChoreography Q) : ℝ≥0 :=
  toNNRealLipschitz C.lipschitzConst

/-- The Lipschitz property holds for the drift with the NNReal constant. -/
theorem MeanFieldChoreography.drift_isLipschitz_nnreal (C : MeanFieldChoreography Q) :
    DriftFunction.IsLipschitz C.drift C.lipschitzConstNNReal :=
  DriftFunction.isLipschitz_nnreal C.drift C.lipschitzConst C.drift_lipschitz.choose_spec

/-- Extend a choreography's drift to the whole space. -/
def MeanFieldChoreography.extendDrift (C : MeanFieldChoreography Q) : DriftFunction Q :=
  DriftFunction.extend C.drift C.lipschitzConstNNReal C.drift_isLipschitz_nnreal

/-- The extended drift of a choreography is globally Lipschitz. -/
theorem MeanFieldChoreography.extendDrift_lipschitz (C : MeanFieldChoreography Q) :
    LipschitzWith C.lipschitzConstNNReal C.extendDrift :=
  DriftFunction.extend_lipschitz C.drift C.lipschitzConstNNReal C.drift_isLipschitz_nnreal

/-- The extended drift agrees with original on simplex. -/
@[simp]
theorem MeanFieldChoreography.extendDrift_apply (C : MeanFieldChoreography Q)
    (x : Q → ℝ) (hx : x ∈ Simplex Q) :
    C.extendDrift x = C.drift x :=
  DriftFunction.extend_apply C.drift C.lipschitzConstNNReal C.drift_isLipschitz_nnreal x hx

/-- Time-dependent wrapper for choreography's extended drift. -/
def MeanFieldChoreography.extendDriftTimeDep (C : MeanFieldChoreography Q) :
    ℝ → (Q → ℝ) → (Q → ℝ) :=
  toTimeDep C.extendDrift

/-- The time-dependent extended drift is Lipschitz at each time. -/
theorem MeanFieldChoreography.extendDriftTimeDep_lipschitz (C : MeanFieldChoreography Q) (t : ℝ) :
    LipschitzWith C.lipschitzConstNNReal (C.extendDriftTimeDep t) := by
  unfold extendDriftTimeDep toTimeDep
  exact C.extendDrift_lipschitz

end

end Gibbs.MeanField
