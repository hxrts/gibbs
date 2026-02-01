import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Phase Space Foundations

Hamiltonian mechanics lives on phase space, the product of position and momentum
coordinates. This file defines `Config` (configuration space) and `PhasePoint`
(the full phase space), along with equilibrium predicates and inherited metric
structure.

We use `EuclideanSpace ℝ (Fin n)` rather than `Fin n → ℝ` because
`EuclideanSpace` carries the `InnerProductSpace` instance that Mathlib's
gradient and calculus API requires.
-/

namespace Gibbs.Hamiltonian

open scoped Classical

noncomputable section

/-! ## Configuration and Phase Space -/

/-- Configuration space: positions indexed by Fin n.
    Using EuclideanSpace ensures InnerProductSpace instance for gradients. -/
abbrev Config (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Phase space: paired position and momentum vectors.
    This is the natural state space for Hamiltonian dynamics. -/
abbrev PhasePoint (n : ℕ) := Config n × Config n

namespace PhasePoint

variable {n : ℕ}

/-! ## Projections -/

/-- Extract the position component q from a phase point. -/
@[reducible] def q (x : PhasePoint n) : Config n := x.1

/-- Extract the momentum component p from a phase point. -/
@[reducible] def p (x : PhasePoint n) : Config n := x.2

/-- Construct a phase point from position and momentum. -/
def mk (q p : Config n) : PhasePoint n := (q, p)

theorem mk_q_p (x : PhasePoint n) : mk (q x) (p x) = x := rfl

theorem q_mk (q' p' : Config n) : q (mk q' p') = q' := rfl

theorem p_mk (q' p' : Config n) : p (mk q' p') = p' := rfl

/-! ## Equilibrium Conditions -/

/-- A phase point is at rest when momentum is zero.
    This is a necessary condition for equilibrium. -/
@[reducible] def isAtRest (x : PhasePoint n) : Prop := x.p = 0

/-- Embed a position into phase space with zero momentum.
    Used to lift configuration-space equilibria to phase space. -/
@[reducible] def fromPosition (q : Config n) : PhasePoint n := (q, (0 : Config n))

theorem fromPosition_q (q : Config n) : (fromPosition q).q = q := rfl

theorem fromPosition_p (q : Config n) : (fromPosition q).p = 0 := rfl

theorem fromPosition_isAtRest (q : Config n) : isAtRest (fromPosition q) := by
  -- isAtRest x means x.p = 0, i.e., p x = 0
  -- fromPosition q = (q, 0), so p (q, 0) = (q, 0).2 = 0
  simp only [isAtRest, p]

/-! ## Kinetic Energy Norm -/

/-- Squared norm of momentum: ‖p‖².
    This appears in kinetic energy and dissipation formulas. -/
def kineticNormSq (x : PhasePoint n) : ℝ := ‖x.p‖^2

theorem kineticNormSq_nonneg (x : PhasePoint n) : 0 ≤ kineticNormSq x := sq_nonneg _

theorem kineticNormSq_eq_zero_iff (x : PhasePoint n) :
    kineticNormSq x = 0 ↔ isAtRest x := by
  simp only [kineticNormSq, sq_eq_zero_iff, norm_eq_zero, isAtRest]

theorem fromPosition_kineticNormSq (q : Config n) :
    kineticNormSq (fromPosition q) = 0 := by
  simp [kineticNormSq, fromPosition]

/-! ## Phase Space Metric -/

/-- Phase space inherits the product metric from Config × Config.
    This is the max metric: d((q₁,p₁), (q₂,p₂)) = max(‖q₁-q₂‖, ‖p₁-p₂‖). -/
instance : MetricSpace (PhasePoint n) := inferInstance

instance : NormedAddCommGroup (PhasePoint n) := inferInstance

/-- Phase space distance decomposes into position and momentum parts. -/
theorem dist_eq_max (x y : PhasePoint n) :
    dist x y = max (dist x.q y.q) (dist x.p y.p) := by
  simp only [q, p, Prod.dist_eq]

/-! ## Zero Phase Point -/

/-- The origin in phase space: (0, 0). -/
def zero : PhasePoint n := (0, 0)

theorem zero_q : (zero : PhasePoint n).q = 0 := rfl

theorem zero_p : (zero : PhasePoint n).p = 0 := rfl

theorem zero_isAtRest : isAtRest (zero : PhasePoint n) := rfl

end PhasePoint

end

end Gibbs.Hamiltonian
