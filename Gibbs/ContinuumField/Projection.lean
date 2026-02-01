import Gibbs.ContinuumField.Kernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Projection exactness

The nonlocal operator `∫ K(x,x')(p(x') - p(x)) dx'` can be written in two
equivalent forms: directly using the global kernel `K(x,x')`, or using the
projected local kernel `K_x(ξ) = K(x, x+ξ)` in displacement coordinates.
The exactness theorem shows these are *definitionally equal* in Lean, not
merely propositionally. This means projecting a global kernel to local form
introduces zero approximation error, and any computation done with local
kernels is faithful to the global operator.
-/

namespace Gibbs.ContinuumField

open scoped Classical

noncomputable section

/-! ## Nonlocal Operators -/

variable {X : Type*} [MeasureTheory.MeasureSpace X] [Add X]
-- Only addition is needed for displacement coordinates; no inverses used.
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Global nonlocal operator in displacement coordinates. -/
def nonlocalGlobal (K : GlobalKernel X) (p : X → V) (x : X) : V :=
  -- Integrate the global kernel against the displacement field
  ∫ ξ, (K.K x (x + ξ)) • (p (x + ξ) - p x)

/-- Local nonlocal operator using the projected kernel field. -/
def nonlocalLocal (K : GlobalKernel X) (p : X → V) (x : X) : V :=
  -- Same integrand, but via the local kernel field
  ∫ ξ, (GlobalKernel.localKernel K x ξ) • (p (x + ξ) - p x)

/-- Exactness: the local operator equals the global operator by definition. -/
theorem nonlocal_exact (K : GlobalKernel X) (p : X → V) (x : X) :
    nonlocalGlobal K p x = nonlocalLocal K p x := by
  -- Unfolding the projection shows the integrands coincide
  rfl

end

end Gibbs.ContinuumField
