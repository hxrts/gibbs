import Gibbs.ContinuumField.Kernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-
The Problem. We need an exact correspondence between the global nonlocal
operator and the local-kernel form obtained by projection. This is the core
"exactness" guarantee for global → local kernels.

The difficulty is keeping the statement minimal: we want a definitional
connection without invoking change-of-variables arguments. We therefore define
both operators in displacement form.

Solution Structure.
1. nonlocalGlobal: operator using the global kernel in displacement form
2. nonlocalLocal: operator using the projected local kernel field
3. exactness lemma: the two are definitionally equal
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
