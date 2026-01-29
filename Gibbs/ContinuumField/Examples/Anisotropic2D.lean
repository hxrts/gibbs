import Gibbs.ContinuumField.Kernel
import Gibbs.ContinuumField.Projection
import Gibbs.ContinuumField.Closure
import Mathlib.Data.Real.Basic

/-
The Problem. We want a small, concrete 2D example that illustrates an
anisotropic local kernel profile, the exactness of global→local projection,
and how a closure summarizes a kernel without changing the core operator.

The difficulty is keeping this example lightweight. We provide simple 2D
vector helpers and reuse the exactness lemma and closure soundness contract.

Solution Structure.
1. 2D helper functions (dot, normSq)
2. Anisotropic local kernel profile
3. Example exactness + closure summaries
-/

namespace Gibbs.ContinuumField

open scoped Classical

/-! ## 2D Helpers -/

/-- 2D space as a pair of reals. -/
abbrev X2 := ℝ × ℝ

/-- Dot product on ℝ². -/
def dot (u v : X2) : ℝ :=
  -- Multiply and sum components for a basic inner product.
  u.1 * v.1 + u.2 * v.2

/-- Squared norm on ℝ². -/
def normSq (u : X2) : ℝ :=
  -- Reuse dot product with itself.
  dot u u

/-! ## Anisotropic Local Kernel -/

/-- A simple anisotropic local kernel profile in 2D. -/
noncomputable def anisotropicLocal (axis : X2) (range : ℝ) (α : ℝ) : KernelField X2 :=
  -- A rational bump with directional bias (no proofs required).
  fun ξ => (1 + α * dot axis ξ) / (1 + normSq ξ / range)

/-! ## Example Exactness and Closure -/

section WithKernel

variable [MeasureTheory.MeasureSpace X2]

/-- A bundled 2D example with a global kernel and anisotropy data. -/
structure Example2D where
  /-- The global kernel supplying exact nonlocal semantics. -/
  K : GlobalKernel X2
  /-- Directional axis for anisotropy (example parameter). -/
  axis : X2
  /-- Range parameter for the local profile. -/
  range : ℝ
  /-- Strength of anisotropy in the profile. -/
  anisotropy : ℝ

end WithKernel

section WithOperator

variable [MeasureTheory.MeasureSpace X2] [Add X2]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The projection exactness lemma specialized to the 2D example. -/
theorem example_exact (ex : Example2D) (p : X2 → V) (x : X2) :
    nonlocalGlobal ex.K p x = nonlocalLocal ex.K p x := by
  -- Reuse the generic exactness lemma.
  simpa using nonlocal_exact ex.K p x

end WithOperator

/-- Summarize a kernel field using a closure spec. -/
def exampleSummary (C : ClosureSpec X2) (Kx : KernelField X2) : KernelSummary X2 :=
  -- Apply the closure's summary map.
  C.close Kx

/-- The closure spec guarantees reconstruction accuracy. -/
theorem example_closure_bound (C : ClosureSpec X2) (Kx : KernelField X2) :
    KernelApprox Kx (C.reconstruct (C.close Kx)) C.bound := by
  -- This is exactly the closure soundness field.
  simpa using C.sound Kx

end Gibbs.ContinuumField
