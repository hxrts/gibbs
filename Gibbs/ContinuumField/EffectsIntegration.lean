import Gibbs.ContinuumField.TimeBridge
import Gibbs.ContinuumField.Kernel
import Gibbs.ContinuumField.Projection
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-
The Problem. We need a minimal interface between choreography-level kernel
specifications and local environments that carry kernel fields, together with
a coherence check and a projection-soundness lemma for the nonlocal operator.

The difficulty is keeping the interface lightweight while still connecting to
role locations and exactness. We therefore define kernel declarations, local
kernel environments, and a simple soundness lemma that reuses the exactness
result.

Solution Structure.
1. KernelDecl + LocalKernelEnv
2. Coherence predicate and projection map
3. Projection soundness lemma for nonlocal operator
-/

namespace Gibbs.ContinuumField

open scoped Classical
open MeasureTheory

noncomputable section

/-! ## Choreography Kernel Declarations -/

/-- Choreography-level kernel declaration. -/
structure KernelDecl (X : Type*) [MeasureTheory.MeasureSpace X] where
  -- Package a global kernel as a choreography declaration.
  kernel : GlobalKernel X

/-! ## Local Kernel Environments -/

/-- Local environment carrying a kernel field per role. -/
structure LocalKernelEnv (X : Type*) (R : Type*) where
  -- Each role is assigned a local kernel field.
  kernelAt : R → KernelField X

/-- Project a global kernel to each role using its location. -/
def projectKernelAt {X : Type*} [MeasureTheory.MeasureSpace X] [Add X]
    (loc : RoleLoc X) (K : GlobalKernel X) : Role → KernelField X :=
  -- Use the displacement projection at each role's location.
  fun r => GlobalKernel.localKernel K (loc r)

/-- Coherence: local kernel fields match the global projection. -/
def KernelCoherent {X : Type*} [MeasureTheory.MeasureSpace X] [Add X]
    (loc : RoleLoc X) (K : GlobalKernel X) (env : LocalKernelEnv X Role) : Prop :=
  -- Every role's kernel is the projected global kernel at its location.
  ∀ r, env.kernelAt r = GlobalKernel.localKernel K (loc r)

/-! ## Local Operator and Soundness -/

variable {X : Type*} [MeasureTheory.MeasureSpace X] [Add X]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Nonlocal operator built directly from a local kernel field. -/
def nonlocalFromField (Kx : KernelField X) (p : X → V) (x : X) : V :=
  -- Integrate the displacement kernel against the polarization field.
  ∫ ξ, Kx ξ • (p (x + ξ) - p x)

/-- Projection soundness: coherent locals reproduce the global operator. -/
theorem projection_sound
    (loc : RoleLoc X) (K : GlobalKernel X) (env : LocalKernelEnv X Role)
    (p : X → V) (r : Role) (hcoh : KernelCoherent loc K env) :
    nonlocalFromField (env.kernelAt r) p (loc r) =
      nonlocalGlobal K p (loc r) := by
  -- Rewrite by coherence and unfold the projection definition.
  have hker : env.kernelAt r = GlobalKernel.localKernel K (loc r) := hcoh r
  -- Use the definitional equality between localKernel and global K.
  simp [nonlocalFromField, nonlocalGlobal, hker, GlobalKernel.localKernel]

end

end Gibbs.ContinuumField
