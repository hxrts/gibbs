import Gibbs.ContinuumField.TimeBridge
import Gibbs.ContinuumField.Kernel
import Gibbs.ContinuumField.Projection
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Choreography-to-kernel integration

Connects choreography-level kernel declarations to local kernel environments
carried by individual roles. A `KernelDecl` wraps a global kernel as a
choreography specification. A `LocalKernelEnv` assigns each role a local
kernel field. The `KernelCoherent` predicate asserts that every role's local
kernel matches the global kernel projected to that role's location.

The projection-soundness theorem shows that when coherence holds, evaluating
the nonlocal operator from local kernel fields reproduces the global operator
exactly. This closes the loop: choreography-level specifications project
faithfully to role-level computations.
-/

namespace Gibbs.ContinuumField

open scoped Classical
open MeasureTheory

noncomputable section

/-! ## Choreography Kernel Declarations -/

/-- Choreography-level kernel declaration. -/
structure KernelDecl (X : Type*) [MeasureTheory.MeasureSpace X] where
  /-- A global kernel packaged as a choreography declaration. -/
  kernel : GlobalKernel X

/-! ## Local Kernel Environments -/

/-- Local environment carrying a kernel field per role. -/
structure LocalKernelEnv (X : Type*) (R : Type*) where
  /-- Each role is assigned a local kernel field. -/
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
-- Only addition is needed for displacement coordinates; no inverses used.
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
