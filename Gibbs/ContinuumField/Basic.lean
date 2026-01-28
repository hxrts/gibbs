import Mathlib

/-
The Problem. We need basic field-level objects for continuum models:
spatial fields, a bundled state (density, polarization, spin), and
lightweight aliases that can be reused by kernel and projection layers.

The difficulty is keeping the interface minimal while still expressing
adaptive kernels that depend on fields. We keep the state generic over
space and value types.

Solution Structure.
1. Field alias: X → V
2. FieldState: rho, p, omega bundled together
-/

namespace Gibbs.ContinuumField

open scoped Classical

/-! ## Field Primitives -/

/-- A field over space X with values in V. -/
abbrev Field (X : Type*) (V : Type*) := X → V  -- pointwise field

/-- Bundle the global state: density, polarization, and spin. -/
structure FieldState (X : Type*) (V : Type*) (W : Type*) where
  /-- Density field ρ(x). -/
  rho : Field X ℝ
  /-- Polarization field p(x). -/
  p : Field X V
  /-- Spin/turning field ω(x) (use W := PUnit if unused). -/
  omega : Field X W

/-- A version of FieldState without spin; uses PUnit as the value. -/
abbrev FieldStateNoSpin (X : Type*) (V : Type*) := FieldState X V PUnit  -- spin-free

end Gibbs.ContinuumField
