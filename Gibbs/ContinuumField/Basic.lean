import Mathlib

/-!
# Continuum field primitives

The basic degrees of freedom for spatially extended models. A *field* is a
function from positions `X` to values `V`, and the global state bundles three
fields: density `ρ(x)`, polarization `p(x)`, and spin/turning `ω(x)`. These
are the continuum analogues of the discrete per-process states in the
consensus layer. All kernel, projection, and closure machinery is
parameterized over this generic state bundle.
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
