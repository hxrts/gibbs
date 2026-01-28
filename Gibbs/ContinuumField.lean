import Gibbs.ContinuumField.Basic
import Gibbs.ContinuumField.Adaptivity
import Gibbs.ContinuumField.Kernel
import Gibbs.ContinuumField.Closure
import Gibbs.ContinuumField.Projection
import Gibbs.ContinuumField.EffectsIntegration
import Gibbs.ContinuumField.TimeBridge
import Gibbs.ContinuumField.SpatialBridge
import Gibbs.ContinuumField.Examples.Anisotropic2D

/-
The Problem. Provide a single entry point for the continuum-field layer so
clients can import space/time, kernel, projection, and Effects alignment
without enumerating individual files.

The difficulty is keeping the interface lightweight while preserving the
structured file layout. This file serves as a curated facade.

Solution Structure.
1. Re-export core continuum-field modules
-/

/-! # Continuum Field Layer -/
