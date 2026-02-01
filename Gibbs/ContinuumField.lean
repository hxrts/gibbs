import Gibbs.ContinuumField.Basic
import Gibbs.ContinuumField.Adaptivity
import Gibbs.ContinuumField.Kernel
import Gibbs.ContinuumField.Closure
import Gibbs.ContinuumField.Projection
import Gibbs.ContinuumField.EffectsIntegration
import Gibbs.ContinuumField.TimeBridge
import Gibbs.ContinuumField.SpatialBridge
import Gibbs.ContinuumField.Examples.Anisotropic2D

/-!
# Continuum field layer facade

Single entry point for the continuum-field layer. Importing this file brings
in field primitives, interaction kernels, projection exactness, closure
approximation, adaptive kernel dependence, space/time bridging, Telltale
spatial alignment, and the 2D anisotropic example.
-/
