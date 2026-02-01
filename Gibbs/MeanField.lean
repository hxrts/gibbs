import Gibbs.MeanField.Basic
import Gibbs.MeanField.Rules
import Gibbs.MeanField.Choreography
import Gibbs.MeanField.LipschitzBridge
import Gibbs.MeanField.ODE
import Gibbs.MeanField.Existence
import Gibbs.MeanField.Stability
import Gibbs.MeanField.Projection
import Gibbs.MeanField.OrderParameter
import Gibbs.MeanField.Universality
import Gibbs.MeanField.Examples.Ising

/-!
# Mean-Field Layer

Single entry point for the mean-field layer. Importing this file brings in
simplex and population types, transition rules, choreography constraints,
the Lipschitz bridge to Mathlib ODE infrastructure, existence and stability
theorems, global-to-local projection, order parameters, universality classes,
and the Ising model example.
-/
