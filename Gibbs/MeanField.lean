import Gibbs.MeanField.Basic
import Gibbs.MeanField.Rules
import Gibbs.MeanField.Choreography
import Gibbs.MeanField.LipschitzBridge
import Gibbs.MeanField.ODE
import Gibbs.MeanField.Existence
import Gibbs.MeanField.Stability
import Gibbs.MeanField.Projection
import Gibbs.MeanField.Examples.Ising

/-
The Problem. Provide a single entry point for the mean-field layer so
clients can import simplex, drift, ODE, stability, and projection
without enumerating individual files.

The difficulty is keeping the interface lightweight while preserving the
structured file layout. This file serves as a curated facade.

Solution Structure.
1. Re-export core mean-field modules
-/

/-! # Mean Field Layer -/
