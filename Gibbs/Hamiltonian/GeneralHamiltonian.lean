import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.ConvexHamiltonian
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
General (possibly non-convex, non-separable) Hamiltonians on phase space.

This file introduces a Hamiltonian `H : PhasePoint n → ℝ` with gradients in
each component, and defines the canonical symplectic drift. Convex-specific
results remain in `ConvexHamiltonian` and related modules.
-/

namespace Gibbs.Hamiltonian

noncomputable section

variable {n : ℕ}

/-! ## General Hamiltonian Structure -/

/-- A Hamiltonian on phase space with differentiability in each component. -/
structure GeneralHamiltonian (n : ℕ) where
  /-- Full Hamiltonian energy on phase space. -/
  H : PhasePoint n → ℝ
  /-- Differentiable in position for every fixed momentum. -/
  diff_q : ∀ p : Config n, Differentiable ℝ (fun q => H (q, p))
  /-- Differentiable in momentum for every fixed position. -/
  diff_p : ∀ q : Config n, Differentiable ℝ (fun p => H (q, p))

namespace GeneralHamiltonian

/-- Gradient with respect to position. -/
def grad_q (H : GeneralHamiltonian n) (q p : Config n) : Config n :=
  gradient (fun q' => H.H (q', p)) q

/-- Gradient with respect to momentum. -/
def grad_p (H : GeneralHamiltonian n) (q p : Config n) : Config n :=
  gradient (fun p' => H.H (q, p')) p

/-- Canonical symplectic drift for a general Hamiltonian. -/
def drift (H : GeneralHamiltonian n) : PhasePoint n → PhasePoint n :=
  fun x => (H.grad_p x.q x.p, -H.grad_q x.q x.p)

end GeneralHamiltonian

/-! ## Separable Hamiltonians as a Special Case -/

/-- A separable convex Hamiltonian induces a general Hamiltonian. -/
def ConvexHamiltonian.toGeneral (H : ConvexHamiltonian n) : GeneralHamiltonian n :=
  { H := fun x => H.energy x
    diff_q := by
      intro p
      change Differentiable ℝ (fun q : Config n => H.T p + H.V q)
      exact (H.V_diff.const_add (H.T p))
    diff_p := by
      intro q
      change Differentiable ℝ (fun p : Config n => H.T p + H.V q)
      exact (H.T_diff.add_const (H.V q)) }

end

end Gibbs.Hamiltonian
