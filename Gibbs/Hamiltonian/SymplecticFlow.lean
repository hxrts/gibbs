import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.DampedFlow

/-!
Undamped (symplectic) Hamiltonian dynamics on phase space.

We implement the standard flow
  q̇ = ∇_p T,   ṗ = -∇_q V
and record the energy conservation identity (no dissipation).
-/

namespace Gibbs.Hamiltonian

open InnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ## Symplectic Drift -/

/-- Undamped Hamiltonian drift on phase space.
    q̇ = ∇_p T,  ṗ = -∇_q V. -/
def symplecticDrift (H : ConvexHamiltonian n) : PhasePoint n → PhasePoint n :=
  fun x => (H.velocity x.p, H.force x.q)

/-! ## Energy Conservation -/

/-- Energy derivative along the symplectic drift vanishes. -/
theorem symplectic_energy_conserved (H : ConvexHamiltonian n) (x : PhasePoint n) :
    energyDerivative H (symplecticDrift H) x = 0 := by
  -- Force is minus the potential gradient and velocity is the kinetic gradient.
  calc
    energyDerivative H (symplecticDrift H) x =
        ⟪gradient H.T x.p, -gradient H.V x.q⟫_ℝ +
          ⟪gradient H.V x.q, gradient H.T x.p⟫_ℝ := by
          simp [energyDerivative, symplecticDrift, ConvexHamiltonian.force,
            ConvexHamiltonian.velocity, PhasePoint.p, PhasePoint.q]
    _ = 0 := by
          simp [real_inner_comm, add_comm]

/-! ## Harmonic Oscillator Example -/

/-- Symplectic energy conservation for the harmonic oscillator Hamiltonian. -/
theorem harmonicOscillator_symplectic_energy (n : ℕ) (x : PhasePoint n) :
    energyDerivative (harmonicOscillator n) (symplecticDrift (harmonicOscillator n)) x = 0 := by
  simpa using (symplectic_energy_conserved (H := harmonicOscillator n) (x := x))

end

end Gibbs.Hamiltonian
