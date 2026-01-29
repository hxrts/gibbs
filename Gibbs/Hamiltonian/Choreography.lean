import Gibbs.Basic
import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.DampedFlow

/-
The Problem. We want a choreography wrapper for Hamiltonian systems: a way to
assign coordinates to roles, and a way to project Hamiltonian dynamics to a
mean-field style drift on configuration space.

The difficulty is keeping the structure lightweight while still recording the
role partition of coordinates. We also want phase-space messages that can be
routed through the existing choreography layer without rebuilding it.

Solution Structure.
1. Define `HamiltonianChoreography` with Hamiltonian, damping, and role cover.
2. Provide a mean-field drift projection on positions only.
3. Define `PhaseMessage` for position, momentum, force, and coupled states.
-/

namespace Gibbs.Hamiltonian

open scoped Classical

noncomputable section

/-! ## Choreography Structure -/

/-- Hamiltonian choreography bundles a Hamiltonian with a role partition.
    Roles act on disjoint coordinate sets in the configuration space. -/
structure HamiltonianChoreography (n : ℕ) where
  /-- Base Hamiltonian that defines the dynamics. -/
  ham : ConvexHamiltonian n
  /-- Linear damping coefficient used in the damped drift. -/
  damping : Damping
  /-- Role-local coordinate ownership. -/
  roles : Role → Finset (Fin n)
  /-- Every coordinate is owned by a unique role. -/
  roles_partition : ∀ i, ∃! r, i ∈ roles r

/-! ## Mean-Field Projection -/

/-- Project a Hamiltonian choreography to configuration-space drift.
    This is the force field on positions (slow manifold). -/
noncomputable def HamiltonianChoreography.toMeanFieldDrift
    (C : HamiltonianChoreography n) : Config n → Config n := by
  -- Drop momentum and use the force field on positions.
  exact fun q => C.ham.force q

/-! ## Role-Local Projections -/

/-- Project a configuration to a role by zeroing non-owned coordinates. -/
noncomputable def HamiltonianChoreography.projectConfig
    (C : HamiltonianChoreography n) (r : Role) (q : Config n) : Config n := by
  -- Keep coordinates owned by the role and zero out the rest.
  classical
  exact (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
    (fun i => if i ∈ C.roles r then q i else 0)

/-- Project a phase point to a role (apply projection to q and p). -/
noncomputable def HamiltonianChoreography.projectPhase
    (C : HamiltonianChoreography n) (r : Role) (x : PhasePoint n) : PhasePoint n := by
  -- Apply the coordinate projection componentwise.
  exact (C.projectConfig r x.q, C.projectConfig r x.p)

/-! ## Phase Messages -/

/-- Messages in phase space: positions, momenta, forces, or full state. -/
inductive PhaseMessage (n : ℕ) where
  | position : Config n → PhaseMessage n
  | momentum : Config n → PhaseMessage n
  | force : Config n → PhaseMessage n
  | coupled : PhasePoint n → PhaseMessage n

/-! ## Coherence Conditions -/

/-- Role ownership sets are disjoint for distinct roles. -/
theorem roles_disjoint (C : HamiltonianChoreography n) (r₁ r₂ : Role) (h : r₁ ≠ r₂) :
    Disjoint (C.roles r₁) (C.roles r₂) := by
  -- Uniqueness of ownership implies disjointness.
  classical
  refine Finset.disjoint_left.2 ?_
  intro i hi₁ hi₂
  obtain ⟨r, hr, huniq⟩ := C.roles_partition i
  have hr₁ : r₁ = r := huniq r₁ hi₁
  have hr₂ : r₂ = r := huniq r₂ hi₂
  exact h (hr₁.trans hr₂.symm)

/-- Coordinate formula for role projection. -/
theorem projectConfig_apply (C : HamiltonianChoreography n) (r : Role)
    (q : Config n) (i : Fin n) :
    C.projectConfig r q i = if i ∈ C.roles r then q i else 0 := by
  -- Unfold the projection and evaluate the coordinate.
  simp [HamiltonianChoreography.projectConfig]

/-- Projection keeps owned coordinates unchanged. -/
theorem projectConfig_eq_of_mem (C : HamiltonianChoreography n) (r : Role)
    (q : Config n) {i : Fin n} (hi : i ∈ C.roles r) :
    C.projectConfig r q i = q i := by
  -- The indicator selects the original coordinate.
  simp [projectConfig_apply, hi]

/-- Projection zeroes non-owned coordinates. -/
theorem projectConfig_eq_zero_of_not_mem (C : HamiltonianChoreography n) (r : Role)
    (q : Config n) {i : Fin n} (hi : i ∉ C.roles r) :
    C.projectConfig r q i = 0 := by
  -- The indicator selects zero off the owned set.
  simp [projectConfig_apply, hi]

/-- Projections to different roles do not overlap on owned coordinates. -/
theorem projectConfig_disjoint (C : HamiltonianChoreography n) (r₁ r₂ : Role)
    (h : r₁ ≠ r₂) (q : Config n) {i : Fin n} (hi : i ∈ C.roles r₁) :
    C.projectConfig r₂ q i = 0 := by
  -- Use disjointness of ownership sets.
  have hdis := roles_disjoint C r₁ r₂ h
  have hi' : i ∉ C.roles r₂ := by
    exact (Finset.disjoint_left.1 hdis) hi
  exact projectConfig_eq_zero_of_not_mem C r₂ q hi'

end

end Gibbs.Hamiltonian
