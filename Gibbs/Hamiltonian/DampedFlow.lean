import Gibbs.Hamiltonian.ConvexHamiltonian
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

/-!
# Damped Hamiltonian Dynamics

Adding a friction term -gamma * p to the momentum equation breaks energy
conservation and introduces dissipation. The total energy now decreases along
trajectories, making it a natural Lyapunov candidate for stability analysis.

This file defines the damping parameter, the damped drift on phase space, and
the energy-derivative identity used in later dissipation proofs.
-/

namespace Gibbs.Hamiltonian

open scoped Classical
open scoped NNReal
open InnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ## Damping Parameter -/

/-- Damping parameter γ > 0. -/
structure Damping where
  /-- Damping coefficient -/
  γ : ℝ
  /-- Positivity of damping -/
  γ_pos : 0 < γ

/-! ## NNReal Coefficient -/

/-- Damping coefficient as a nonnegative real. -/
def gammaNN (d : Damping) : ℝ≥0 :=
  ⟨d.γ, le_of_lt d.γ_pos⟩

/-! ## Damped Drift -/

/-- Damped Hamiltonian drift on phase space.
    q̇ = ∇_p T,  ṗ = -∇_q V - γ p. -/
def dampedDrift (H : ConvexHamiltonian n) (d : Damping) :
    PhasePoint n → PhasePoint n :=
  fun x => (H.velocity x.p, H.force x.q - d.γ • x.p)

/-- q-component of the damped drift. -/
theorem dampedDrift_q (H : ConvexHamiltonian n) (d : Damping) (x : PhasePoint n) :
    (dampedDrift H d x).q = H.velocity x.p := by
  -- q̇ is the velocity component.
  rfl

/-- p-component of the damped drift. -/
theorem dampedDrift_p (H : ConvexHamiltonian n) (d : Damping) (x : PhasePoint n) :
    (dampedDrift H d x).p = H.force x.q - d.γ • x.p := by
  -- ṗ is the force minus linear damping.
  rfl

/-! ## Energy Derivative Helper -/

/-- Directional derivative of the Hamiltonian energy along a drift.
    This is the standard gradient pairing used in dissipation proofs. -/
def energyDerivative (H : ConvexHamiltonian n) (F : PhasePoint n → PhasePoint n)
    (x : PhasePoint n) : ℝ :=
  ⟪gradient H.T x.p, (F x).p⟫_ℝ + ⟪gradient H.V x.q, (F x).q⟫_ℝ

/-! ## Energy Dissipation -/

/-- Cross-term cancellation for Hamiltonian gradients. -/
private lemma inner_cancel (p q : Config n) :
    ⟪p, -q⟫_ℝ + ⟪q, p⟫_ℝ = 0 := by
  -- Use symmetry and negation of the inner product.
  simp [real_inner_comm, add_comm]

/-- Energy dissipation rate for damped drift under quadratic kinetic energy.

    This assumes `∇T = id`, i.e. `T(p) = ½‖p‖²`. -/
theorem energy_dissipation (H : ConvexHamiltonian n) (d : Damping)
    (hgrad : ∀ p, gradient H.T p = p) (x : PhasePoint n) :
    energyDerivative H (dampedDrift H d) x = -d.γ * PhasePoint.kineticNormSq x := by
  -- Expand the derivative and cancel Hamiltonian cross terms.
  have hcross :
      ⟪gradient H.T x.p, H.force x.q⟫_ℝ + ⟪gradient H.V x.q, H.velocity x.p⟫_ℝ = 0 := by
    -- Force is minus gradient and velocity is gradient.
    simp [ConvexHamiltonian.force, ConvexHamiltonian.velocity, real_inner_comm, add_comm]
  have hsplit :
      energyDerivative H (dampedDrift H d) x
        = ⟪gradient H.T x.p, H.force x.q⟫_ℝ
          + ⟪gradient H.V x.q, H.velocity x.p⟫_ℝ
          - d.γ * ⟪gradient H.T x.p, x.p⟫_ℝ := by
    -- Split the inner product over subtraction and scalar action.
    simp [energyDerivative, dampedDrift_p, dampedDrift_q, sub_eq_add_neg,
      inner_add_right, inner_neg_right, inner_smul_right,
      add_comm, add_left_comm, add_assoc]
  calc
    energyDerivative H (dampedDrift H d) x
        = ⟪gradient H.T x.p, H.force x.q⟫_ℝ
          + ⟪gradient H.V x.q, H.velocity x.p⟫_ℝ
          - d.γ * ⟪gradient H.T x.p, x.p⟫_ℝ := hsplit
    _ = -d.γ * ⟪gradient H.T x.p, x.p⟫_ℝ := by
      -- The cross terms cancel.
      linarith [hcross]
    _ = -d.γ * PhasePoint.kineticNormSq x := by
            -- Replace ∇T with identity and use ‖p‖² = ⟪p,p⟫.
            simp [PhasePoint.kineticNormSq, hgrad]

/-- Energy is non-increasing along trajectories with the dissipation derivative.
    This uses the first-derivative test for antitone functions. -/
theorem energy_decreasing (H : ConvexHamiltonian n) (d : Damping)
    (sol : ℝ → PhasePoint n)
    (hderiv : ∀ t,
      HasDerivAt (fun s => H.energy (sol s))
        (-d.γ * PhasePoint.kineticNormSq (sol t)) t) :
    ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → H.energy (sol t₂) ≤ H.energy (sol t₁) := by
  -- Derivative non-positivity gives antitone energy.
  have hnonpos :
      (fun t => -d.γ * PhasePoint.kineticNormSq (sol t)) ≤ 0 := by
    intro t
    have hk : 0 ≤ PhasePoint.kineticNormSq (sol t) :=
      PhasePoint.kineticNormSq_nonneg (sol t)
    have hγ : 0 ≤ d.γ := le_of_lt d.γ_pos
    have hmul : 0 ≤ d.γ * PhasePoint.kineticNormSq (sol t) := mul_nonneg hγ hk
    have hneg : -(d.γ * PhasePoint.kineticNormSq (sol t)) ≤ 0 := neg_nonpos.mpr hmul
    simpa [neg_mul] using hneg
  have hanti : Antitone (fun t => H.energy (sol t)) :=
    antitone_of_hasDerivAt_nonpos hderiv hnonpos
  intro t₁ t₂ _ ht
  exact hanti ht

/-! ## Lipschitz Continuity -/

/-- Projection to position is 1-Lipschitz under the max product metric. -/
private lemma proj_q_lipschitz : LipschitzWith 1 (fun x : PhasePoint n => x.q) := by
  -- The product distance is a max of the component distances.
  refine LipschitzWith.mk_one ?_
  intro x y
  simp [PhasePoint.q, Prod.dist_eq]

/-- Projection to momentum is 1-Lipschitz under the max product metric. -/
private lemma proj_p_lipschitz : LipschitzWith 1 (fun x : PhasePoint n => x.p) := by
  -- The product distance is a max of the component distances.
  refine LipschitzWith.mk_one ?_
  intro x y
  simp [PhasePoint.p, Prod.dist_eq]

/-- Force term is Lipschitz when ∇V is Lipschitz. -/
private lemma dist_force_le (H : ConvexHamiltonian n) (K_V : ℝ≥0)
    (hV : LipschitzWith K_V (gradient H.V)) (x y : PhasePoint n) :
    dist (H.force x.q) (H.force y.q) ≤ K_V * dist x.q y.q := by
  -- Negation preserves distances; use Lipschitz of ∇V.
  simpa [ConvexHamiltonian.force] using (hV.dist_le_mul x.q y.q)

/-- Damping term scales distances by γ. -/
private lemma dist_damp_le (d : Damping) (x y : PhasePoint n) :
    dist (d.γ • x.p) (d.γ • y.p) ≤ d.γ * dist x.p y.p := by
  -- Scaling by γ scales the distance.
  -- Rewrite as a scalar multiple of a difference.
  have h :
      dist (d.γ • x.p) (d.γ • y.p) = d.γ * dist x.p y.p := by
    calc
      dist (d.γ • x.p) (d.γ • y.p) = ‖d.γ • x.p - d.γ • y.p‖ := by
        simp [dist_eq_norm]
      _ = ‖d.γ • (x.p - y.p)‖ := by
        simp [smul_sub]
      _ = d.γ * ‖x.p - y.p‖ := by
        simp [norm_smul, Real.norm_of_nonneg (le_of_lt d.γ_pos)]
      _ = d.γ * dist x.p y.p := by
        simp [dist_eq_norm]
  exact le_of_eq h

/-- Position distance is bounded by the phase-space distance. -/
private lemma dist_q_le (x y : PhasePoint n) : dist x.q y.q ≤ dist x y := by
  -- Use the 1-Lipschitz projection.
  simpa [one_mul] using (proj_q_lipschitz.dist_le_mul x y)

/-- Momentum distance is bounded by the phase-space distance. -/
private lemma dist_p_le (x y : PhasePoint n) : dist x.p y.p ≤ dist x y := by
  -- Use the 1-Lipschitz projection.
  simpa [one_mul] using (proj_p_lipschitz.dist_le_mul x y)

/-- Combine component bounds into a max-metric bound. -/
private lemma force_damp_sum_le (d : Damping) (K_V : ℝ≥0) (x y : PhasePoint n) :
    (K_V : ℝ) * dist x.q y.q + d.γ * dist x.p y.p
      ≤ (K_V + gammaNN d) * dist x y := by
  -- Use component bounds and expand the product.
  have hK : (K_V : ℝ) * dist x.q y.q ≤ (K_V : ℝ) * dist x y :=
    mul_le_mul_of_nonneg_left (dist_q_le x y) K_V.coe_nonneg
  have hγ : d.γ * dist x.p y.p ≤ d.γ * dist x y :=
    mul_le_mul_of_nonneg_left (dist_p_le x y) (le_of_lt d.γ_pos)
  have hsum' : (K_V : ℝ) * dist x.q y.q + d.γ * dist x.p y.p
      ≤ (K_V : ℝ) * dist x y + d.γ * dist x y := add_le_add hK hγ
  have hcoe : ((K_V + gammaNN d) : ℝ) = (K_V : ℝ) + d.γ := by
    simp [gammaNN]
  simpa [hcoe, add_mul] using hsum'

/-- q-component of damped drift is Lipschitz if ∇T is Lipschitz. -/
private lemma dampedDrift_q_lipschitz (H : ConvexHamiltonian n) (d : Damping)
    (K_T : ℝ≥0) (hT : LipschitzWith K_T (gradient H.T)) :
    LipschitzWith K_T (fun x : PhasePoint n => (dampedDrift H d x).q) := by
  -- q̇ depends only on p, so compose with the projection.
  simpa [dampedDrift_q, mul_one] using hT.comp proj_p_lipschitz

/-- p-component of damped drift is Lipschitz if ∇V is Lipschitz. -/
private lemma dampedDrift_p_lipschitz (H : ConvexHamiltonian n) (d : Damping)
    (K_V : ℝ≥0) (hV : LipschitzWith K_V (gradient H.V)) :
    LipschitzWith (K_V + gammaNN d)
      (fun x : PhasePoint n => (dampedDrift H d x).p) := by
  -- Bound the distance by force and damping contributions.
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have htriangle :
      dist ((dampedDrift H d x).p) ((dampedDrift H d y).p)
        ≤ dist (H.force x.q) (H.force y.q) + dist (d.γ • x.p) (d.γ • y.p) := by
    -- Split the sum using `dist_add_add_le`.
    simpa [dampedDrift_p, sub_eq_add_neg] using
      (dist_add_add_le (H.force x.q) (-d.γ • x.p) (H.force y.q) (-d.γ • y.p))
  have hforce := dist_force_le H K_V hV x y
  have hdamp := dist_damp_le d x y
  have hsum :
      (K_V : ℝ) * dist x.q y.q + d.γ * dist x.p y.p ≤ (K_V + gammaNN d) * dist x y :=
    force_damp_sum_le d K_V x y
  exact (htriangle.trans (add_le_add hforce hdamp)).trans hsum

/-- The damped drift is Lipschitz when ∇T and ∇V are Lipschitz. -/
theorem dampedDrift_lipschitz (H : ConvexHamiltonian n) (d : Damping)
    (K_T K_V : ℝ≥0)
    (hT : LipschitzWith K_T (gradient H.T))
    (hV : LipschitzWith K_V (gradient H.V)) :
    LipschitzWith (max K_T (K_V + gammaNN d)) (dampedDrift H d) := by
  -- Combine component Lipschitz bounds using the product max metric.
  simpa using (dampedDrift_q_lipschitz H d K_T hT).prodMk
    (dampedDrift_p_lipschitz H d K_V hV)

/-- Damped drift is globally Lipschitz with an explicit constant.
    This is the hypothesis required for Picard–Lindelöf ODE existence. -/
theorem dampedDrift_hasLipschitz (H : ConvexHamiltonian n) (d : Damping)
    (K_T K_V : ℝ≥0)
    (hT : LipschitzWith K_T (gradient H.T))
    (hV : LipschitzWith K_V (gradient H.V)) :
    ∃ K, LipschitzWith K (dampedDrift H d) := by
  -- Provide the explicit Lipschitz constant.
  refine ⟨max K_T (K_V + gammaNN d), ?_⟩
  exact dampedDrift_lipschitz H d K_T K_V hT hV

end

end Gibbs.Hamiltonian
