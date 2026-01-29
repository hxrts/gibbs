import Mathlib
import Gibbs.Hamiltonian.Basic

/-
The Problem. Provide a stochastic Langevin core together with a full proof
that the Gibbs density is stationary for the associated Fokker–Planck equation.

The difficulty is keeping the stochastic side lightweight while still
formalizing the PDE-level stationary statement. We follow a direct
calculus proof, specialized to the quadratic kinetic energy 1/2‖p‖².

Solution Structure.
1. Define Langevin parameters and Brownian effects.
2. Define the Euler–Maruyama update and Fokker–Planck operator.
3. Prove the Gibbs density is stationary under fluctuation–dissipation.
-/

namespace Gibbs.Hamiltonian.Stochastic

open Gibbs.Hamiltonian
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

noncomputable section

lemma toDual_symm_innerSL_ofLp (v : Config n) (i : Fin n) :
    ((InnerProductSpace.toDual ℝ (Config n)).symm ((innerSL ℝ) v)).ofLp i = v.ofLp i := by
  have h' :
      inner ℝ ((InnerProductSpace.toDual ℝ (Config n)).symm ((innerSL ℝ) v))
          (EuclideanSpace.single i (1 : ℝ)) =
        (innerSL ℝ v) (EuclideanSpace.single i (1 : ℝ)) := by
    exact
      (InnerProductSpace.toDual_symm_apply
        (x := EuclideanSpace.single i (1 : ℝ)) (y := (innerSL ℝ) v))
  have h'' :
      inner ℝ ((InnerProductSpace.toDual ℝ (Config n)).symm ((innerSL ℝ) v))
          (EuclideanSpace.single i (1 : ℝ)) =
        inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
    calc
      inner ℝ ((InnerProductSpace.toDual ℝ (Config n)).symm ((innerSL ℝ) v))
          (EuclideanSpace.single i (1 : ℝ)) =
          (innerSL ℝ v) (EuclideanSpace.single i (1 : ℝ)) := h'
      _ = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
            simp [innerSL_apply_apply]
  have h :
      inner ℝ (EuclideanSpace.single i (1 : ℝ))
          ((InnerProductSpace.toDual ℝ (Config n)).symm ((innerSL ℝ) v)) =
        inner ℝ (EuclideanSpace.single i (1 : ℝ)) v := by
    calc
      inner ℝ (EuclideanSpace.single i (1 : ℝ))
          ((InnerProductSpace.toDual ℝ (Config n)).symm ((innerSL ℝ) v)) =
          inner ℝ ((InnerProductSpace.toDual ℝ (Config n)).symm ((innerSL ℝ) v))
            (EuclideanSpace.single i (1 : ℝ)) := by
              rw [real_inner_comm]
      _ = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := h''
      _ = inner ℝ (EuclideanSpace.single i (1 : ℝ)) v := by
            rw [real_inner_comm]
  simpa [EuclideanSpace.inner_single_left] using h

/-! ## Langevin Parameters -/

/-- Parameters for full Langevin dynamics with quadratic kinetic energy. -/
structure LangevinParams (n : ℕ) where
  /-- Potential energy. -/
  V : Config n → ℝ
  /-- Damping coefficient. -/
  γ : ℝ
  /-- Thermal energy (k_B · T). -/
  kT : ℝ
  /-- Potential is differentiable. -/
  V_diff : Differentiable ℝ V
  /-- Damping is positive. -/
  γ_pos : 0 < γ
  /-- Temperature is positive. -/
  kT_pos : 0 < kT

variable {n : ℕ}

/-- Noise strength from fluctuation–dissipation: σ = √(2γkT). -/
def LangevinParams.σ (L : LangevinParams n) : ℝ :=
  Real.sqrt (2 * L.γ * L.kT)

/-- The fluctuation–dissipation relation: σ² = 2γkT. -/
theorem LangevinParams.σ_sq (L : LangevinParams n) :
    L.σ ^ 2 = 2 * L.γ * L.kT := by
  simp [LangevinParams.σ]
  exact Real.sq_sqrt (by nlinarith [L.γ_pos, L.kT_pos])

/-! ## Brownian Effect Signature -/

/-- A Brownian increment with specified time step. -/
structure BrownianIncrement (n : ℕ) where
  /-- Increment vector ΔW. -/
  value : Config n
  /-- Time step. -/
  dt : ℝ
  /-- Time step is positive. -/
  dt_pos : 0 < dt

/-- Abstract Brownian effect providing random increments. -/
class BrownianEffect (n : ℕ) (M : Type → Type*) where
  /-- Sample a Brownian increment for time step dt. -/
  sample : (dt : ℝ) → (hdt : 0 < dt) → M (BrownianIncrement n)

/-! ## Langevin Step -/

/-- One Euler–Maruyama step of full Langevin dynamics. -/
def langevinStep {M : Type → Type} [Monad M] [BrownianEffect n M] (L : LangevinParams n)
    (x : PhasePoint n) (dt : ℝ) (hdt : 0 < dt) : M (PhasePoint n) := do
  let inc ← BrownianEffect.sample dt hdt
  let q' : Config n := x.1 + dt • x.2
  let p' : Config n := x.2 + dt • (-(gradient L.V x.1) - L.γ • x.2) + L.σ • inc.value
  return (q', p')

/-! ## Fokker–Planck Equation -/

/-- Divergence of a vector field on configuration space. -/
def divergence (f : Config n → Config n) (x : Config n) : ℝ :=
  ∑ i : Fin n, (gradient (fun y => f y i) x) i

/-- A time-dependent density on phase space. -/
def Density (n : ℕ) := ℝ → PhasePoint n → ℝ

/-- Fokker–Planck operator for Langevin dynamics. -/
def FokkerPlanckRHS (L : LangevinParams n) (ρ : Density n) (t : ℝ) (x : PhasePoint n) : ℝ :=
  let q := x.1
  let p := x.2
  let grad_q_rho := gradient (fun q' => ρ t (q', p)) q
  let J_p (p' : Config n) :=
    ρ t (q, p') • gradient L.V q +
    (L.γ * ρ t (q, p')) • p' +
    (L.γ * L.kT) • gradient (fun p'' => ρ t (q, p'')) p'
  divergence J_p p - inner ℝ p grad_q_rho

/-- A density satisfies the Fokker–Planck equation. -/
def SatisfiesFokkerPlanck (L : LangevinParams n) (ρ : Density n) : Prop :=
  ∀ t x, deriv (fun s => ρ s x) t = FokkerPlanckRHS L ρ t x

/-! ## Gibbs Stationarity -/

/-- Gibbs density on phase space: ρ(q,p) ∝ exp(-(½‖p‖² + V(q))/kT). -/
def gibbsDensity (L : LangevinParams n) (Z : ℝ) (x : PhasePoint n) : ℝ :=
  Real.exp (-((1 / 2) * ‖x.2‖ ^ 2 + L.V x.1) / L.kT) / Z

/-- The Gibbs density as a stationary (time-independent) density. -/
def gibbsStationary (L : LangevinParams n) (Z : ℝ) : Density n :=
  fun _ x => gibbsDensity L Z x

/-- The Gibbs density is a stationary solution of the Fokker–Planck equation. -/
theorem gibbs_is_stationary (L : LangevinParams n) (Z : ℝ) (hZ : Z ≠ 0) :
    SatisfiesFokkerPlanck L (gibbsStationary L Z) := by
  intro t x
  simp [gibbsStationary]
  have hdiff_norm_sq :
      ∀ x0 : Config n, DifferentiableAt ℝ (fun y : Config n => ‖y‖ ^ 2) x0 := by
    intro x0
    simpa using
      (DifferentiableAt.norm_sq (𝕜 := ℝ) (f := fun y : Config n => y) (x := x0)
        differentiableAt_id)
  -- Gradient identities for the Gibbs density in q and p variables.
  have h_simp :
      ∀ i : Fin n,
        (gradient (fun q' => gibbsDensity L Z (q', x.2)) x.1) i =
            -(1 / L.kT) * (gibbsDensity L Z (x.1, x.2)) * (gradient L.V x.1) i ∧
        (gradient (fun p' => gibbsDensity L Z (x.1, p')) x.2) i =
            -(1 / L.kT) * (gibbsDensity L Z (x.1, x.2)) * (x.2 i) := by
    unfold gibbsDensity
    norm_num [gradient]
    intro i
    constructor <;> norm_num [fderiv_deriv, div_eq_mul_inv] <;> ring_nf
    · erw [fderiv_mul_const]
      ring_nf
      · erw [fderiv_exp] <;> norm_num [L.V_diff.differentiableAt]
        ring_nf
        rw [fderiv_const_mul (ha := L.V_diff.differentiableAt)]; norm_num
        ring_nf
      ·
        exact DifferentiableAt.exp
          (DifferentiableAt.add
            (DifferentiableAt.neg
              (DifferentiableAt.mul (L.V_diff.differentiableAt) (differentiableAt_const _)))
            (differentiableAt_const _))
    ·
      have hdiff_inner_p :
          DifferentiableAt ℝ
              (fun p' : Config n =>
                -(L.V x.1 * L.kT⁻¹) + ‖p'‖ ^ 2 * L.kT⁻¹ * (-1 / 2)) x.2 := by
        have hquad : DifferentiableAt ℝ (fun p' : Config n => ‖p'‖ ^ 2) x.2 :=
          hdiff_norm_sq _
        have hmul :
            DifferentiableAt ℝ
                (fun p' : Config n => ‖p'‖ ^ 2 * L.kT⁻¹ * (-1 / 2)) x.2 := by
          have hmul' :
              DifferentiableAt ℝ (fun p' : Config n => ‖p'‖ ^ 2 * L.kT⁻¹) x.2 :=
            DifferentiableAt.mul_const hquad L.kT⁻¹
          exact DifferentiableAt.mul_const hmul' (-1 / 2)
        exact (differentiableAt_const _).add hmul
      have hdiff_exp_p :
          DifferentiableAt ℝ
              (fun p' : Config n =>
                Real.exp (-(L.V x.1 * L.kT⁻¹) + ‖p'‖ ^ 2 * L.kT⁻¹ * (-1 / 2))) x.2 :=
        DifferentiableAt.exp hdiff_inner_p
      erw [fderiv_mul_const (hc := hdiff_exp_p)]
      norm_num [fderiv_deriv]
      ring_nf
      ·
        have hdiff_inner_p_comm :
            DifferentiableAt ℝ
                (fun p' : Config n =>
                  -(L.V x.1 * L.kT⁻¹) + L.kT⁻¹ * ‖p'‖ ^ 2 * (-1 / 2)) x.2 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hdiff_inner_p
        erw [fderiv_exp (hc := hdiff_inner_p_comm)]; norm_num [fderiv_deriv]
        ring_nf
        ·
          have h_grad :
              fderiv ℝ (fun y => ‖y‖ ^ 2) x.2 =
                (2 : ℝ) • (InnerProductSpace.toDual ℝ (Config n)) x.2 := by
            convert HasFDerivAt.fderiv (hasFDerivAt_id x.2 |> HasFDerivAt.norm_sq) using 1
            norm_num [two_smul]
            rfl
          have hdiff_LkT_mul_norm :
              DifferentiableAt ℝ (fun y : Config n => L.kT⁻¹ * ‖y‖ ^ 2) x.2 := by
            simpa using (DifferentiableAt.const_mul (hdiff_norm_sq _) L.kT⁻¹)
          rw [fderiv_mul_const (c := fun y : Config n => L.kT⁻¹ * ‖y‖ ^ 2)
                (d := (1 / 2)) (x := x.2) (hc := hdiff_LkT_mul_norm)]
          rw [fderiv_const_mul (a := fun y : Config n => ‖y‖ ^ 2) (b := L.kT⁻¹)
                (x := x.2) (ha := hdiff_norm_sq _)]
          simp [h_grad, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  -- Substitute the simplified gradient terms into the expressions for J_p and the divergence.
  have h_J_p :
      ∀ p' : Config n,
        (gibbsDensity L Z (x.1, p')) • gradient L.V x.1 +
            (L.γ * (gibbsDensity L Z (x.1, p'))) • p' +
            (L.γ * L.kT) • (gradient (fun p'' => gibbsDensity L Z (x.1, p'')) p') =
          (gibbsDensity L Z (x.1, p')) • (gradient L.V x.1 + L.γ • p' - L.γ • p') := by
    intro p'
    have hdiff_inner_p' :
        DifferentiableAt ℝ
            (fun p'' : Config n =>
              -(L.V x.1 * L.kT⁻¹) + ‖p''‖ ^ 2 * L.kT⁻¹ * (-1 / 2)) p' := by
      have hquad : DifferentiableAt ℝ (fun p'' : Config n => ‖p''‖ ^ 2) p' :=
        hdiff_norm_sq _
      have hmul :
          DifferentiableAt ℝ
              (fun p'' : Config n => ‖p''‖ ^ 2 * L.kT⁻¹ * (-1 / 2)) p' := by
        have hmul' :
            DifferentiableAt ℝ (fun p'' : Config n => ‖p''‖ ^ 2 * L.kT⁻¹) p' :=
          DifferentiableAt.mul_const hquad L.kT⁻¹
        exact DifferentiableAt.mul_const hmul' (-1 / 2)
      exact (differentiableAt_const _).add hmul
    have hdiff_exp_p' :
        DifferentiableAt ℝ
            (fun p'' : Config n =>
              Real.exp (-(L.V x.1 * L.kT⁻¹) + ‖p''‖ ^ 2 * L.kT⁻¹ * (-1 / 2))) p' :=
      DifferentiableAt.exp hdiff_inner_p'
    have h_grad_p' :
        gradient (fun p'' => gibbsDensity L Z (x.1, p'')) p' =
          -(1 / L.kT) • (gibbsDensity L Z (x.1, p')) • p' := by
      ext i
      simp [gradient]
      unfold gibbsDensity
      norm_num [fderiv_deriv, mul_assoc, mul_comm, mul_left_comm]
      ring_nf
      rw [fderiv_mul_const (hc := hdiff_exp_p')]
      norm_num [fderiv_deriv, mul_assoc, mul_comm, mul_left_comm]
      ring_nf
      ·
        have hdiff_inner_p'_comm :
            DifferentiableAt ℝ
                (fun p'' : Config n =>
                  -(L.kT⁻¹ * L.V x.1) + L.kT⁻¹ * ‖p''‖ ^ 2 * (-1 / 2)) p' := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hdiff_inner_p'
        rw [fderiv_exp (hc := hdiff_inner_p'_comm)];
          norm_num [fderiv_deriv, mul_assoc, mul_comm, mul_left_comm]
        ring_nf
        ·
          have hdiff_LkT_mul_norm_p' :
              DifferentiableAt ℝ (fun y : Config n => L.kT⁻¹ * ‖y‖ ^ 2) p' := by
            simpa using (DifferentiableAt.const_mul (hdiff_norm_sq _) L.kT⁻¹)
          rw [fderiv_mul_const (c := fun y : Config n => L.kT⁻¹ * ‖y‖ ^ 2)
                (d := (1 / 2)) (x := p') (hc := hdiff_LkT_mul_norm_p')]
          rw [fderiv_const_mul (a := fun y : Config n => ‖y‖ ^ 2) (b := L.kT⁻¹)
                (x := p') (ha := hdiff_norm_sq _)]
          have h_grad_p'' :
              fderiv ℝ (fun y : Config n => ‖y‖ ^ 2) p' =
                (2 : ℝ) • (InnerProductSpace.toDual ℝ (Config n)) p' := by
            convert HasFDerivAt.fderiv (hasFDerivAt_id p' |> HasFDerivAt.norm_sq) using 1
            norm_num [two_smul]
            rfl
          simp [h_grad_p'', smul_smul, mul_comm, mul_left_comm, mul_assoc]
    simp_all +decide [mul_assoc, mul_comm, mul_left_comm, smul_smul, sub_eq_add_neg]
    simp +decide [L.kT_pos.ne']
  simp_all +decide [FokkerPlanckRHS, gibbsStationary]
  unfold divergence
  simp_all +decide [mul_assoc, mul_comm]
  rw [Finset.sum_congr rfl
    (fun i _ =>
      show gradient (fun y => gradient L.V x.1 i * gibbsDensity L Z (x.1, y)) x.2 i =
          gradient L.V x.1 i * gradient (fun y => gibbsDensity L Z (x.1, y)) x.2 i from ?_)]
  simp_all +decide [mul_assoc, mul_comm]
  ring_nf
  ·
    field_simp
    simp_all +decide [mul_assoc, mul_comm, inner]
    ring_nf!
    grind
  ·
    unfold gradient
    ring_nf
    rw [fderiv_const_mul] <;> norm_num
    apply_rules [DifferentiableAt.mul, DifferentiableAt.exp, DifferentiableAt.neg,
      differentiableAt_id, differentiableAt_const]
    exact
      DifferentiableAt.add
        (DifferentiableAt.mul (differentiableAt_const _)
          (hdiff_norm_sq _))
        (L.V_diff.differentiableAt.comp _ (differentiableAt_const _))

end

end Gibbs.Hamiltonian.Stochastic
