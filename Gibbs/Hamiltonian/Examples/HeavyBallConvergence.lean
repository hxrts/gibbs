import Gibbs.Hamiltonian.Examples.GradientDescent
import Mathlib

/-!
Heavy-ball convergence scaffolding: Lyapunov derivative + exponential comparison.

This module computes the derivative of the standard heavy-ball Lyapunov
functional along solutions and provides a generic exponential decay lemma
once a differential inequality is established.
-/
namespace Gibbs.Hamiltonian.Examples

noncomputable section

variable {n : ℕ}

/-! ## Heavy-ball dynamics -/

/-- Heavy-ball / momentum dynamics: q̈ + γ q̇ + ∇f(q) = 0. -/
structure HeavyBallDynamics (n : ℕ) where
  f : Config n → ℝ
  γ : ℝ
  f_diff : Differentiable ℝ f
  γ_pos : 0 < γ

/-- Phase space state (position, velocity). -/
abbrev HeavyBallState (n : ℕ) := PhasePoint n

/-- A trajectory solves heavy-ball dynamics. -/
def SolvesHeavyBall {n : ℕ} (dyn : HeavyBallDynamics n) (sol : ℝ → HeavyBallState n) : Prop :=
  ∀ t, HasDerivAt (fun s => (sol s).1) (sol t).2 t ∧
       HasDerivAt (fun s => (sol s).2)
         (-gradient dyn.f (sol t).1 - dyn.γ • (sol t).2) t

/-! ## Lyapunov derivative -/

/-- Derivative of the heavy-ball Lyapunov functional along solutions (raw form). -/
lemma heavyBallLyapunov_hasDeriv (f : Config n → ℝ) (x_star : Config n) (ε : ℝ)
    (dyn : HeavyBallDynamics n) (hdyn : dyn.f = f)
    (sol : ℝ → HeavyBallState n) (hsol : SolvesHeavyBall dyn sol) (t : ℝ) :
    HasDerivAt (fun s => heavyBallLyapunov (n := n) f x_star ε (sol s))
      (inner (𝕜 := ℝ) (gradient f (sol t).1) (sol t).2 +
        inner (𝕜 := ℝ) (sol t).2 (-gradient f (sol t).1 - dyn.γ • (sol t).2) +
        ε * (inner (𝕜 := ℝ) (sol t).2 (sol t).2 +
          inner (𝕜 := ℝ) ((sol t).1 - x_star)
            (-gradient f (sol t).1 - dyn.γ • (sol t).2))) t := by
  -- Derivative of the potential term.
  have hq : HasDerivAt (fun s => (sol s).1) (sol t).2 t := (hsol t).1
  have hp : HasDerivAt (fun s => (sol s).2)
      (-gradient f (sol t).1 - dyn.γ • (sol t).2) t := by
    simpa [hdyn] using (hsol t).2
  have hf_comp : HasDerivAt (fun s => f (sol s).1)
      (fderiv ℝ f (sol t).1 (sol t).2) t := by
    have hf' : HasFDerivAt f (fderiv ℝ f (sol t).1) (sol t).1 := by
      simpa [hdyn] using (dyn.f_diff.differentiableAt.hasFDerivAt)
    have hq' := hq.hasFDerivAt
    have hcomp := HasFDerivAt.comp t hf' hq'
    -- Convert to a scalar derivative and simplify.
    have hcomp' := (HasFDerivAt.hasDerivAt hcomp)
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul, mul_comm, mul_left_comm, mul_assoc] using hcomp'
  have hf : HasDerivAt (fun s => f (sol s).1)
      (inner (𝕜 := ℝ) (gradient f (sol t).1) (sol t).2) t := by
    have hto :
        (InnerProductSpace.toDual ℝ (Config n)) (gradient f (sol t).1) =
          fderiv ℝ f (sol t).1 := by
      simp [gradient]
    have hto' := congrArg (fun g => g (sol t).2) hto
    have hto'' : inner (𝕜 := ℝ) (gradient f (sol t).1) (sol t).2 =
        fderiv ℝ f (sol t).1 (sol t).2 := by
      simpa [InnerProductSpace.toDual_apply_apply] using hto'
    simpa [hto''] using hf_comp
  have h_pot : HasDerivAt (fun s => f (sol s).1 - f x_star)
      (inner (𝕜 := ℝ) (gradient f (sol t).1) (sol t).2) t := by
    simpa using (hf.sub_const (f x_star))
  -- Derivative of the kinetic term.
  have h_norm : HasDerivAt (fun s => ‖(sol s).2‖ ^ 2)
      (2 * inner (𝕜 := ℝ) (sol t).2
        (-gradient f (sol t).1 - dyn.γ • (sol t).2)) t := by
    simpa using (HasDerivAt.norm_sq hp)
  have h_kin : HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(sol s).2‖ ^ 2)
      (inner (𝕜 := ℝ) (sol t).2
        (-gradient f (sol t).1 - dyn.γ • (sol t).2)) t := by
    have h := h_norm.const_mul (1 / 2 : ℝ)
    -- Simplify the scalar factor.
    convert h using 1
    ring
  -- Derivative of the coupling term.
  have h_inner : HasDerivAt
      (fun s => inner (𝕜 := ℝ) ((sol s).1 - x_star) ((sol s).2))
      (inner (𝕜 := ℝ) (sol t).2 (sol t).2 +
        inner (𝕜 := ℝ) ((sol t).1 - x_star)
          (-gradient f (sol t).1 - dyn.γ • (sol t).2)) t := by
    have hq' : HasDerivAt (fun s => (sol s).1 - x_star) (sol t).2 t :=
      (hsol t).1.sub_const x_star
    have := HasDerivAt.inner ℝ hq' hp
    -- Reorder terms.
    simpa [add_comm, add_left_comm, add_assoc] using this
  have h_coupling : HasDerivAt
      (fun s => ε * inner (𝕜 := ℝ) ((sol s).1 - x_star) ((sol s).2))
      (ε * (inner (𝕜 := ℝ) (sol t).2 (sol t).2 +
        inner (𝕜 := ℝ) ((sol t).1 - x_star)
          (-gradient f (sol t).1 - dyn.γ • (sol t).2))) t :=
    h_inner.const_mul ε
  -- Combine the pieces (raw form).
  exact HasDerivAt.add (HasDerivAt.add h_pot h_kin) h_coupling

/-- Simplified derivative formula (using the raw form). -/
lemma heavyBallLyapunov_deriv (f : Config n → ℝ) (x_star : Config n) (ε : ℝ)
    (dyn : HeavyBallDynamics n) (hdyn : dyn.f = f)
    (sol : ℝ → HeavyBallState n) (hsol : SolvesHeavyBall dyn sol) (t : ℝ) :
    deriv (fun s => heavyBallLyapunov (n := n) f x_star ε (sol s)) t =
      inner (𝕜 := ℝ) (gradient f (sol t).1) (sol t).2 +
        inner (𝕜 := ℝ) (sol t).2 (-gradient f (sol t).1 - dyn.γ • (sol t).2) +
        ε * (inner (𝕜 := ℝ) (sol t).2 (sol t).2 +
          inner (𝕜 := ℝ) ((sol t).1 - x_star)
            (-gradient f (sol t).1 - dyn.γ • (sol t).2)) := by
  simpa using (heavyBallLyapunov_hasDeriv (n := n) f x_star ε dyn hdyn sol hsol t).deriv

/-! ## Exponential comparison -/

/-- Exponential decay from a differential inequality. -/
lemma exp_decay_of_deriv_le (V : ℝ → ℝ) (rate : ℝ)
    (hV : ∀ t, HasDerivAt V (deriv V t) t)
    (hVle : ∀ t, deriv V t ≤ -rate * V t) :
    ∀ t ≥ 0, V t ≤ V 0 * Real.exp (-rate * t) := by
  intro t ht
  let g : ℝ → ℝ := fun s => V s * Real.exp (rate * s)
  have hderiv_g : ∀ s, HasDerivAt g
      (deriv V s * Real.exp (rate * s) + V s * Real.exp (rate * s) * rate) s := by
    intro s
    have hlin : HasDerivAt (fun r => rate * r) rate s := by
      simpa [mul_comm] using (HasDerivAt.const_mul rate (hasDerivAt_id s))
    have hexp : HasDerivAt (fun r => Real.exp (rate * r))
        (Real.exp (rate * s) * rate) s :=
      HasDerivAt.exp hlin
    have hmul := HasDerivAt.mul (hV s) hexp
    -- `HasDerivAt.mul` gives `(deriv V s) * exp + V s * (exp * rate)`.
    simpa [g, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hmul
  have hderiv_g_nonpos : ∀ s, deriv g s ≤ 0 := by
    intro s
    have hderiv := (hderiv_g s).deriv
    have hle : Real.exp (rate * s) * (deriv V s + rate * V s) ≤ 0 := by
      have hpos : 0 < Real.exp (rate * s) := Real.exp_pos _
      have h' : deriv V s + rate * V s ≤ 0 := by
        nlinarith [hVle s]
      nlinarith [hpos, h']
    -- Match the raw derivative form.
    have h_eq :
        deriv V s * Real.exp (rate * s) + V s * Real.exp (rate * s) * rate =
          Real.exp (rate * s) * (deriv V s + rate * V s) := by
      ring
    simpa [hderiv, h_eq] using hle
  have hdiff : Differentiable ℝ g := fun s => (hderiv_g s).differentiableAt
  have hanti : Antitone g := antitone_of_deriv_nonpos hdiff hderiv_g_nonpos
  have hle_g : g t ≤ g 0 := by
    have ht' : 0 ≤ t := ht
    exact hanti ht'
  have hgt : V t * Real.exp (rate * t) ≤ V 0 * Real.exp (rate * 0) := by
    simpa [g] using hle_g
  have hmul := mul_le_mul_of_nonneg_right hgt (by
    exact le_of_lt (Real.exp_pos (-rate * t)))
  have hexp : Real.exp (rate * t) * Real.exp (-(rate * t)) = 1 := by
    calc
      Real.exp (rate * t) * Real.exp (-(rate * t)) =
          Real.exp (rate * t + -(rate * t)) := by
            simpa [mul_comm] using (Real.exp_add (rate * t) (-(rate * t))).symm
      _ = 1 := by simp
  have h0 : Real.exp (rate * 0) = 1 := by simp
  simpa [mul_comm, mul_left_comm, mul_assoc, h0, hexp] using hmul

/-- Exponential decay for the heavy-ball Lyapunov functional, assuming a
    pointwise differential inequality. -/
theorem heavyBallLyapunov_decay (f : Config n → ℝ) (x_star : Config n) (ε rate : ℝ)
    (dyn : HeavyBallDynamics n) (hdyn : dyn.f = f)
    (sol : ℝ → HeavyBallState n) (hsol : SolvesHeavyBall dyn sol)
    (hdecay : ∀ t,
      deriv (fun s => heavyBallLyapunov (n := n) f x_star ε (sol s)) t
        ≤ -rate * heavyBallLyapunov (n := n) f x_star ε (sol t)) :
    ∀ t ≥ 0,
      heavyBallLyapunov (n := n) f x_star ε (sol t) ≤
        heavyBallLyapunov (n := n) f x_star ε (sol 0) * Real.exp (-rate * t) := by
  intro t ht
  have hV : ∀ s, HasDerivAt
      (fun r => heavyBallLyapunov (n := n) f x_star ε (sol r))
      (deriv (fun r => heavyBallLyapunov (n := n) f x_star ε (sol r)) s) s := by
    intro s
    -- use the explicit derivative formula
    have h := heavyBallLyapunov_hasDeriv (n := n) (f := f) (x_star := x_star) (ε := ε)
      (dyn := dyn) hdyn sol hsol s
    have hderiv : deriv (fun r => heavyBallLyapunov (n := n) f x_star ε (sol r)) s =
        inner (𝕜 := ℝ) (gradient f (sol s).1) (sol s).2 +
          inner (𝕜 := ℝ) (sol s).2 (-gradient f (sol s).1 - dyn.γ • (sol s).2) +
          ε * (inner (𝕜 := ℝ) (sol s).2 (sol s).2 +
            inner (𝕜 := ℝ) ((sol s).1 - x_star)
              (-gradient f (sol s).1 - dyn.γ • (sol s).2)) := h.deriv
    simpa [hderiv] using h
  exact exp_decay_of_deriv_le
    (V := fun r => heavyBallLyapunov (n := n) f x_star ε (sol r))
    (rate := rate) hV hdecay t ht

end

end Gibbs.Hamiltonian.Examples
