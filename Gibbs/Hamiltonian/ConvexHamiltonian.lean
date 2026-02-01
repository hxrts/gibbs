import Gibbs.Hamiltonian.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

/-!
# Convex Hamiltonian Structure

A separable Hamiltonian H(q,p) = T(p) + V(q) with convex kinetic and potential
energy. Convexity of T and V ensures well-behaved dynamics: Lipschitz drift
fields, energy as a Lyapunov candidate under damping, and unique equilibria
when V is strictly convex.

This file defines `ConvexHamiltonian` and `StrictlyConvexHamiltonian`, derives
velocity (nabla_p T) and force (-nabla_q V), and provides quadratic constructors
for the standard harmonic oscillator.
-/

namespace Gibbs.Hamiltonian

open scoped Classical
open InnerProductSpace

noncomputable section

/-! ## Separable Convex Hamiltonian -/

/-- A separable convex Hamiltonian H(q,p) = T(p) + V(q).

    Separability means kinetic energy T depends only on momentum,
    and potential energy V depends only on position. This is the
    standard form for mechanical systems.

    Convexity of T and V ensures:
    - Gradients are well-defined (by differentiability)
    - The drift function is Lipschitz (enabling ODE existence)
    - With damping, H becomes a Lyapunov function -/
structure ConvexHamiltonian (n : ℕ) where
  /-- Kinetic energy: function of momentum only -/
  T : Config n → ℝ
  /-- Potential energy: function of position only -/
  V : Config n → ℝ
  /-- Kinetic energy is convex -/
  T_convex : ConvexOn ℝ Set.univ T
  /-- Potential energy is convex -/
  V_convex : ConvexOn ℝ Set.univ V
  /-- Kinetic energy is differentiable -/
  T_diff : Differentiable ℝ T
  /-- Potential energy is differentiable -/
  V_diff : Differentiable ℝ V

namespace ConvexHamiltonian

variable {n : ℕ}

/-! ## Energy -/

/-- Total energy H = T + V at a phase point. -/
def energy (H : ConvexHamiltonian n) (x : PhasePoint n) : ℝ :=
  H.T x.p + H.V x.q

/-- Energy is the sum of kinetic and potential. -/
theorem energy_eq_sum (H : ConvexHamiltonian n) (x : PhasePoint n) :
    H.energy x = H.T x.p + H.V x.q := rfl

/-! ## Velocity and Force -/

/-- Velocity: v = ∇_p T(p).
    This is the rate of change of position in Hamiltonian dynamics. -/
def velocity (H : ConvexHamiltonian n) : Config n → Config n :=
  gradient H.T

/-- Force: F = -∇_q V(q).
    This is the negative gradient of potential energy. -/
def force (H : ConvexHamiltonian n) : Config n → Config n :=
  fun q => -gradient H.V q

/-- Force is the negation of the potential gradient. -/
theorem force_eq_neg_grad (H : ConvexHamiltonian n) (q : Config n) :
    H.force q = -gradient H.V q := rfl

end ConvexHamiltonian

/-! ## Strictly Convex Hamiltonian -/

/-- A Hamiltonian with strictly convex potential energy.
    Strict convexity of V implies a unique global minimum,
    which becomes the unique stable equilibrium with damping. -/
structure StrictlyConvexHamiltonian (n : ℕ) extends ConvexHamiltonian n where
  /-- Potential energy is strictly convex -/
  V_strictConvex : StrictConvexOn ℝ Set.univ V

namespace StrictlyConvexHamiltonian

variable {n : ℕ}

/-- Strictly convex implies convex. -/
theorem V_convex' (H : StrictlyConvexHamiltonian n) : ConvexOn ℝ Set.univ H.V :=
  H.V_strictConvex.convexOn

end StrictlyConvexHamiltonian

/-! ## Quadratic Hamiltonians -/

/-- Standard quadratic kinetic energy: T(p) = ½‖p‖².
    This corresponds to unit mass in all directions. -/
def quadraticKinetic (n : ℕ) : Config n → ℝ :=
  fun p => (1/2) * ‖p‖^2

/-- Quadratic kinetic energy is convex.
    Proof: ‖·‖² is convex (composition of convex norm with convex square),
    and scaling by positive constant preserves convexity. -/
theorem quadraticKinetic_convex (n : ℕ) : ConvexOn ℝ Set.univ (quadraticKinetic n) := by
  unfold quadraticKinetic
  -- (1/2) * ‖p‖^2 is convex because:
  -- 1. ‖·‖ is convex (convexOn_univ_norm)
  -- 2. ‖·‖^2 is convex (ConvexOn.pow with non-negativity of norm)
  -- 3. Scaling by positive constant preserves convexity
  have h1 : ConvexOn ℝ Set.univ (fun p : Config n => ‖p‖) := convexOn_univ_norm
  have h2 : ConvexOn ℝ Set.univ (fun p : Config n => ‖p‖^2) := by
    have := h1.pow (fun _ _ => norm_nonneg _) 2
    convert this using 1
  exact h2.smul (by norm_num : (0 : ℝ) ≤ 1/2)

/-- Quadratic kinetic energy is differentiable.
    Follows from smoothness of the squared norm in inner product spaces. -/
theorem quadraticKinetic_diff (n : ℕ) : Differentiable ℝ (quadraticKinetic n) := by
  unfold quadraticKinetic
  -- ‖·‖² is smooth in an inner product space, use Differentiable.norm_sq with id
  apply Differentiable.const_mul
  exact differentiable_id.norm_sq ℝ

/-- Gradient of quadratic kinetic energy is the identity map. -/
theorem quadraticKinetic_grad (n : ℕ) (p : Config n) :
    gradient (quadraticKinetic n) p = p := by
  -- Compare inner products using the Riesz representation.
  apply ext_inner_right ℝ
  intro z
  have hdiff : DifferentiableAt ℝ (fun q : Config n => ‖q‖ ^ 2) p :=
    (differentiableAt_id).norm_sq ℝ
  have hfd : fderiv ℝ (quadraticKinetic n) p = innerSL ℝ p := by
    -- Evaluate the derivative on an arbitrary vector `z`.
    ext z
    have hfd' :
        fderiv ℝ (quadraticKinetic n) p = (1 / 2 : ℝ) • (2 • innerSL ℝ p) := by
      -- Unfold the quadratic and use `fderiv_const_mul`.
      change fderiv ℝ (fun q : Config n => (1 / 2 : ℝ) * ‖q‖ ^ 2) p =
        (1 / 2 : ℝ) • (2 • innerSL ℝ p)
      simpa [fderiv_norm_sq_apply, smul_smul] using
        (fderiv_const_mul (x := p) hdiff (1 / 2 : ℝ))
    have hcoeff : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    have hfdz := congrArg (fun L => L z) hfd'
    simpa [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_smul, hcoeff] using hfdz
  simp [gradient, hfd, toDual_symm_apply, innerSL_apply_apply]

/-- Quadratic potential energy: V(q) = ½‖q‖².
    This is the harmonic potential with unit spring constant. -/
def quadraticPotential (n : ℕ) : Config n → ℝ :=
  fun q => (1/2) * ‖q‖^2

/-- Quadratic potential is convex.
    Same proof as quadraticKinetic_convex. -/
theorem quadraticPotential_convex (n : ℕ) : ConvexOn ℝ Set.univ (quadraticPotential n) := by
  -- Reuse convexity of the norm and of `x ↦ x^2`, then scale.
  unfold quadraticPotential
  have h1 : ConvexOn ℝ Set.univ (fun q : Config n => ‖q‖) := convexOn_univ_norm
  have h2 : ConvexOn ℝ Set.univ (fun q : Config n => ‖q‖^2) := by
    have := h1.pow (fun _ _ => norm_nonneg _) 2
    convert this using 1
  exact h2.smul (by norm_num : (0 : ℝ) ≤ 1/2)

/-- Helper: squared norm of a convex combination with `a + b = 1`. -/
private lemma norm_sq_combo (x y : Config n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 =
      a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  -- Expand with `norm_add_sq_real`, then eliminate `a^2`/`b^2` using `a + b = 1`.
  have hsum :
      ‖a • x + b • y‖ ^ 2 =
        a ^ 2 * ‖x‖ ^ 2 + 2 * a * b * ⟪x, y⟫_ℝ + b ^ 2 * ‖y‖ ^ 2 := by
    -- Use bilinearity of the inner product and `‖a • x‖ = |a| ‖x‖`.
    calc
      ‖a • x + b • y‖ ^ 2 =
          ‖a • x‖ ^ 2 + 2 * ⟪a • x, b • y⟫_ℝ + ‖b • y‖ ^ 2 := by
        simp [norm_add_sq_real]
      _ = a ^ 2 * ‖x‖ ^ 2 + 2 * a * b * ⟪x, y⟫_ℝ + b ^ 2 * ‖y‖ ^ 2 := by
        simp [norm_smul, inner_smul_left, inner_smul_right, pow_two, abs_of_pos ha,
          abs_of_pos hb, mul_comm, mul_left_comm, mul_assoc]
  have hsub : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 :=
    norm_sub_sq_real x y
  -- Finish by rewriting `a^2`/`b^2` via `hab` and using `hsub`.
  calc
    ‖a • x + b • y‖ ^ 2
        = a ^ 2 * ‖x‖ ^ 2 + 2 * a * b * ⟪x, y⟫_ℝ + b ^ 2 * ‖y‖ ^ 2 := hsum
    _ = a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
      -- Pure algebra after substituting `a + b = 1`.
      have hb' : b = 1 - a := by linarith [hab]
      simp [hsub, hb'] ; ring

/-- Quadratic potential is strictly convex (when n > 0).
    Proof uses the norm-square identity
    `‖x - y‖² = ‖x‖² - 2⟨x,y⟩ + ‖y‖²` and the fact `x ≠ y → ‖x - y‖² > 0`. -/
theorem quadraticPotential_strictConvex (n : ℕ) [NeZero n] :
    StrictConvexOn ℝ Set.univ (quadraticPotential n) := by
  -- Use the norm-square identity to get a strict inequality.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hpos : 0 < a * b * ‖x - y‖ ^ 2 := by
    -- Each factor is positive when `x ≠ y`.
    have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hnorm : 0 < ‖x - y‖ ^ 2 := by
      exact pow_pos (norm_pos_iff.mpr hxy') 2
    exact mul_pos (mul_pos ha hb) hnorm
  have hcombo := norm_sq_combo (n := n) x y ha hb hab
  -- Rewrite the strict convexity inequality with the combo identity.
  simp [quadraticPotential, smul_eq_mul] at hcombo ⊢
  nlinarith [hcombo, hpos]

/-- Quadratic potential is differentiable. -/
theorem quadraticPotential_diff (n : ℕ) : Differentiable ℝ (quadraticPotential n) := by
  -- Smoothness of the squared norm gives differentiability.
  unfold quadraticPotential
  apply Differentiable.const_mul
  exact differentiable_id.norm_sq ℝ

/-! ## Harmonic Oscillator -/

/-- The harmonic oscillator Hamiltonian: H = ½‖p‖² + ½‖q‖².
    This is the canonical example of a convex Hamiltonian. -/
def harmonicOscillator (n : ℕ) : ConvexHamiltonian n where
  T := quadraticKinetic n
  V := quadraticPotential n
  T_convex := quadraticKinetic_convex n
  V_convex := quadraticPotential_convex n
  T_diff := quadraticKinetic_diff n
  V_diff := quadraticPotential_diff n

/-- Harmonic oscillator as strictly convex (when n > 0). -/
def harmonicOscillatorStrict (n : ℕ) [NeZero n] : StrictlyConvexHamiltonian n where
  toConvexHamiltonian := harmonicOscillator n
  V_strictConvex := quadraticPotential_strictConvex n

namespace HarmonicOscillator

variable {n : ℕ}

/-- Harmonic oscillator energy: H = ½‖p‖² + ½‖q‖². -/
theorem energy_eq (x : PhasePoint n) :
    (harmonicOscillator n).energy x = (1/2) * ‖x.p‖^2 + (1/2) * ‖x.q‖^2 := rfl

/-- Harmonic oscillator has minimum energy 0 at the origin. -/
theorem energy_nonneg (x : PhasePoint n) : 0 ≤ (harmonicOscillator n).energy x := by
  simp only [energy_eq]
  positivity

/-- Energy is zero iff at the origin. -/
theorem energy_eq_zero_iff (x : PhasePoint n) :
    (harmonicOscillator n).energy x = 0 ↔ x = PhasePoint.zero := by
  simp only [energy_eq, PhasePoint.zero]
  constructor
  · intro h
    -- Sum of non-negative terms is 0 iff each is 0
    have hp : (1/2) * ‖x.p‖^2 = 0 := by
      have h1 : 0 ≤ (1/2 : ℝ) * ‖x.p‖^2 := by positivity
      have h2 : 0 ≤ (1/2 : ℝ) * ‖x.q‖^2 := by positivity
      linarith [add_eq_zero_iff_of_nonneg h1 h2 |>.mp h]
    have hq : (1/2) * ‖x.q‖^2 = 0 := by
      have h1 : 0 ≤ (1/2 : ℝ) * ‖x.p‖^2 := by positivity
      have h2 : 0 ≤ (1/2 : ℝ) * ‖x.q‖^2 := by positivity
      linarith [add_eq_zero_iff_of_nonneg h1 h2 |>.mp h]
    simp only [mul_eq_zero, one_div, inv_eq_zero, OfNat.ofNat_ne_zero, sq_eq_zero_iff,
      norm_eq_zero, false_or] at hp hq
    ext <;> simp [*]
  · intro h
    simp [h]

end HarmonicOscillator

/-! ## Strong Convexity -/

/-- Strong convexity with parameter m. -/
structure StronglyConvex (f : Config n → ℝ) (m : ℝ) : Prop where
  /-- Strong convexity parameter is positive. -/
  m_pos : 0 < m
  /-- Quadratic lower bound with gradient linearization. -/
  lower_bound :
    ∀ x y, f y ≥ f x + inner (𝕜 := ℝ) (gradient f x) (y - x) +
      (m / 2) * ‖y - x‖ ^ 2

/-- Lipschitz gradient with constant L. -/
structure LipschitzGradient (f : Config n → ℝ) (L : ℝ) : Prop where
  /-- Lipschitz constant is positive. -/
  L_pos : 0 < L
  /-- Gradient is L-Lipschitz. -/
  lipschitz : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- Condition number kappa = L/m. -/
def conditionNumber (m L : ℝ) : ℝ := L / m

/-- Optimal damping used in heavy-ball rates. -/
def optimalDamping (m : ℝ) : ℝ := 2 * Real.sqrt m

end

end Gibbs.Hamiltonian
