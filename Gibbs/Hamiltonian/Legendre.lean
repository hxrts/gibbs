import Gibbs.Hamiltonian.ConvexHamiltonian
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Legendre Transform and Bregman Divergence

The Legendre transform f*(p) = sup_x { <p, x> - f(x) } converts between
conjugate descriptions of a convex function, exchanging slopes and intercepts.
It is the convex-analytic backbone of thermodynamic duality (energy vs entropy,
temperature vs inverse temperature).

The Bregman divergence D_f(x, y) = f(x) - f(y) - <nabla f(y), x - y> measures
how far f deviates from its tangent approximation at y. For convex f it is
nonneg, and for strictly convex f it vanishes only at x = y, making it a
natural Lyapunov function for gradient and mirror-descent dynamics.

The biconjugate identity f** = f (Fenchel-Moreau) is proved in FenchelMoreau.lean.
5. Fenchel-Moreau is proved in `Gibbs/Hamiltonian/FenchelMoreau.lean`
-/

namespace Gibbs.Hamiltonian

open scoped Classical
open InnerProductSpace
open AffineMap

noncomputable section

variable {n : ℕ}

/-! ## Legendre Transform -/

/-- The Legendre transform (convex conjugate) of f.
    f*(p) = sup_x { ⟨p, x⟩ - f(x) }

    For differentiable convex f, this is achieved at x where ∇f(x) = p,
    giving f*(p) = ⟨p, (∇f)⁻¹(p)⟩ - f((∇f)⁻¹(p)). -/
def legendre (f : Config n → ℝ) : Config n → ℝ :=
  fun p => ⨆ x, ⟪p, x⟫_ℝ - f x

/-- Alternative notation emphasizing the dual nature. -/
notation:max f "∗" => legendre f

/-- Legendre transform restricted to a domain S.
    f*_S(p) = sSup { ⟨p, x⟩ - f(x) | x ∈ S } -/
def legendreOn (f : Config n → ℝ) (S : Set (Config n)) : Config n → ℝ :=
  fun p => sSup ((fun x => ⟪p, x⟫_ℝ - f x) '' S)

/-! ## Bregman Divergence -/

/-- The Bregman divergence induced by a differentiable convex function f.
    D_f(x, y) = f(x) - f(y) - ⟨∇f(y), x - y⟩

    Geometrically: the gap between f(x) and the linear approximation at y.
    For f(x) = ½‖x‖², this is ½‖x - y‖². -/
def bregman (f : Config n → ℝ) (x y : Config n) : ℝ :=
  f x - f y - ⟪gradient f y, x - y⟫_ℝ

/-! ## Bregman Divergence Properties -/

/-! ### Line-map helpers for convexity and derivatives -/

/-- Convexity along a line segment from `y` to `x`. -/
private lemma lineMap_comp_convex (f : Config n → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (x y : Config n) :
    ConvexOn ℝ Set.univ (fun t => f (lineMap (k := ℝ) y x t)) := by
  -- Precompose with the affine line map.
  simpa using hconv.comp_affineMap (lineMap (k := ℝ) y x)

/-- Strict convexity along a line segment when endpoints differ. -/
private lemma lineMap_comp_strictConvex (f : Config n → ℝ)
    (hconv : StrictConvexOn ℝ Set.univ f) {x y : Config n} (hxy : x ≠ y) :
    StrictConvexOn ℝ Set.univ (fun t => f (lineMap (k := ℝ) y x t)) := by
  -- Use strict convexity of `f` and injectivity of `lineMap`.
  refine ⟨convex_univ, ?_⟩
  intro t _ s _ hts a b ha hb hab
  have hts' : lineMap (k := ℝ) y x t ≠ lineMap (k := ℝ) y x s := by
    -- Injectivity of the line map turns `t ≠ s` into point inequality.
    intro hls
    have hxy' : y ≠ x := by simpa [ne_comm] using hxy
    exact hts ((lineMap_injective (k := ℝ) (p₀ := y) (p₁ := x) hxy') hls)
  have h := hconv.2 (by simp) (by simp) hts' ha hb hab
  -- Rewrite the affine combination through the line map.
  have hcombo :
      a • lineMap (k := ℝ) y x t + b • lineMap (k := ℝ) y x s =
        lineMap (k := ℝ) y x (a * t + b * s) := by
    -- Use the affine-map combination rule and rewrite scalar actions.
    have hcombo' :
        lineMap (k := ℝ) y x (a • t + b • s) =
          a • lineMap (k := ℝ) y x t + b • lineMap (k := ℝ) y x s := by
      simpa using (Convex.combo_affine_apply (f := lineMap (k := ℝ) y x)
        (x := t) (y := s) hab)
    simpa [smul_eq_mul] using hcombo'.symm
  simpa [hcombo, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Derivative of `f ∘ lineMap` at `0` is the directional derivative at `y`. -/
private lemma hasDerivAt_lineMap_comp (f : Config n → ℝ)
    (hdiff : Differentiable ℝ f) (x y : Config n) :
    HasDerivAt (fun t => f (lineMap (k := ℝ) y x t)) ⟪gradient f y, x - y⟫_ℝ (0 : ℝ) := by
  -- Chain rule: differentiate `f` and the line map.
  have hgrad : HasGradientAt f (gradient f y) y :=
    (hdiff.differentiableAt).hasGradientAt
  have hfd : HasFDerivAt f (toDual ℝ (Config n) (gradient f y)) y :=
    (hasGradientAt_iff_hasFDerivAt).1 hgrad
  have hline : HasDerivAt (lineMap (k := ℝ) y x) (x - y) (0 : ℝ) := hasDerivAt_lineMap
  have hy : y = lineMap (k := ℝ) y x (0 : ℝ) := by
    -- Evaluate the line map at 0.
    simp [lineMap_apply_zero]
  have hcomp := hfd.comp_hasDerivAt_of_eq (x := 0) hline hy
  simpa [toDual_apply_apply] using hcomp

/-- Slope of `f ∘ lineMap` between `0` and `1` is `f x - f y`. -/
private lemma slope_lineMap_comp (f : Config n → ℝ) (x y : Config n) :
    slope (fun t : ℝ => f (lineMap (k := ℝ) y x t)) (0 : ℝ) (1 : ℝ) = f x - f y := by
  -- Expand the slope and use `lineMap` endpoints.
  simp [slope_def_field, lineMap_apply_zero, lineMap_apply_one]

/-- Convexity along the line gives the directional inequality. -/
private lemma deriv_le_slope_lineMap_comp (f : Config n → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f) (x y : Config n) :
    ⟪gradient f y, x - y⟫_ℝ ≤ f x - f y := by
  -- Apply `deriv_le_slope` to the 1D restriction.
  let g : ℝ → ℝ := fun t => f (lineMap (k := ℝ) y x t)
  have hconv' : ConvexOn ℝ Set.univ g := lineMap_comp_convex f hconv x y
  have hderiv : HasDerivAt g ⟪gradient f y, x - y⟫_ℝ 0 := by
    -- Reuse the chain-rule derivative for the line restriction.
    simpa [g] using hasDerivAt_lineMap_comp f hdiff x y
  have hle : deriv g 0 ≤ slope g 0 1 := by
    -- Apply the convex `deriv ≤ slope` inequality at 0 and 1.
    have hdiffg : DifferentiableAt ℝ g 0 := hderiv.differentiableAt
    exact hconv'.deriv_le_slope (by simp) (by simp) (by norm_num) hdiffg
  have hslope : slope g 0 1 = f x - f y := by
    -- Compute the slope using the line map endpoints.
    simpa [g] using slope_lineMap_comp f x y
  simpa [hderiv.deriv, hslope] using hle

/-- Strict convexity along the line gives a strict directional inequality. -/
private lemma deriv_lt_slope_lineMap_comp (f : Config n → ℝ)
    (hconv : StrictConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    {x y : Config n} (hxy : x ≠ y) :
    ⟪gradient f y, x - y⟫_ℝ < f x - f y := by
  -- Apply `deriv_lt_slope` to the strictly convex restriction.
  let g : ℝ → ℝ := fun t => f (lineMap (k := ℝ) y x t)
  have hconv' : StrictConvexOn ℝ Set.univ g := lineMap_comp_strictConvex f hconv hxy
  have hderiv : HasDerivAt g ⟪gradient f y, x - y⟫_ℝ 0 := by
    -- Reuse the chain-rule derivative for the line restriction.
    simpa [g] using hasDerivAt_lineMap_comp f hdiff x y
  have hlt : deriv g 0 < slope g 0 1 := by
    -- Apply the strict convex `deriv < slope` inequality at 0 and 1.
    have hdiffg : DifferentiableAt ℝ g 0 := hderiv.differentiableAt
    exact hconv'.deriv_lt_slope (by simp) (by simp) (by norm_num) hdiffg
  have hslope : slope g 0 1 = f x - f y := by
    -- Compute the slope using the line map endpoints.
    simpa [g] using slope_lineMap_comp f x y
  simpa [hderiv.deriv, hslope] using hlt

/-- Bregman divergence is non-negative for convex functions.

    Proof strategy: reduce to the 1D restriction along the line from `y` to `x`
    and apply the `deriv ≤ slope` inequality. -/
theorem bregman_nonneg {f : Config n → ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (x y : Config n) : 0 ≤ bregman f x y := by
  -- Convert convexity to the directional inequality.
  have hdir : ⟪gradient f y, x - y⟫_ℝ ≤ f x - f y :=
    deriv_le_slope_lineMap_comp f hconv hdiff x y
  -- Rearrange into the Bregman divergence form.
  unfold bregman
  linarith

/-- Bregman divergence at the same point is zero. -/
theorem bregman_self (f : Config n → ℝ) (x : Config n) : bregman f x x = 0 := by
  -- Substitute `x = y` into the definition.
  simp [bregman]

/-- For strictly convex f, Bregman divergence is zero iff x = y.

    The forward direction uses strict convexity: if x ≠ y, then
    f(x) > f(y) + ⟨∇f(y), x - y⟩, so D_f(x,y) > 0.

    Reference: work/aristotle/10_bregman_3.lean -/
theorem bregman_eq_zero_iff {f : Config n → ℝ}
    (hconv : StrictConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (x y : Config n) : bregman f x y = 0 ↔ x = y := by
  -- Use strict convexity to rule out zero divergence at distinct points.
  constructor
  · intro hxy
    by_contra hne
    have hpos : 0 < bregman f x y := by
      -- Strict directional inequality gives strict Bregman positivity.
      have hdir := deriv_lt_slope_lineMap_comp f hconv hdiff hne
      unfold bregman
      linarith
    exact (ne_of_gt hpos) hxy
  · intro hxy
    simp [hxy, bregman_self]

/-! ## Bregman Divergence for Quadratic Functions -/

/-- Bregman divergence of ½‖·‖² is ½‖x - y‖².
    This shows Bregman generalizes squared Euclidean distance.

    Reference: work/aristotle/10_bregman_2.lean -/
theorem bregman_quadratic (x y : Config n) :
    bregman (quadraticPotential n) x y = (1/2) * ‖x - y‖^2 := by
  -- Compute the gradient of the quadratic potential and simplify.
  have hgrad : gradient (quadraticPotential n) y = y := by
    -- Compare inner products using the Riesz representation.
    apply ext_inner_right ℝ
    intro z
    have hdiff : DifferentiableAt ℝ (fun q : Config n => ‖q‖ ^ 2) y :=
      (differentiableAt_id).norm_sq ℝ
    have hfd : fderiv ℝ (quadraticPotential n) y = innerSL ℝ y := by
      -- Compare the linear maps by evaluating on an arbitrary vector.
      ext z
      have hfd' :
          fderiv ℝ (quadraticPotential n) y = (1 / 2 : ℝ) • (2 • innerSL ℝ y) := by
        -- Unfold the potential and apply the constant-multiple derivative.
        change fderiv ℝ (fun q : Config n => (1 / 2 : ℝ) * ‖q‖ ^ 2) y =
          (1 / 2 : ℝ) • (2 • innerSL ℝ y)
        simpa [fderiv_norm_sq_apply, smul_smul] using
          (fderiv_const_mul (x := y) hdiff (1 / 2 : ℝ))
      have hcoeff : (1 / 2 : ℝ) * 2 = 1 := by norm_num
      -- Apply the linear maps to `z` and simplify the scalar factor.
      have hfdz := congrArg (fun L => L z) hfd'
      simpa [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_smul, hcoeff] using hfdz
    simp [gradient, hfd, toDual_symm_apply, innerSL_apply_apply]
  -- Reduce to the norm-square identity.
  have hnorm : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 :=
    norm_sub_sq_real x y
  -- Expand the Bregman divergence and use `hnorm`.
  simp [bregman, quadraticPotential, hgrad, inner_sub_right, real_inner_comm, hnorm] ; ring

/-! ## Connection to Lyapunov Functions -/

/-- Bregman divergence from equilibrium serves as a Lyapunov function.
    For a system with equilibrium x*, V(x) = D_f(x, x*) is:
    - Non-negative (by convexity)
    - Zero only at x* (by strict convexity)
    - Decreasing along trajectories (requires drift analysis)

    This theorem just states the first two properties. -/
theorem bregman_lyapunov_candidate {f : Config n → ℝ}
    (hconv : StrictConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (x_eq : Config n) :
    (∀ x, 0 ≤ bregman f x x_eq) ∧
    (∀ x, bregman f x x_eq = 0 ↔ x = x_eq) := by
  -- Combine non-negativity and strictness into a Lyapunov-style pair.
  constructor
  · intro x
    exact bregman_nonneg hconv.convexOn hdiff x x_eq
  · intro x
    exact bregman_eq_zero_iff hconv hdiff x x_eq

end

end Gibbs.Hamiltonian
