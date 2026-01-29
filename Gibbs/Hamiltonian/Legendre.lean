import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.MeanField.ODE
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

/-
The Problem. Legendre transforms and Bregman divergences are central
to convex analysis and connect to Lyapunov functions for stability.

For a convex function f, its Legendre transform f* is defined by:
  f*(p) = sup_x { ⟨p, x⟩ - f(x) }

The Bregman divergence generalizes squared distance:
  D_f(x, y) = f(x) - f(y) - ⟨∇f(y), x - y⟩

Key properties:
- Bregman divergence ≥ 0 for convex f (by definition of convexity)
- Bregman divergence = 0 iff x = y for strictly convex f
- f** = f for closed convex f (Fenchel-Moreau theorem, proved in FenchelMoreau.lean)

Solution Structure.
1. legendre: Legendre transform definition
2. bregman: Bregman divergence definition
3. bregman_nonneg: non-negativity from convexity
4. bregman_eq_zero_iff: characterization for strict convexity
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

/-! ## Connection to Mean-Field Stability -/

/-! ### Config/Function Conversion -/

/-- Convert a configuration vector to a function on `Fin n`. -/
private noncomputable def fromConfig (x : Config n) : Fin n → ℝ :=
  -- Use the EuclideanSpace equivalence.
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)) x

/-- Convert a `Fin n → ℝ` function to a configuration vector. -/
private noncomputable def toConfig (x : Fin n → ℝ) : Config n :=
  -- Use the inverse EuclideanSpace equivalence.
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x

/-- Conversion round-trip: `fromConfig (toConfig x) = x`. -/
private theorem fromConfig_toConfig (x : Fin n → ℝ) : fromConfig (toConfig x) = x := by
  -- Apply the equivalence's `apply_symm_apply`.
  simpa [fromConfig, toConfig] using
    (ContinuousLinearEquiv.apply_symm_apply (EuclideanSpace.equiv (Fin n) ℝ) x)

/-- Conversion round-trip: `toConfig (fromConfig x) = x`. -/
private theorem toConfig_fromConfig (x : Config n) : toConfig (fromConfig x) = x := by
  -- Apply the equivalence's `symm_apply_apply`.
  simp [fromConfig, toConfig]

/-- Bregman positivity away from the equilibrium. -/
private theorem bregman_pos_of_ne {f : Config n → ℝ}
    (hconv : StrictConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    {x y : Config n} (hxy : x ≠ y) :
    0 < bregman f x y := by
  -- Combine non-negativity with strictness at equality.
  have hnonneg : 0 ≤ bregman f x y := bregman_nonneg hconv.convexOn hdiff x y
  have hzero : bregman f x y = 0 ↔ x = y := bregman_eq_zero_iff hconv hdiff x y
  have hne : bregman f x y ≠ 0 := by
    intro h
    exact hxy (hzero.mp h)
  exact lt_of_le_of_ne hnonneg (by simpa [ne_comm] using hne)

/-- Convert inequality at function level to configuration inequality. -/
private theorem toConfig_ne_of_ne {x : Fin n → ℝ} {x_eq : Config n}
    (hx : x ≠ fromConfig x_eq) : toConfig x ≠ x_eq := by
  -- Use the equivalence to transport the contradiction.
  intro hxeq
  have hx' : x = fromConfig x_eq := by
    -- Apply `fromConfig` and use the round-trip lemma.
    have := congrArg fromConfig hxeq
    simpa [fromConfig_toConfig] using this
  exact hx hx'

/-- Package Bregman divergence as a Lyapunov function for MeanField stability.
    The monotonicity along trajectories is supplied as an assumption. -/
def bregman_lyapunov_data {n : ℕ} {f : Config n → ℝ}
    (hconv : StrictConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (x_eq : Config n)
    (F : Gibbs.MeanField.DriftFunction (Fin n))
    (hcont : Continuous fun x => bregman f (toConfig x) x_eq)
    (hdec : ∀ (sol : ℝ → Fin n → ℝ),
      (∀ t ≥ 0, HasDerivAt sol (F (sol t)) t) →
      ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ →
        bregman f (toConfig (sol t₂)) x_eq ≤ bregman f (toConfig (sol t₁)) x_eq) :
    Gibbs.MeanField.LyapunovData F (fromConfig x_eq) := by
  -- Populate LyapunovData with Bregman as the candidate.
  refine
    { V := fun x => bregman f (toConfig x) x_eq
      V_cont := hcont
      V_zero := ?_
      V_pos := ?_
      V_nonneg := ?_
      V_decreasing := ?_ }
  · -- Bregman vanishes at the equilibrium point.
    simpa [fromConfig, toConfig] using (bregman_self f x_eq)
  · intro x hx
    -- Convert to Config to apply strict positivity.
    exact bregman_pos_of_ne hconv hdiff (toConfig_ne_of_ne hx)
  · intro x
    -- Nonnegativity of Bregman after converting to Config.
    exact bregman_nonneg hconv.convexOn hdiff (toConfig x) x_eq
  · intro sol hsol t₁ t₂ ht₁ ht₁₂
    exact hdec sol hsol t₁ t₂ ht₁ ht₁₂

end

end Gibbs.Hamiltonian
