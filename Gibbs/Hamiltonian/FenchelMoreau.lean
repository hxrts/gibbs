import Gibbs.Hamiltonian.Legendre
import Mathlib

/-!
# Fenchel-Moreau Duality

The Fenchel-Moreau theorem states that a convex lower-semicontinuous function
equals its biconjugate: f** = f. The Legendre-Fenchel transform replaces f by
the supremum of its affine minorants, so applying it twice recovers f exactly
when no affine minorant is missing (i.e., f is closed and convex).

The proof splits into two directions. The inequality f** le f follows from
Fenchel-Young (each affine term is bounded by the supremum). The reverse
f le f** uses Hahn-Banach separation to produce a supporting hyperplane at
every point, which enters the supremum defining f**.
-/

namespace Gibbs.Hamiltonian

open scoped Classical
open InnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ## Finiteness Conditions -/

/-- Conjugate finiteness: the supremum defining f*(p) is bounded for all p. -/
abbrev HasFiniteConjugate (f : Config n → ℝ) : Prop :=
  ∀ p, BddAbove (Set.range (fun x => ⟪p, x⟫_ℝ - f x))

/-- Biconjugate finiteness: the supremum defining f**(x) is bounded for all x. -/
abbrev HasFiniteBiconjugate (f : Config n → ℝ) : Prop :=
  ∀ x, BddAbove (Set.range (fun p => ⟪x, p⟫_ℝ - legendre f p))

/-! ## Fenchel-Young Inequality and f** ≤ f -/

/-- Fenchel-Young inequality: ⟨p, x⟩ ≤ f(x) + f*(p). -/
lemma fenchel_young (f : Config n → ℝ) (hf : HasFiniteConjugate f) (x p : Config n) :
    ⟪p, x⟫_ℝ - f x ≤ legendre f p := by
  -- The supremum defining the conjugate bounds each affine term.
  exact le_ciSup (hf p) x

/-- First direction: f**(x) ≤ f(x) for all x. -/
lemma biconjugate_le (f : Config n → ℝ) (hf : HasFiniteConjugate f) (x : Config n) :
    legendre (legendre f) x ≤ f x := by
  -- Apply Fenchel-Young inside the biconjugate supremum.
  refine ciSup_le ?_
  intro p
  have h := fenchel_young f hf x p
  have hcomm : ⟪x, p⟫_ℝ = ⟪p, x⟫_ℝ := by
    -- Symmetry of the real inner product.
    simpa using (real_inner_comm p x)
  linarith [h, hcomm]

/-! ## Subgradient Characterization -/

/-- A subgradient at x is a supporting hyperplane for f. -/
def IsSubgradientAt (f : Config n → ℝ) (x p : Config n) : Prop :=
  ∀ y, f y ≥ f x + ⟪p, y - x⟫_ℝ

/-- Subgradient existence predicate. -/
def SubgradientExists (f : Config n → ℝ) : Prop :=
  ∀ x, ∃ p, IsSubgradientAt f x p

/-- A subgradient bounds the conjugate at the supporting slope. -/
lemma subgradient_conjugate_bound (f : Config n → ℝ) {x p : Config n}
    (hsub : IsSubgradientAt f x p) :
    legendre f p ≤ ⟪p, x⟫_ℝ - f x := by
  -- Use the subgradient inequality to bound each affine term.
  refine ciSup_le ?_
  intro y
  have hsub' := hsub y
  have hlin : ⟪p, y⟫_ℝ - ⟪p, y - x⟫_ℝ = ⟪p, x⟫_ℝ := by
    -- Expand the inner product along the difference.
    simp only [inner_sub_right]
    ring
  linarith [hsub', hlin]

/-- A subgradient provides a lower bound on the biconjugate at that point. -/
lemma subgradient_le_biconjugate (f : Config n → ℝ) (hf' : HasFiniteBiconjugate f)
    {x p : Config n} (hsub : IsSubgradientAt f x p) :
    f x ≤ legendre (legendre f) x := by
  -- Insert the supporting slope into the biconjugate supremum.
  have hconj : legendre f p ≤ ⟪p, x⟫_ℝ - f x := subgradient_conjugate_bound f hsub
  have hsup : f x ≤ ⟪x, p⟫_ℝ - legendre f p := by
    -- Swap the inner product to align terms.
    have hcomm : ⟪x, p⟫_ℝ = ⟪p, x⟫_ℝ := by
      -- Symmetry of the real inner product.
      simpa using (real_inner_comm p x)
    linarith [hconj, hcomm]
  exact le_ciSup_of_le (hf' x) p hsup

/-- If every point admits a subgradient, then f ≤ f**. -/
lemma le_biconjugate_of_subgradient (f : Config n → ℝ) (hf' : HasFiniteBiconjugate f)
    (hsub : ∀ x, ∃ p, IsSubgradientAt f x p) :
    ∀ x, f x ≤ legendre (legendre f) x := by
  -- Pick a subgradient at the point and apply the previous lemma.
  intro x
  obtain ⟨p, hp⟩ := hsub x
  exact subgradient_le_biconjugate f hf' hp

/-- Fenchel-Moreau via explicit subgradients. -/
theorem fenchel_moreau_of_subgradients (f : Config n → ℝ)
    (hf : HasFiniteConjugate f) (hf' : HasFiniteBiconjugate f)
    (hsub : ∀ x, ∃ p, IsSubgradientAt f x p) :
    legendre (legendre f) = f := by
  -- Combine the two inequalities pointwise.
  funext x
  apply le_antisymm
  · exact biconjugate_le f hf x
  · exact le_biconjugate_of_subgradient f hf' hsub x

/-! ## Epigraph and Separation -/

/-- Epigraph of f as a subset of Config n × ℝ. -/
abbrev epigraph (f : Config n → ℝ) : Set (Config n × ℝ) :=
  { z | f z.1 ≤ z.2 }

/-- Epigraph is convex for convex functions. -/
lemma epigraph_convex (f : Config n → ℝ) (hconv : ConvexOn ℝ Set.univ f) :
    Convex ℝ (epigraph f) := by
  -- Convexity of f is equivalent to convexity of its epigraph.
  simpa [epigraph] using (hconv.convex_epigraph (s := Set.univ))

/-- Epigraph is closed for lower semicontinuous functions. -/
lemma epigraph_closed (f : Config n → ℝ) (hlsc : LowerSemicontinuous f) :
    IsClosed (epigraph f) := by
  -- Lower semicontinuity is equivalent to a closed epigraph.
  simpa [epigraph] using (LowerSemicontinuous.isClosed_epigraph hlsc)

/-- Separation data from a strict point below the epigraph. -/
lemma separation_data (f : Config n → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) (x : Config n) {t : ℝ} (ht : t < f x) :
    ∃ L : (Config n × ℝ) →L[ℝ] ℝ,
      ∃ α : ℝ,
        L (x, t) < α ∧ ∀ y : Config n, ∀ s : ℝ, f y ≤ s → α ≤ L (y, s) := by
  -- Separate a point below the epigraph from the closed convex epigraph.
  have hconv' : Convex ℝ (epigraph f) := epigraph_convex f hconv
  have hclosed : IsClosed (epigraph f) := epigraph_closed f hlsc
  have hx : (x, t) ∉ epigraph f := by
    -- Strict inequality puts the point below the epigraph.
    simp [epigraph, not_le_of_gt ht]
  obtain ⟨L, α, hLt, hsep⟩ := geometric_hahn_banach_point_closed hconv' hclosed hx
  refine ⟨L, α, hLt, ?_⟩
  intro y s hs
  -- Convert strict separation into the required weak inequality.
  exact le_of_lt (hsep _ (by simpa [epigraph] using hs))

/-- Decompose a continuous linear functional on Config n × ℝ. -/
lemma linear_form_decompose (L : (Config n × ℝ) →L[ℝ] ℝ) :
    ∃ p : Config n, ∃ β : ℝ,
      ∀ y : Config n, ∀ s : ℝ, L (y, s) = ⟪p, y⟫_ℝ + β * s := by
  -- Split a linear form on the product into spatial and scalar components.
  refine ⟨(toDual ℝ (Config n)).symm (L.comp (ContinuousLinearMap.inl ℝ (Config n) ℝ)),
    L (0, 1), ?_⟩
  intro y s
  have h₁ : L (y, s) = L (y, 0) + L (0, s) := by
    -- Split along the product coordinates.
    simpa using L.map_add (y, 0) (0, s)
  have h₂ : L (0, s) = (L (0, 1)) * s := by
    -- Linearity in the scalar coordinate.
    simpa [mul_comm] using (L.map_smul s (0, 1))
  have h₃ : L (y, 0) = ⟪(toDual ℝ (Config n)).symm
      (L.comp (ContinuousLinearMap.inl ℝ (Config n) ℝ)), y⟫_ℝ := by
    -- Identify the spatial component via the Riesz map.
    symm
    simp [toDual_symm_apply]
  calc
    L (y, s) = L (y, 0) + L (0, s) := h₁
    _ = L (y, 0) + (L (0, 1)) * s := by
      -- Replace the scalar component using linearity.
      rw [h₂]
    _ = ⟪(toDual ℝ (Config n)).symm
        (L.comp (ContinuousLinearMap.inl ℝ (Config n) ℝ)), y⟫_ℝ + (L (0, 1)) * s := by
      -- Replace the spatial component using the Riesz map.
      rw [h₃]

/-! ## Supporting Affine Bounds -/

/-- Rewrite the supporting affine form after rescaling by `β`. -/
private lemma affine_rewrite (p : Config n) (α β : ℝ) (y : Config n) :
    ⟪-(1 / β) • p, y⟫_ℝ + α / β = (α - ⟪p, y⟫_ℝ) / β := by
  -- Expand the inner product and regroup the scalar factor.
  calc
    ⟪-(1 / β) • p, y⟫_ℝ + α / β
        = (-(1 / β) * ⟪p, y⟫_ℝ) + α * (1 / β) := by
          -- Convert the inner product and division into scalar products.
          simp [inner_smul_left, inner_neg_left, div_eq_inv_mul, mul_comm]
    _ = (α - ⟪p, y⟫_ℝ) * (1 / β) := by ring
    _ = (α - ⟪p, y⟫_ℝ) / β := by
      -- Replace multiplication by the reciprocal with division.
      simp [div_eq_inv_mul, mul_comm]

/-- The separating functional has positive `β`. -/
private lemma beta_pos_of_sep (f : Config n → ℝ) (x : Config n) (ε : ℝ) (hε : 0 < ε)
    (L : (Config n × ℝ) →L[ℝ] ℝ) (α : ℝ) (p : Config n) (β : ℝ)
    (hLt : L (x, f x - ε / 2) < α)
    (hsep : ∀ y : Config n, ∀ s : ℝ, f y ≤ s → α ≤ L (y, s))
    (hL : ∀ y : Config n, ∀ s : ℝ, L (y, s) = ⟪p, y⟫_ℝ + β * s) :
    0 < β := by
  -- If β ≤ 0, strict separation contradicts `α ≤ L (x, f x)`.
  by_contra hβ
  have hβ' : β ≤ 0 := le_of_not_gt hβ
  have hx : α ≤ L (x, f x) := hsep x (f x) le_rfl
  have hx' : L (x, f x) ≤ L (x, f x - ε / 2) := by
    -- If β ≤ 0, decreasing `s` increases the linear form.
    have hfx : f x - ε / 2 ≤ f x := by nlinarith [hε]
    have hmul : β * f x ≤ β * (f x - ε / 2) := mul_le_mul_of_nonpos_left hfx hβ'
    have hmul' :
        ⟪p, x⟫_ℝ + β * f x ≤ ⟪p, x⟫_ℝ + β * (f x - ε / 2) :=
      add_le_add_right hmul ⟪p, x⟫_ℝ
    simpa [hL] using hmul'
  exact (not_lt_of_ge (le_trans hx hx')) hLt

/-- Turn strict separation at `x` into a strict affine bound. -/
private lemma supporting_affine_at (f : Config n → ℝ) (x : Config n) (ε : ℝ)
    (p : Config n) (β α : ℝ) (hβ : 0 < β)
    (hLt' : ⟪p, x⟫_ℝ + β * (f x - ε / 2) < α) :
    f x - ε / 2 < ⟪-(1 / β) • p, x⟫_ℝ + α / β := by
  -- Move terms and divide by positive `β`.
  have h1 : β * (f x - ε / 2) < α - ⟪p, x⟫_ℝ := by linarith [hLt']
  have h1' : (f x - ε / 2) * β < α - ⟪p, x⟫_ℝ := by
    simpa [mul_comm] using h1
  have hx' : f x - ε / 2 < (α - ⟪p, x⟫_ℝ) / β := (lt_div_iff₀ hβ).mpr h1'
  -- Rewrite the affine form to match the divided expression.
  calc
    f x - ε / 2 < (α - ⟪p, x⟫_ℝ) / β := hx'
    _ = ⟪-(1 / β) • p, x⟫_ℝ + α / β := by
      symm
      exact affine_rewrite p α β x

/-- Turn the separation inequality at `y` into a global affine lower bound. -/
private lemma supporting_affine_le (f : Config n → ℝ) (y : Config n)
    (p : Config n) (β α : ℝ) (hβ : 0 < β)
    (hsep' : α ≤ ⟪p, y⟫_ℝ + β * f y) :
    ⟪-(1 / β) • p, y⟫_ℝ + α / β ≤ f y := by
  -- Move terms and divide by positive `β`.
  have h1 : α - ⟪p, y⟫_ℝ ≤ β * f y := by linarith [hsep']
  have h1' : α - ⟪p, y⟫_ℝ ≤ f y * β := by
    simpa [mul_comm] using h1
  have hy' : (α - ⟪p, y⟫_ℝ) / β ≤ f y := (div_le_iff₀ hβ).mpr h1'
  -- Rewrite the affine form to match the divided expression.
  calc
    ⟪-(1 / β) • p, y⟫_ℝ + α / β = (α - ⟪p, y⟫_ℝ) / β := by
      exact affine_rewrite p α β y
    _ ≤ f y := hy'

/-- From separation, build an affine lower bound `y ↦ ⟪q,y⟫ + a`. -/
private lemma supporting_affine (f : Config n → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) (x : Config n) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Config n, ∃ a : ℝ,
      ⟪q, x⟫_ℝ + a > f x - ε / 2 ∧ ∀ y, ⟪q, y⟫_ℝ + a ≤ f y := by
  -- Separate a point strictly below the epigraph.
  obtain ⟨L, α, hLt, hsep⟩ :=
    separation_data f hconv hlsc x (t := f x - ε / 2) (by linarith)
  obtain ⟨p, β, hL⟩ := linear_form_decompose (n := n) L
  have hβ : 0 < β := beta_pos_of_sep f x ε hε L α p β hLt hsep hL
  refine ⟨-(1 / β) • p, α / β, ?_, ?_⟩
  · -- The affine bound is close to `f x` from below.
    have hLt' : ⟪p, x⟫_ℝ + β * (f x - ε / 2) < α := by
      -- Expand the separating inequality using the decomposition.
      simpa [hL] using hLt
    exact supporting_affine_at f x ε p β α hβ hLt'
  · -- The affine form is below `f` everywhere.
    intro y
    have hsep' : α ≤ ⟪p, y⟫_ℝ + β * f y := by
      -- Use the epigraph inequality at `s = f y`.
      simpa [hL] using hsep y (f y) le_rfl
    exact supporting_affine_le f y p β α hβ hsep'

/-! ## Affine Bounds and Conjugates -/

/-- An affine lower bound controls the conjugate. -/
private lemma conjugate_le_of_affine (f : Config n → ℝ) (q : Config n) (a : ℝ)
    (hbound : ∀ y, ⟪q, y⟫_ℝ + a ≤ f y) :
    legendre f q ≤ -a := by
  -- Each affine term is bounded above by `-a`.
  refine ciSup_le ?_
  intro y
  linarith [hbound y]

/-- An affine lower bound yields a pointwise lower bound on the biconjugate. -/
private lemma biconjugate_ge_of_affine (f : Config n → ℝ) (hf' : HasFiniteBiconjugate f)
    (x q : Config n) (a : ℝ) (hconj : legendre f q ≤ -a) :
    ⟪q, x⟫_ℝ + a ≤ legendre (legendre f) x := by
  -- Choose the slope `q` in the biconjugate supremum.
  have hx : ⟪q, x⟫_ℝ + a ≤ ⟪x, q⟫_ℝ - legendre f q := by
    -- Swap the inner product to align terms.
    have hcomm : ⟪x, q⟫_ℝ = ⟪q, x⟫_ℝ := by
      -- Symmetry of the real inner product.
      simpa using (real_inner_comm q x)
    linarith [hconj, hcomm]
  exact le_trans hx (le_ciSup_of_le (hf' x) q (le_rfl))

/-! ## Full Fenchel-Moreau Theorem -/

/-- Second direction: f(x) ≤ f**(x) for convex lsc functions.

    This uses Hahn-Banach separation on the epigraph to construct
    a supporting hyperplane at each point. -/
lemma le_biconjugate (f : Config n → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f) (_hf : HasFiniteConjugate f)
    (hf' : HasFiniteBiconjugate f) (x : Config n) :
    f x ≤ legendre (legendre f) x := by
  -- Use an ε-argument with a supporting affine bound.
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨q, a, hx, hbound⟩ := supporting_affine f hconv hlsc x hε
  have hconj : legendre f q ≤ -a := conjugate_le_of_affine f q a hbound
  have hx' : f x - ε / 2 < legendre (legendre f) x := by
    -- Insert the affine bound into the biconjugate supremum.
    exact lt_of_lt_of_le hx (biconjugate_ge_of_affine f hf' x q a hconj)
  linarith

/-- Fenchel-Moreau theorem: f** = f for convex lsc functions with finite conjugates.

    For differentiable convex f, subgradients always exist (= gradient),
    so this follows from fenchel_moreau_of_subgradients.

    For general convex lsc f, we use Hahn-Banach separation. -/
theorem fenchel_moreau (f : Config n → ℝ)
    (hconv : ConvexOn ℝ Set.univ f)
    (hlsc : LowerSemicontinuous f)
    (hf : HasFiniteConjugate f)
    (hf' : HasFiniteBiconjugate f) :
    legendre (legendre f) = f := by
  -- Combine the two inequalities pointwise.
  funext x
  apply le_antisymm
  · exact biconjugate_le f hf x
  · exact le_biconjugate f hconv hlsc hf hf' x

end

end Gibbs.Hamiltonian
