import Gibbs.Hamiltonian.Entropy
import Gibbs.Hamiltonian.Legendre
import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.PartitionFunction
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Entropy as a Bregman Generator

Connects negative entropy to Bregman divergence and the Legendre transform.
The deep convex-analytic results are stated as axioms to keep this file a
lightweight bridge between the information-theory and Hamiltonian layers.
-/

namespace Gibbs.Hamiltonian.EntropyBregman

open Gibbs.Hamiltonian

noncomputable section

variable {n : ℕ}

/-- Convert `Fin n → ℝ` to configuration space. -/
private def toConfig (x : Fin n → ℝ) : Config n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm x

/-- Convert configuration space to `Fin n → ℝ`. -/
private def fromConfig (x : Config n) : Fin n → ℝ :=
  (EuclideanSpace.equiv (Fin n) ℝ) x

/-- Negative entropy on configuration space. -/
def negEntropyConfig (n : ℕ) : Config n → ℝ :=
  fun x => ∑ i : Fin n, let xi := (fromConfig x) i
            if xi = 0 then 0 else xi * Real.log xi

/-- Negative entropy is strictly convex on the simplex interior. -/
theorem negEntropyConfig_strictConvex_on_interior (n : ℕ) :
    StrictConvexOn ℝ { x : Config n | ∀ i, 0 < (fromConfig x) i }
      (negEntropyConfig n) := by
  classical
  let S : Set (Config n) := { x : Config n | ∀ i, 0 < (fromConfig x) i }
  let g : ℝ → ℝ := fun x => x * Real.log x
  have hstrict_g : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) g := by
    have h := (strictConvexOn_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) g)
    exact h.subset (by intro x hx; exact le_of_lt hx) (convex_Ioi (0 : ℝ))
  have hconv_g : ConvexOn ℝ (Set.Ioi (0 : ℝ)) g := hstrict_g.convexOn
  have hfrom_add :
      ∀ (a b : ℝ) (x y : Config n) (i : Fin n),
        fromConfig (a • x + b • y) i =
          a * fromConfig x i + b * fromConfig y i := by
    intro a b x y i
    -- `fromConfig` is linear via the EuclideanSpace equivalence.
    simp [fromConfig, map_add, map_smul, mul_add, add_comm, add_left_comm, add_assoc]
  have hconvS : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    intro i
    have hxpos : 0 < fromConfig x i := hx i
    have hypos : 0 < fromConfig y i := hy i
    have hlin := hfrom_add a b x y i
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [hlin, ha0, hb1] using hypos
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simpa [hlin, hb0, ha1] using hxpos
      · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hsum : 0 < a * fromConfig x i + b * fromConfig y i :=
          add_pos (mul_pos ha_pos hxpos) (mul_pos hb_pos hypos)
        simpa [hlin] using hsum
  refine ⟨hconvS, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hneq : ∃ i, fromConfig x i ≠ fromConfig y i := by
    by_contra h
    apply hxy
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    funext i
    by_contra hne
    exact h ⟨i, hne⟩
  rcases hneq with ⟨i0, hneq0⟩
  have hle :
      ∀ i, g (a * fromConfig x i + b * fromConfig y i) ≤
        a * g (fromConfig x i) + b * g (fromConfig y i) := by
    intro i
    have hxpos : 0 < fromConfig x i := hx i
    have hypos : 0 < fromConfig y i := hy i
    have hconv := hconv_g.2 hxpos hypos (le_of_lt ha) (le_of_lt hb) hab
    simpa [g, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hconv
  have hlt :
      g (a * fromConfig x i0 + b * fromConfig y i0) <
        a * g (fromConfig x i0) + b * g (fromConfig y i0) := by
    have hxpos : 0 < fromConfig x i0 := hx i0
    have hypos : 0 < fromConfig y i0 := hy i0
    have hstrict := hstrict_g.2 hxpos hypos hneq0 ha hb hab
    simpa [g, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc] using hstrict
  have hsum_lt :
      ∑ i, g (a * fromConfig x i + b * fromConfig y i) <
        ∑ i, (a * g (fromConfig x i) + b * g (fromConfig y i)) := by
    refine Finset.sum_lt_sum (fun i _ => hle i) ?_
    exact ⟨i0, by simp, hlt⟩
  have hpos_comb :
      ∀ i, 0 < a * fromConfig x i + b * fromConfig y i := by
    intro i
    have hxpos : 0 < fromConfig x i := hx i
    have hypos : 0 < fromConfig y i := hy i
    exact add_pos (mul_pos ha hxpos) (mul_pos hb hypos)
  have hneg_x :
      negEntropyConfig n x = ∑ i, g (fromConfig x i) := by
    unfold negEntropyConfig g
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hxpos : 0 < fromConfig x i := hx i
    have hne : fromConfig x i ≠ 0 := ne_of_gt hxpos
    simp [hne]
  have hneg_y :
      negEntropyConfig n y = ∑ i, g (fromConfig y i) := by
    unfold negEntropyConfig g
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hypos : 0 < fromConfig y i := hy i
    have hne : fromConfig y i ≠ 0 := ne_of_gt hypos
    simp [hne]
  have hneg_xy :
      negEntropyConfig n (a • x + b • y) =
        ∑ i, g (a * fromConfig x i + b * fromConfig y i) := by
    unfold negEntropyConfig g
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hpos : 0 < a * fromConfig x i + b * fromConfig y i := hpos_comb i
    have hne : a * fromConfig x i + b * fromConfig y i ≠ 0 := ne_of_gt hpos
    have hlin := hfrom_add a b x y i
    simp [hlin, hne]
  have hsum_rhs :
      ∑ i, (a * g (fromConfig x i) + b * g (fromConfig y i)) =
        a * (∑ i, g (fromConfig x i)) + b * (∑ i, g (fromConfig y i)) := by
    calc
      ∑ i, (a * g (fromConfig x i) + b * g (fromConfig y i))
          = ∑ i, a * g (fromConfig x i) + ∑ i, b * g (fromConfig y i) := by
              simp [Finset.sum_add_distrib]
      _ = a * (∑ i, g (fromConfig x i)) + b * (∑ i, g (fromConfig y i)) := by
              simp [Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
  calc
    negEntropyConfig n (a • x + b • y)
        = ∑ i, g (a * fromConfig x i + b * fromConfig y i) := hneg_xy
    _ < ∑ i, (a * g (fromConfig x i) + b * g (fromConfig y i)) := hsum_lt
    _ = a * negEntropyConfig n x + b * negEntropyConfig n y := by
        simp [hsum_rhs, hneg_x, hneg_y]

/-! ## KL = Bregman -/

/-- KL divergence is the Bregman divergence of negative entropy. -/
axiom kl_eq_bregman_negEntropy (n : ℕ) (p q : Fin n → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1) :
    Gibbs.Hamiltonian.Entropy.klDivergence p q =
      bregman (negEntropyConfig n) (toConfig p) (toConfig q)

/-- KL nonnegativity via Bregman divergence. -/
axiom kl_nonneg_via_bregman (n : ℕ) (p q : Fin n → ℝ)
    (hp_nn : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_pos : ∀ i, 0 < q i) (hq_sum : ∑ i, q i = 1) :
    0 ≤ Gibbs.Hamiltonian.Entropy.klDivergence p q

/-! ## Legendre Dual of Negative Entropy -/

/-- The Legendre dual of negative entropy is log-sum-exp. -/
axiom legendre_negEntropy_eq_logSumExp (n : ℕ) [NeZero n] (θ : Config n) :
    legendre (negEntropyConfig n) θ =
      Real.log (∑ i : Fin n, Real.exp ((fromConfig θ) i))

/-- Softmax distribution. -/
def softmax (n : ℕ) (θ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.exp (θ i) / ∑ j, Real.exp (θ j)

/-- Softmax is nonnegative. -/
theorem softmax_nonneg (n : ℕ) (θ : Fin n → ℝ) (i : Fin n) :
    0 ≤ softmax n θ i := by
  unfold softmax
  have hsum : 0 ≤ ∑ j, Real.exp (θ j) := by
    exact Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)
  have hden : 0 ≤ (∑ j, Real.exp (θ j))⁻¹ := by
    exact inv_nonneg.mpr hsum
  -- division as multiplication by inverse
  simpa [div_eq_mul_inv] using mul_nonneg (Real.exp_nonneg _) hden

/-- Softmax sums to one. -/
theorem softmax_sum_one (n : ℕ) [NeZero n] (θ : Fin n → ℝ) :
    ∑ i, softmax n θ i = 1 := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let i0 : Fin n := ⟨0, hn⟩
  have hmem : i0 ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hpos_term : 0 < Real.exp (θ i0) := Real.exp_pos _
  have hle : Real.exp (θ i0) ≤ ∑ j, Real.exp (θ j) := by
    exact Finset.single_le_sum (f := fun j => Real.exp (θ j))
      (fun _ _ => (Real.exp_pos _).le) hmem
  have hpos : 0 < ∑ j, Real.exp (θ j) := lt_of_lt_of_le hpos_term hle
  have hne : (∑ j, Real.exp (θ j)) ≠ 0 := ne_of_gt hpos
  calc
    ∑ i, softmax n θ i
        = ∑ i, Real.exp (θ i) / ∑ j, Real.exp (θ j) := by rfl
    _ = (∑ i, Real.exp (θ i)) / (∑ j, Real.exp (θ j)) := by
        simpa using (Finset.sum_div (s := (Finset.univ : Finset (Fin n)))
          (f := fun i => Real.exp (θ i)) (a := ∑ j, Real.exp (θ j))).symm
    _ = 1 := by field_simp [hne]

/-- Free energy is a scaled Legendre dual of negative entropy. -/
axiom freeEnergy_eq_scaled_legendre_dual (n : ℕ) [NeZero n]
    (H : Fin n → ℝ) (β : ℝ) (hβ : 0 < β) :
    PartitionFunction.freeEnergy H β =
      -(1/β) * legendre (negEntropyConfig n) (toConfig (fun i => -β * H i))

end

end Gibbs.Hamiltonian.EntropyBregman
