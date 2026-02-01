import Gibbs.MeanField.LipschitzBridge
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# ODE Existence and Simplex Invariance

Given a Lipschitz mean-field choreography, this file proves that the ODE
dx/dt = F(x) has a unique global solution that remains on the simplex. The
argument proceeds in three stages: local existence from Picard-Lindelof on a
bounded domain, sum preservation (the total probability stays at one because
the drift is conservative), and simplex invariance (each component stays
nonneg via a Gronwall comparison using the boundary condition from the
choreography).
-/

namespace Gibbs.MeanField

open scoped Classical NNReal Topology
open Set

noncomputable section

variable {Q : Type*} [Fintype Q]

/-! ## Boundedness Properties -/

/-- The simplex is bounded (contained in unit hypercube). -/
theorem simplex_bounded [Nonempty Q] : Bornology.IsBounded (Simplex Q) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : Q → ℝ)]
  use Fintype.card Q
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  -- ‖x‖ ≤ |Q| for x in simplex since each |x q| ≤ 1
  have h : ∀ q, ‖x q‖ ≤ 1 := fun q => by
    have hle := Simplex.le_one hx q
    have hnn := hx.1 q
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle
  calc ‖x‖ = ‖x‖ := rfl
    _ ≤ Fintype.card Q := by
        -- Use that pi norm is bounded by card * max component
        rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg (Fintype.card Q))]
        intro q
        calc ‖x q‖ ≤ 1 := h q
          _ ≤ Fintype.card Q := Nat.one_le_cast.mpr Fintype.card_pos

/-- A globally Lipschitz function is bounded on bounded sets. -/
theorem lipschitz_bounded_on_bounded
    {E F : Type*} [PseudoMetricSpace E] [SeminormedAddCommGroup F]
    {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : Bornology.IsBounded s) (hne : s.Nonempty) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, ‖f x‖ ≤ M := by
  obtain ⟨x₀, hx₀⟩ := hne
  rw [Metric.isBounded_iff_subset_closedBall x₀] at hs
  obtain ⟨R, hsub⟩ := hs
  -- Use max R 0 to ensure non-negativity
  let R' := max R 0
  use K * R' + ‖f x₀‖
  constructor
  · apply add_nonneg
    · exact mul_nonneg K.2 (le_max_right R 0)
    · exact norm_nonneg _
  intro x hx
  have hxR := hsub hx
  rw [Metric.mem_closedBall] at hxR
  have hRR' : R ≤ R' := le_max_left R 0
  have hdist_le : dist x x₀ ≤ R' := le_trans hxR hRR'
  have hfx : ‖f x - f x₀‖ ≤ K * dist x x₀ := by
    rw [← dist_eq_norm]
    exact hf.dist_le_mul x x₀
  have hnorm : ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := by
    have := norm_sub_norm_le (f x) (f x₀)
    linarith
  calc ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := hnorm
    _ ≤ K * dist x x₀ + ‖f x₀‖ := by linarith
    _ ≤ K * R' + ‖f x₀‖ := by
        have h : (K : ℝ) * dist x x₀ ≤ K * R' := mul_le_mul_of_nonneg_left hdist_le K.2
        linarith

/-- The simplex is nonempty (contains the uniform distribution). -/
theorem simplex_nonempty [Nonempty Q] : (Simplex Q).Nonempty := by
  use fun _ => 1 / Fintype.card Q
  constructor
  · intro q
    apply div_nonneg
    · norm_num
    · exact Nat.cast_nonneg (Fintype.card Q)
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)]

/-- The extended drift is bounded on the simplex. -/
theorem MeanFieldChoreography.extendDrift_bounded_simplex [Nonempty Q] (C : MeanFieldChoreography Q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Simplex Q, ‖C.extendDrift x‖ ≤ M :=
  lipschitz_bounded_on_bounded C.extendDrift_lipschitz simplex_bounded simplex_nonempty

/-! ## Local Existence -/

/-- Helper: get a positive bound on a Lipschitz function over a closed ball. -/
private theorem lipschitz_ball_bound {E F : Type*} [PseudoMetricSpace E]
    [SeminormedAddCommGroup F] {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x₀ : E) (a : ℝ) (ha : 0 ≤ a) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Metric.closedBall x₀ a, ‖f x‖ ≤ L := by
  -- Lipschitz functions are bounded on bounded sets
  obtain ⟨M, _, hMle⟩ := lipschitz_bounded_on_bounded hf
    Metric.isBounded_closedBall ⟨x₀, Metric.mem_closedBall_self ha⟩
  exact ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right M 1),
    fun x hx => le_trans (hMle x hx) (le_max_left M 1)⟩

/-- Helper: construct IsPicardLindelof for autonomous Lipschitz ODE.
    Returns the Picard-Lindelöf structure with time step T = 1/(2L). -/
private theorem picard_lindelof_autonomous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E) :
    ∃ T > 0, ∃ (t₀ : ↑(Icc (-T) T)),
      ↑t₀ = (0 : ℝ) ∧
      ∃ (a r : ℝ≥0) (L : ℝ≥0),
        IsPicardLindelof (fun _ => f) t₀ x₀ a r L K ∧
        x₀ ∈ Metric.closedBall x₀ r := by
  -- Get bound L on f over ball of radius 2
  obtain ⟨L, hLpos, hLbound⟩ := lipschitz_ball_bound hf x₀ 2 (by norm_num)
  let L' : ℝ≥0 := ⟨L, le_of_lt hLpos⟩
  let a : ℝ≥0 := 2; let r : ℝ≥0 := 1
  -- Time step T = 1/(2L), ensuring L·T ≤ a - r = 1
  let T := 1 / (2 * L)
  have hTpos : T > 0 := div_pos one_pos (mul_pos two_pos hLpos)
  have ht0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, by linarith⟩
  -- Verify Picard-Lindelöf conditions
  have hcond : (L' : ℝ) * max (T - 0) (0 - (-T)) ≤ (a : ℝ) - r := by
    simp only [sub_zero, sub_neg_eq_add, zero_add, max_self, a, r,
      NNReal.coe_ofNat, NNReal.coe_one]
    calc (L : ℝ) * (1 / (2 * L)) = 1 / 2 := by field_simp
      _ ≤ 2 - 1 := by norm_num
  exact ⟨T, hTpos, ⟨0, ht0⟩, rfl, a, r, L',
    IsPicardLindelof.of_time_independent hLbound hf.lipschitzOnWith hcond,
    Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1)⟩

/-- Local existence: ODE solutions exist on a small time interval.
    Direct application of Picard-Lindelöf via `picard_lindelof_autonomous`. -/
theorem local_ode_exists [Nonempty Q] (C : MeanFieldChoreography Q) (x₀ : Q → ℝ)
    (_hx₀ : x₀ ∈ Simplex Q) :
    ∃ T > 0, ∃ sol : ℝ → (Q → ℝ),
      sol 0 = x₀ ∧
      ContinuousOn sol (Icc (-T) T) ∧
      ∀ t ∈ Ico (-T) T, HasDerivWithinAt sol (C.extendDrift (sol t)) (Ici t) t := by
  -- Get Picard-Lindelöf structure for the extended drift
  obtain ⟨T, hTpos, t₀, ht₀, a, r, L, hPL, hx₀_ball⟩ :=
    picard_lindelof_autonomous C.extendDrift_lipschitz x₀
  -- Apply existence theorem
  obtain ⟨sol, hsol0, hsol_deriv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hx₀_ball
  refine ⟨T, hTpos, sol, ?_, ?_, ?_⟩
  · -- sol 0 = x₀ (t₀ = 0 as subtype)
    rw [show (0 : ℝ) = ↑t₀ from ht₀.symm]; exact hsol0
  · -- Continuity: differentiable on Icc implies continuous on Icc
    intro t ht; exact (hsol_deriv t ht).continuousWithinAt
  · -- Derivative: convert from HasDerivWithinAt on Icc to Ici
    intro t ht
    exact (hsol_deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)

/-! ## Sum Preservation -/

/-- The sum functional is a continuous linear map. -/
def sumCLM (Q : Type*) [Fintype Q] : (Q → ℝ) →L[ℝ] ℝ :=
  (Finset.univ.sum fun q => ContinuousLinearMap.proj q : (Q → ℝ) →L[ℝ] ℝ)

@[simp]
theorem sumCLM_apply (x : Q → ℝ) : sumCLM Q x = ∑ q, x q := by
  simp [sumCLM, ContinuousLinearMap.proj]

/-- If sol satisfies dx/dt = F(x) where F conserves probability,
    then ∑ sol(t)_q is constant (derivative is zero). -/
theorem sum_hasDerivAt_zero
    (C : MeanFieldChoreography Q) (sol : ℝ → (Q → ℝ))
    (hderiv : ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t) (t : ℝ) (ht : t ≥ 0)
    (hsol_simplex : sol t ∈ Simplex Q) :
    HasDerivAt (fun s => ∑ q, sol s q) 0 t := by
  -- The sum functional composed with sol has derivative = sum of drift = 0
  have h1 : HasDerivAt sol (C.drift (sol t)) t := hderiv t ht
  -- Apply the continuous linear map (sum) to the derivative
  have h2 : HasDerivAt (fun s => sumCLM Q (sol s)) (sumCLM Q (C.drift (sol t))) t :=
    (sumCLM Q).hasFDerivAt.comp_hasDerivAt t h1
  simp only [sumCLM_apply] at h2
  -- By conservation, ∑ C.drift(sol t) q = 0
  have h3 : ∑ q, C.drift (sol t) q = 0 := C.drift_conserves (sol t) hsol_simplex
  rwa [h3] at h2

/-- Helper: a continuous function with zero derivative on [0,t] is constant.
    Uses `ODE_solution_unique` with zero vector field. -/
private theorem constant_of_zero_deriv {g : ℝ → ℝ}
    (hcont : Continuous g) (hderiv : ∀ s ≥ 0, HasDerivAt g 0 s)
    {t : ℝ} (ht : 0 ≤ t) : g t = g 0 := by
  -- Trivial case
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · rfl
  -- Apply ODE uniqueness: g and (fun _ => g 0) both solve dx/dt = 0
  have heqOn : Set.EqOn g (fun _ => g 0) (Set.Icc 0 t) := by
    apply ODE_solution_unique (v := fun (_ : ℝ) (_ : ℝ) => (0 : ℝ)) (K := 0)
      (a := 0) (b := t)
    · intro _; exact LipschitzWith.const 0
    · exact hcont.continuousOn
    · intro s hs; exact (hderiv s hs.1).hasDerivWithinAt
    · exact continuousOn_const
    · intro s _; exact hasDerivWithinAt_const s (Set.Ici s) (g 0)
    · rfl
  exact heqOn ⟨ht, le_refl t⟩

/-- Sum is preserved along solutions: ∑ sol(t)_q = ∑ sol(0)_q for all t ≥ 0,
    provided the solution stays in the simplex (so conservation applies). -/
theorem sum_preserved
    (C : MeanFieldChoreography Q) (sol : ℝ → (Q → ℝ))
    (hcont : Continuous sol) (hderiv : ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t)
    (hsimplex : ∀ t ≥ 0, sol t ∈ Simplex Q) (t : ℝ) (ht : t ≥ 0) :
    ∑ q, sol t q = ∑ q, sol 0 q := by
  -- The scalar function g(s) = ∑ sol(s)_q has zero derivative
  let g : ℝ → ℝ := fun s => ∑ q, sol s q
  have hcont_g : Continuous g :=
    continuous_finset_sum _ fun q _ => (continuous_apply q).comp hcont
  have hderiv_zero : ∀ s ≥ 0, HasDerivAt g 0 s := fun s hs =>
    sum_hasDerivAt_zero C sol hderiv s hs (hsimplex s hs)
  exact constant_of_zero_deriv hcont_g hderiv_zero ht

/-! ## Sum Preservation (Global Conservation) -/

/-- Sum is preserved when drift conserves total mass on all inputs. -/
private theorem sum_preserved_of_conserves_all
    (C : MeanFieldChoreography Q) (sol : ℝ → (Q → ℝ))
    (hcont : Continuous sol) (hderiv : ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t)
    (hcons : ∀ x, ∑ q, C.drift x q = 0) (t : ℝ) (ht : t ≥ 0) :
    ∑ q, sol t q = ∑ q, sol 0 q := by
  -- Apply the linear-sum derivative and use global conservation.
  let g : ℝ → ℝ := fun s => ∑ q, sol s q
  have hcont_g : Continuous g :=
    continuous_finset_sum _ fun q _ => (continuous_apply q).comp hcont
  have hderiv_zero : ∀ s ≥ 0, HasDerivAt g 0 s := by
    intro s hs
    have h1 : HasDerivAt sol (C.drift (sol s)) s := hderiv s hs
    have h2 : HasDerivAt (fun u => sumCLM Q (sol u)) (sumCLM Q (C.drift (sol s))) s :=
      (sumCLM Q).hasFDerivAt.comp_hasDerivAt s h1
    have hsum : ∑ q, C.drift (sol s) q = 0 := hcons (sol s)
    simpa [sumCLM_apply, hsum] using h2
  exact constant_of_zero_deriv hcont_g hderiv_zero ht

/-! ## Global Existence -/

/-- Fixed step size for Lipschitz ODE chaining. -/
private def odeStep (K : ℝ≥0) : ℝ :=
  -- Use a uniform step with K·δ < 1.
  1 / (2 * ((K : ℝ) + 1))

/-- Helper: uniform step is positive and small enough for contraction. -/
private theorem odeStep_pos {K : ℝ≥0} :
    0 < odeStep K ∧ (K : ℝ) * odeStep K < 1 := by
  have hpos : 0 < (K : ℝ) + 1 := by positivity
  have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
  have hstep : 0 < odeStep K := by
    unfold odeStep; positivity
  have hcalc : (K : ℝ) * odeStep K = (K : ℝ) / (2 * ((K : ℝ) + 1)) := by
    unfold odeStep; field_simp
  have hK : (K : ℝ) * odeStep K < 1 / 2 := by
    rw [hcalc]
    rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [K.2]
  exact ⟨hstep, by linarith⟩

/-- Helper: Lipschitz bound on a closed ball using a linear estimate. -/
private theorem lipschitz_norm_le_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E) (a : ℝ)
    (x : E) (hx : x ∈ Metric.closedBall x₀ a) :
    ‖f x‖ ≤ ‖f x₀‖ + (K : ℝ) * a := by
  -- Combine triangle inequality with the Lipschitz bound.
  have hdist : dist (f x) (f x₀) ≤ (K : ℝ) * dist x x₀ := hf.dist_le_mul x x₀
  have hball : dist x x₀ ≤ a := by simpa [Metric.mem_closedBall] using hx
  have htri : ‖f x‖ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (f x - f x₀) (f x₀))
  have hdist' : ‖f x - f x₀‖ ≤ (K : ℝ) * a := by
    have : ‖f x - f x₀‖ = dist (f x) (f x₀) := by
      simp [dist_eq_norm]
    calc ‖f x - f x₀‖ = dist (f x) (f x₀) := this
      _ ≤ (K : ℝ) * dist x x₀ := hdist
      _ ≤ (K : ℝ) * a := by gcongr
  linarith

/-- Helper: a fixed-step Picard-Lindelöf solution on [0, δ]. -/
private theorem lipschitz_step_params
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    (δ : ℝ) (hδ : 0 < δ) (hKδ : (K : ℝ) * δ < 1) (x₀ : E) :
    ∃ a : ℝ, 0 ≤ a ∧
      ∃ L : ℝ, 0 ≤ L ∧
        (∀ x ∈ Metric.closedBall x₀ a, ‖f x‖ ≤ L) ∧
        L * δ ≤ a := by
  -- Solve L * δ = a with L = ‖f x₀‖ + K * a.
  let c : ℝ := 1 - (K : ℝ) * δ
  have hcpos : 0 < c := by linarith
  let a : ℝ := ‖f x₀‖ * δ / c
  have ha : 0 ≤ a := by
    have hnum : 0 ≤ ‖f x₀‖ * δ := mul_nonneg (norm_nonneg _) (le_of_lt hδ)
    exact div_nonneg hnum (le_of_lt hcpos)
  let L : ℝ := ‖f x₀‖ + (K : ℝ) * a
  have hL : 0 ≤ L := by
    exact add_nonneg (norm_nonneg _) (mul_nonneg K.2 ha)
  have hbound : ∀ x ∈ Metric.closedBall x₀ a, ‖f x‖ ≤ L := by
    intro x hx
    exact lipschitz_norm_le_closedBall hf x₀ a x hx
  have hcond : L * δ ≤ a := by
    have hcalc : (L : ℝ) * δ = a := by
      have hc : c ≠ 0 := ne_of_gt hcpos
      have hac : a * c = ‖f x₀‖ * δ := by
        dsimp [a]
        field_simp [c, hc]
      calc
        L * δ = (‖f x₀‖ + (K : ℝ) * a) * δ := by rfl
        _ = ‖f x₀‖ * δ + (K : ℝ) * a * δ := by ring
        _ = ‖f x₀‖ * δ + (K : ℝ) * δ * a := by ring
        _ = ‖f x₀‖ * δ + (1 - c) * a := by
              have : (K : ℝ) * δ = 1 - c := by simp [c]
              simp [this]
        _ = a + (‖f x₀‖ * δ - a * c) := by ring
        _ = a := by simp [hac]
    exact le_of_eq hcalc
  exact ⟨a, ha, L, hL, hbound, hcond⟩

private theorem lipschitz_step_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    (δ : ℝ) (hδ : 0 < δ) (hKδ : (K : ℝ) * δ < 1) (x₀ : E) :
    ∃ sol : ℝ → E,
      sol 0 = x₀ ∧
      ∀ t ∈ Icc 0 δ, HasDerivWithinAt sol (f (sol t)) (Icc 0 δ) t := by
  -- Choose parameters satisfying the Picard-Lindelöf conditions.
  obtain ⟨a, ha, L, hL, hbound, hcond⟩ := lipschitz_step_params hf δ hδ hKδ x₀
  let aNN : ℝ≥0 := ⟨a, ha⟩
  let LNN : ℝ≥0 := ⟨L, hL⟩
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) δ := by exact ⟨le_rfl, le_of_lt hδ⟩
  let t₀ : ↑(Icc (0 : ℝ) δ) := ⟨0, ht0⟩
  have hcond' : (LNN : ℝ) * max (δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (aNN : ℝ) - 0 := by
    -- Simplify the max and use the parameter condition.
    simpa [t₀, aNN, LNN, sub_eq_add_neg, max_eq_left, le_of_lt hδ] using hcond
  have hpl :
      IsPicardLindelof (fun _ => f) t₀ x₀ aNN 0 LNN K :=
    IsPicardLindelof.of_time_independent hbound (by simpa using hf.lipschitzOnWith) hcond'
  obtain ⟨sol, hsol0, hderiv⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨sol, by simpa using hsol0, hderiv⟩

/-! ## Fixed-Step Chaining Helpers -/

/-- Shift a solution in time by `t₀`. -/
private def shiftSol {E : Type*} (t₀ : ℝ) (sol : ℝ → E) : ℝ → E :=
  -- Use translation in time for autonomous ODEs.
  fun t => sol (t - t₀)

/-- The shift maps [t₀, t₀+δ] into [0, δ]. -/
private theorem shift_mapsTo {t₀ δ : ℝ} :
    MapsTo (fun t => t - t₀) (Icc t₀ (t₀ + δ)) (Icc (0 : ℝ) δ) := by
  -- Subtracting t₀ sends endpoints to 0 and δ.
  intro t ht
  constructor
  · exact sub_nonneg.mpr ht.1
  · have : t - t₀ ≤ δ := by linarith [ht.2]
    exact this

/-- Shifting preserves the derivative property on a translated interval. -/
private theorem shift_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {t₀ δ : ℝ} {sol : ℝ → E}
    (hsol : ∀ t ∈ Icc (0 : ℝ) δ,
      HasDerivWithinAt sol (f (sol t)) (Icc (0 : ℝ) δ) t)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + δ)) :
    HasDerivWithinAt (shiftSol t₀ sol) (f ((shiftSol t₀ sol) t))
      (Icc t₀ (t₀ + δ)) t := by
  -- Use the chain rule with the translation map.
  have ht' : t - t₀ ∈ Icc (0 : ℝ) δ := shift_mapsTo ht
  have hderiv := hsol (t - t₀) ht'
  have hshift : HasDerivWithinAt (fun t => t - t₀) (1 : ℝ) (Icc t₀ (t₀ + δ)) t := by
    simpa using (hasDerivWithinAt_id t (Icc t₀ (t₀ + δ))).sub_const t₀
  have hcomp := hderiv.scomp t hshift (shift_mapsTo (t₀ := t₀) (δ := δ))
  simpa [shiftSol, one_smul] using hcomp

/-- Extend a solution by one step using a piecewise definition. -/
private def extendSol {E : Type*} (t₀ : ℝ) (sol step : ℝ → E) : ℝ → E :=
  -- Use `sol` before t₀ and the shifted step after.
  fun t => if t ≤ t₀ then sol t else step (t - t₀)

/-! ## Neighborhood Helpers -/

/-- Left-side neighborhood inclusion for interval extension. -/
private theorem nhdsWithin_left_mem {t t₀ δ : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Icc (0 : ℝ) t₀) (hlt : t < t₀) :
    Icc (0 : ℝ) t₀ ∈ 𝓝[ Icc (0 : ℝ) (t₀ + δ) ] t := by
  -- Use interior neighborhoods for t > 0, and nhdsGE for t = 0.
  by_cases hzero : t = 0
  · subst hzero
    have hpos : (0 : ℝ) < t₀ := by linarith
    have hmem : Icc (0 : ℝ) t₀ ∈ 𝓝[≥] (0 : ℝ) := Icc_mem_nhdsGE hpos
    have hnhds : 𝓝[ Icc (0 : ℝ) (t₀ + δ) ] (0 : ℝ) = 𝓝[≥] (0 : ℝ) := by
      simp [nhdsWithin_Icc_eq_nhdsGE (by exact add_pos hpos hδ)]
    simpa [hnhds] using hmem
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    have hmem : Icc (0 : ℝ) t₀ ∈ 𝓝 t := Icc_mem_nhds htpos hlt
    exact mem_nhdsWithin_of_mem_nhds hmem

/-- Right-side neighborhood inclusion for interval extension. -/
private theorem nhdsWithin_right_mem {t t₀ δ : ℝ} (ht0 : 0 ≤ t₀) (hδ : 0 < δ)
    (ht : t ∈ Icc t₀ (t₀ + δ)) (hgt : t₀ < t) :
    Icc t₀ (t₀ + δ) ∈ 𝓝[ Icc (0 : ℝ) (t₀ + δ) ] t := by
  -- Use interior neighborhoods for t < t₀+δ, and nhdsLE at the endpoint.
  by_cases htop : t = t₀ + δ
  · subst htop
    have hpos : t₀ < t₀ + δ := by exact lt_add_of_pos_right _ hδ
    have hmem : Icc t₀ (t₀ + δ) ∈ 𝓝[≤] (t₀ + δ) := Icc_mem_nhdsLE hpos
    have hpos0 : (0 : ℝ) < t₀ + δ := by exact add_pos_of_nonneg_of_pos ht0 hδ
    have hnhds : 𝓝[ Icc (0 : ℝ) (t₀ + δ) ] (t₀ + δ) = 𝓝[≤] (t₀ + δ) := by
      simp [nhdsWithin_Icc_eq_nhdsLE hpos0]
    simpa [hnhds] using hmem
  · have htlt : t < t₀ + δ := lt_of_le_of_ne ht.2 htop
    have hmem : Icc t₀ (t₀ + δ) ∈ 𝓝 t := Icc_mem_nhds hgt htlt
    exact mem_nhdsWithin_of_mem_nhds hmem

/-- Derivative property for a one-step extension. -/
private theorem extend_hasDerivWithinAt_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {t₀ δ : ℝ} {sol step : ℝ → E}
    (hδ : 0 < δ)
    (hsol : ∀ t ∈ Icc (0 : ℝ) t₀,
      HasDerivWithinAt sol (f (sol t)) (Icc (0 : ℝ) t₀) t)
    (_hstep : ∀ t ∈ Icc (0 : ℝ) δ,
      HasDerivWithinAt step (f (step t)) (Icc (0 : ℝ) δ) t)
    (_hstep0 : step 0 = sol t₀)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (t₀ + δ)) (hlt : t < t₀) :
    HasDerivWithinAt (extendSol t₀ sol step)
      (f ((extendSol t₀ sol step) t)) (Icc (0 : ℝ) (t₀ + δ)) t := by
  -- Use the left solution and extend to the larger interval.
  have ht0 : t ∈ Icc (0 : ℝ) t₀ := ⟨ht.1, le_of_lt hlt⟩
  have h := hsol t ht0
  have hsol' :
      HasDerivWithinAt (extendSol t₀ sol step) (f (sol t)) (Icc (0 : ℝ) t₀) t := by
    have hs : ∀ s ∈ Icc (0 : ℝ) t₀, extendSol t₀ sol step s = sol s := by
      intro s hs; simp [extendSol, hs.2]
    exact h.congr_of_mem hs ht0
  have hmem : Icc (0 : ℝ) t₀ ∈ 𝓝[ Icc (0 : ℝ) (t₀ + δ) ] t :=
    nhdsWithin_left_mem hδ ht0 hlt
  have h' := hsol'.mono_of_mem_nhdsWithin hmem
  have hle : t ≤ t₀ := le_of_lt hlt
  simpa [extendSol, hle] using h'

private theorem extend_hasDerivWithinAt_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {t₀ δ : ℝ} {sol step : ℝ → E}
    (ht0 : 0 ≤ t₀)
    (hδ : 0 < δ)
    (hsol : ∀ t ∈ Icc (0 : ℝ) t₀,
      HasDerivWithinAt sol (f (sol t)) (Icc (0 : ℝ) t₀) t)
    (hstep : ∀ t ∈ Icc (0 : ℝ) δ,
      HasDerivWithinAt step (f (step t)) (Icc (0 : ℝ) δ) t)
    (hstep0 : step 0 = sol t₀)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (t₀ + δ)) (hgt : t₀ < t) :
    HasDerivWithinAt (extendSol t₀ sol step)
      (f ((extendSol t₀ sol step) t)) (Icc (0 : ℝ) (t₀ + δ)) t := by
  -- Use the shifted step solution on the right side.
  have ht1 : t ∈ Icc t₀ (t₀ + δ) := ⟨le_of_lt hgt, ht.2⟩
  have h := shift_hasDerivWithinAt hstep t ht1
  have hshift' :
      HasDerivWithinAt (extendSol t₀ sol step) (f (shiftSol t₀ step t)) (Icc t₀ (t₀ + δ)) t := by
    have hs : ∀ s ∈ Icc t₀ (t₀ + δ), extendSol t₀ sol step s = shiftSol t₀ step s := by
      intro s hs
      by_cases hle : s ≤ t₀
      · have hst : s = t₀ := by linarith [hs.1, hle]
        subst hst
        simp [extendSol, shiftSol, hstep0]
      · simp [extendSol, shiftSol, hle]
    exact h.congr_of_mem hs ht1
  have hmem : Icc t₀ (t₀ + δ) ∈ 𝓝[ Icc (0 : ℝ) (t₀ + δ) ] t :=
    nhdsWithin_right_mem ht0 hδ ht1 hgt
  have h' := hshift'.mono_of_mem_nhdsWithin hmem
  simpa [extendSol, shiftSol, not_le_of_gt hgt] using h'

private theorem extend_hasDerivWithinAt_mid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {t₀ δ : ℝ} {sol step : ℝ → E}
    (ht0 : 0 ≤ t₀) (hδ : 0 < δ)
    (hsol : ∀ t ∈ Icc (0 : ℝ) t₀,
      HasDerivWithinAt sol (f (sol t)) (Icc (0 : ℝ) t₀) t)
    (hstep : ∀ t ∈ Icc (0 : ℝ) δ,
      HasDerivWithinAt step (f (step t)) (Icc (0 : ℝ) δ) t)
    (hstep0 : step 0 = sol t₀) :
    HasDerivWithinAt (extendSol t₀ sol step)
      (f ((extendSol t₀ sol step) t₀)) (Icc (0 : ℝ) (t₀ + δ)) t₀ := by
  -- Combine left and right derivatives at the join point.
  have hleft := hsol t₀ ⟨ht0, le_rfl⟩
  have hright := shift_hasDerivWithinAt hstep t₀ ⟨le_rfl, by linarith [hδ]⟩
  have hleft' :
      HasDerivWithinAt (extendSol t₀ sol step) (f ((extendSol t₀ sol step) t₀))
        (Icc (0 : ℝ) t₀) t₀ := by
    have hleft'' :=
      hleft.congr_of_mem (f₁ := extendSol t₀ sol step)
        (by
          intro s hs
          simp [extendSol, hs.2]) ⟨ht0, le_rfl⟩
    simpa [extendSol, le_rfl] using hleft''
  have hright' :
      HasDerivWithinAt (extendSol t₀ sol step) (f ((extendSol t₀ sol step) t₀))
        (Icc t₀ (t₀ + δ)) t₀ := by
    have hright'' :=
      hright.congr_of_mem (f₁ := extendSol t₀ sol step)
        (by
          intro s hs
          by_cases hle : s ≤ t₀
          · have hst : s = t₀ := by linarith [hs.1, hle]
            subst hst
            simp [extendSol, shiftSol, hstep0]
          · simp [extendSol, shiftSol, hle]) ⟨le_rfl, by linarith [hδ]⟩
    simpa [extendSol, shiftSol, hstep0, le_rfl] using hright''
  have hunion := hleft'.union hright'
  have hset : Icc (0 : ℝ) t₀ ∪ Icc t₀ (t₀ + δ) = Icc (0 : ℝ) (t₀ + δ) := by
    exact Icc_union_Icc_eq_Icc ht0 (by linarith [hδ])
  simpa [hset] using hunion

private theorem extend_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {t₀ δ : ℝ} {sol step : ℝ → E}
    (ht0 : 0 ≤ t₀) (hδ : 0 < δ)
    (hsol : ∀ t ∈ Icc (0 : ℝ) t₀,
      HasDerivWithinAt sol (f (sol t)) (Icc (0 : ℝ) t₀) t)
    (hstep : ∀ t ∈ Icc (0 : ℝ) δ,
      HasDerivWithinAt step (f (step t)) (Icc (0 : ℝ) δ) t)
    (hstep0 : step 0 = sol t₀)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (t₀ + δ)) :
    HasDerivWithinAt (extendSol t₀ sol step)
      (f ((extendSol t₀ sol step) t)) (Icc (0 : ℝ) (t₀ + δ)) t := by
  -- Dispatch to left, right, or the join point.
  by_cases hlt : t < t₀
  · exact extend_hasDerivWithinAt_left hδ hsol hstep hstep0 t ht hlt
  by_cases hgt : t₀ < t
  · exact extend_hasDerivWithinAt_right ht0 hδ hsol hstep hstep0 t ht hgt
  · have ht_eq : t = t₀ := by linarith
    subst ht_eq
    exact extend_hasDerivWithinAt_mid ht0 hδ hsol hstep hstep0

/-! ## Fixed-Step Chaining -/

/-- Restrict derivative to `Ici t` from an `Icc` interval. -/
private theorem derivWithin_Ici_of_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {T : ℝ} {sol : ℝ → E}
    (hderiv : ∀ t ∈ Icc 0 T, HasDerivWithinAt sol (f (sol t)) (Icc 0 T) t)
    (t : ℝ) (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt sol (f (sol t)) (Ici t) t := by
  -- Use `mono_of_mem_nhdsWithin` with `Icc_mem_nhdsGE_of_mem`.
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
  have h := hderiv t htIcc
  have hmem : Icc (0 : ℝ) T ∈ 𝓝[≥] t := Icc_mem_nhdsGE_of_mem ht
  exact h.mono_of_mem_nhdsWithin (by simpa using hmem)

/-- Restrict continuity to a shorter interval. -/
private theorem contOn_restrict
    {E : Type*} [TopologicalSpace E] {sol : ℝ → E} {T T' : ℝ}
    (hT : T ≤ T') (hcont : ContinuousOn sol (Icc 0 T')) :
    ContinuousOn sol (Icc 0 T) := by
  -- Use `ContinuousOn.mono` on the smaller interval.
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) T' := ⟨hs.1, le_trans hs.2 hT⟩
  exact (hcont s hs').mono (by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 hT⟩)

/-- Restrict derivative conditions to a shorter interval. -/
private theorem derivOn_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {sol : ℝ → E} {T T' : ℝ}
    (hT : T ≤ T')
    (hderiv : ∀ t ∈ Icc 0 T', HasDerivWithinAt sol (f (sol t)) (Icc 0 T') t) :
    ∀ s ∈ Ico 0 T, HasDerivWithinAt sol (f (sol s)) (Ici s) s := by
  -- Promote Icc-derivatives to Ici and shrink the interval.
  intro s hs
  have hs' : s ∈ Ico (0 : ℝ) T' := ⟨hs.1, lt_of_lt_of_le hs.2 hT⟩
  exact derivWithin_Ici_of_Icc hderiv s hs'

/-- Base case: one-step solution on [0, δ]. -/
private theorem lipschitz_chain_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E)
    (δ : ℝ) (hδ : 0 < δ) (hKδ : (K : ℝ) * δ < 1) :
    ∃ sol : ℝ → E,
      sol 0 = x₀ ∧
      ∀ t ∈ Icc 0 δ, HasDerivWithinAt sol (f (sol t)) (Icc 0 δ) t := by
  -- Use the fixed-step Picard-Lindelöf solution.
  simpa using lipschitz_step_exists hf δ hδ hKδ x₀

/-- Inductive step: extend a solution by one fixed step. -/
private theorem lipschitz_chain_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E)
    (δ : ℝ) (hδ : 0 < δ) (hKδ : (K : ℝ) * δ < 1) (n : Nat)
    (sol : ℝ → E) (hsol0 : sol 0 = x₀)
    (hsol : ∀ t ∈ Icc 0 ((n + 1 : ℝ) * δ),
      HasDerivWithinAt sol (f (sol t)) (Icc 0 ((n + 1 : ℝ) * δ)) t) :
    ∃ sol' : ℝ → E,
      sol' 0 = x₀ ∧
      ∀ t ∈ Icc 0 ((n + 2 : ℝ) * δ),
        HasDerivWithinAt sol' (f (sol' t)) (Icc 0 ((n + 2 : ℝ) * δ)) t := by
  -- Extend the solution by one step at time t₀ = (n+1)·δ.
  let t₀ : ℝ := (n + 1 : ℝ) * δ
  obtain ⟨step, hstep0, hstep⟩ := lipschitz_step_exists hf δ hδ hKδ (sol t₀)
  let sol' := extendSol t₀ sol step
  have ht0 : 0 ≤ t₀ := by
    have hn : 0 ≤ (↑n + 1 : ℝ) := by
      exact add_nonneg (Nat.cast_nonneg n) (by norm_num)
    simpa [t₀, Nat.cast_add, add_assoc, add_comm, add_left_comm] using
      mul_nonneg hn (le_of_lt hδ)
  have hsol0' : sol' 0 = x₀ := by simp [sol', extendSol, hsol0, ht0]
  have hderiv' : ∀ t ∈ Icc 0 (t₀ + δ),
      HasDerivWithinAt sol' (f (sol' t)) (Icc 0 (t₀ + δ)) t := by
    intro t ht
    exact extend_hasDerivWithinAt ht0 hδ hsol hstep hstep0 t ht
  have hlen : t₀ + δ = (n + 2 : ℝ) * δ := by ring
  refine ⟨sol', hsol0', ?_⟩
  intro t ht
  have ht' : t ∈ Icc 0 (t₀ + δ) := by simpa [hlen] using ht
  simpa [hlen] using hderiv' t ht'

/-- Chain fixed steps to cover `n+1` intervals of size δ. -/
private theorem lipschitz_chain_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E)
    (δ : ℝ) (hδ : 0 < δ) (hKδ : (K : ℝ) * δ < 1) :
    ∀ n : Nat, ∃ sol : ℝ → E,
      sol 0 = x₀ ∧
      ∀ t ∈ Icc 0 ((n + 1 : ℝ) * δ),
        HasDerivWithinAt sol (f (sol t)) (Icc 0 ((n + 1 : ℝ) * δ)) t := by
  -- Induct on the number of steps.
  intro n; induction n with
  | zero =>
      simpa using lipschitz_chain_base hf x₀ δ hδ hKδ
  | succ n ih =>
      obtain ⟨sol, hsol0, hsol⟩ := ih
      obtain ⟨sol', hsol'0, hderiv'⟩ :=
        lipschitz_chain_step hf x₀ δ hδ hKδ n sol hsol0 hsol
      refine ⟨sol', hsol'0, ?_⟩
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) ((n + 2 : ℝ) * δ) := by
        have hcast : (↑n + 1 + 1 : ℝ) = (n + 2 : ℝ) := by
          norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
        simpa [hcast] using ht
      have hderiv'' := hderiv' t ht'
      have hcast : (↑n + 1 + 1 : ℝ) = (n + 2 : ℝ) := by
        norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      simpa [hcast] using hderiv''

/-- **Uniform local existence for globally Lipschitz autonomous ODEs.**

    For globally Lipschitz f, Picard-Lindelöf gives a local solution on [-T, T]
    from any starting point. Uses `picard_lindelof_autonomous`. -/
theorem lipschitz_uniform_local_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E) :
    ∃ T > 0, ∃ sol : ℝ → E,
      sol 0 = x₀ ∧
      ContinuousOn sol (Icc (-T) T) ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt sol (f (sol t)) (Icc (-T) T) t := by
  -- Reuse the Picard-Lindelöf construction
  obtain ⟨T, hTpos, t₀, ht₀, _, _, _, hPL, hx₀_ball⟩ :=
    picard_lindelof_autonomous hf x₀
  obtain ⟨sol, hsol0, hsol_deriv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hx₀_ball
  exact ⟨T, hTpos, sol, by rw [show (0 : ℝ) = ↑t₀ from ht₀.symm]; exact hsol0,
    fun t ht => (hsol_deriv t ht).continuousWithinAt, hsol_deriv⟩

/-- **Finite-interval existence for globally Lipschitz autonomous ODEs.**

    For any T > 0, there exists a solution on [0, T] obtained by chaining
    finitely many local Picard-Lindelöf solutions. Each local solution has
    `HasDerivWithinAt` on its interval; uniqueness (Gronwall) ensures they
    agree on overlaps.
    
    This proof uses a **fixed step size** δ = 1/(2(K+1)), which works for
    any starting point by choosing a radius `a` satisfying `L·δ = a`. Then
    finitely many steps cover [0, T] by Archimedean choice of n. -/
private theorem lipschitz_interval_ode_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E)
    (T : ℝ) (hT : 0 < T) :
    ∃ sol : ℝ → E,
      sol 0 = x₀ ∧
      ContinuousOn sol (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt sol (f (sol t)) (Icc 0 T) t := by
  -- Chain fixed-step solutions to cover [0, T], then restrict.
  let δ : ℝ := odeStep K
  obtain ⟨hδ, hKδ⟩ := odeStep_pos (K := K)
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hnpos : 0 < n := by
    have hpos : (0 : ℝ) < T / δ := by exact div_pos hT hδ
    exact Nat.cast_pos.mp (lt_trans hpos hn)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  have hn' : T / δ < (m + 1 : ℝ) := by simpa [hm] using hn
  have hTle : T ≤ (m + 1 : ℝ) * δ := by
    have hTlt : T < (m + 1 : ℝ) * δ := (_root_.div_lt_iff₀ hδ).1 hn'
    exact le_of_lt hTlt
  obtain ⟨sol, hsol0, hderiv⟩ := lipschitz_chain_exists hf x₀ δ hδ hKδ m
  have hsubset : Icc 0 T ⊆ Icc 0 ((m + 1 : ℝ) * δ) := by
    intro t ht; exact ⟨ht.1, le_trans ht.2 hTle⟩
  have hcont : ContinuousOn sol (Icc 0 ((m + 1 : ℝ) * δ)) := by
    intro t ht; exact (hderiv t ht).continuousWithinAt
  refine ⟨sol, hsol0, hcont.mono hsubset, ?_⟩
  intro t ht
  exact (hderiv t (hsubset ht)).mono hsubset

/-- **Solutions on nested intervals agree** (Gronwall uniqueness).

    If sol₁ on [0, T₁] and sol₂ on [0, T₂] both solve the same Lipschitz
    ODE with the same initial condition, they agree on [0, min T₁ T₂]. -/
private theorem lipschitz_interval_ode_unique_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    {T₁ T₂ : ℝ}
    {sol₁ sol₂ : ℝ → E}
    (hcont₁ : ContinuousOn sol₁ (Icc 0 T₁))
    (hcont₂ : ContinuousOn sol₂ (Icc 0 T₂))
    (hderiv₁ : ∀ t ∈ Icc 0 T₁, HasDerivWithinAt sol₁ (f (sol₁ t)) (Icc 0 T₁) t)
    (hderiv₂ : ∀ t ∈ Icc 0 T₂, HasDerivWithinAt sol₂ (f (sol₂ t)) (Icc 0 T₂) t)
    (hinit : sol₁ 0 = sol₂ 0) :
    EqOn sol₁ sol₂ (Icc 0 (min T₁ T₂)) := by
  -- Apply Gronwall uniqueness on the restricted interval.
  let T := min T₁ T₂
  have hT1 : T ≤ T₁ := min_le_left _ _
  have hT2 : T ≤ T₂ := min_le_right _ _
  apply ODE_solution_unique (v := fun _ x => f x) (K := K)
  · intro _; exact hf
  · exact contOn_restrict hT1 hcont₁
  · exact derivOn_restrict hT1 hderiv₁
  · exact contOn_restrict hT2 hcont₂
  · exact derivOn_restrict hT2 hderiv₂
  · exact hinit

private theorem lipschitz_interval_ode_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    {T₁ T₂ : ℝ}
    {sol₁ sol₂ : ℝ → E}
    (hcont₁ : ContinuousOn sol₁ (Icc 0 T₁))
    (hcont₂ : ContinuousOn sol₂ (Icc 0 T₂))
    (hderiv₁ : ∀ t ∈ Icc 0 T₁, HasDerivWithinAt sol₁ (f (sol₁ t)) (Icc 0 T₁) t)
    (hderiv₂ : ∀ t ∈ Icc 0 T₂, HasDerivWithinAt sol₂ (f (sol₂ t)) (Icc 0 T₂) t)
    (hinit : sol₁ 0 = sol₂ 0)
    (t : ℝ) (ht₁ : t ∈ Icc 0 T₁) (ht₂ : t ∈ Icc 0 T₂) :
    sol₁ t = sol₂ t := by
  -- Use the restricted-interval uniqueness lemma.
  have hEq := lipschitz_interval_ode_unique_on hf hcont₁ hcont₂ hderiv₁ hderiv₂ hinit
  have htT : t ∈ Icc (0 : ℝ) (min T₁ T₂) := ⟨ht₁.1, le_min ht₁.2 ht₂.2⟩
  exact hEq htT

/-! ## Global Existence Helpers -/

/-- Negation preserves Lipschitz constants. -/
private theorem lipschitz_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x => -f x) := by
  -- Distances are preserved by negation.
  simpa [one_mul] using (LipschitzWith.id.neg.comp hf)

/-- Reverse a solution in time. -/
private def reverseSol {E : Type*} (sol : ℝ → E) : ℝ → E :=
  -- Map `t` to `-t`.
  fun t => sol (-t)

/-- Negation maps `[-T, 0]` to `[0, T]`. -/
private theorem reverse_mapsTo {T : ℝ} :
    MapsTo (fun t => -t) (Icc (-T) 0) (Icc (0 : ℝ) T) := by
  -- Flip the inequalities.
  intro t ht
  constructor
  · exact neg_nonneg.mpr ht.2
  · have : -t ≤ T := by linarith [ht.1]
    exact this

/-- Reverse-time derivative rule for autonomous ODEs. -/
private theorem reverse_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {T : ℝ} {sol : ℝ → E}
    (hsol : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt sol (-(f (sol t))) (Icc 0 T) t)
    (t : ℝ) (ht : t ∈ Icc (-T) 0) :
    HasDerivWithinAt (reverseSol sol) (f ((reverseSol sol) t)) (Icc (-T) 0) t := by
  -- Chain rule with the negation map.
  have ht' : -t ∈ Icc (0 : ℝ) T := reverse_mapsTo (T := T) ht
  have hderiv := hsol (-t) ht'
  have hneg : HasDerivWithinAt (fun t => -t) (-1 : ℝ) (Icc (-T) 0) t := by
    simpa using (hasDerivWithinAt_neg t (Icc (-T) 0))
  have hcomp := hderiv.scomp t hneg (reverse_mapsTo (T := T))
  simpa [reverseSol, smul_neg, neg_smul, one_smul] using hcomp

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E)

/-- Chosen positive-time solution on `[0, T]`. -/
private noncomputable def posSol (T : ℝ) (hT : 0 < T) : ℝ → E :=
  -- Choose a Lipschitz interval solution.
  (lipschitz_interval_ode_exists (f := f) (K := K) hf x₀ T hT).choose

/-- Initial condition for the chosen positive-time solution. -/
private theorem posSol_init {T : ℝ} (hT : 0 < T) :
    posSol (hf := hf) (x₀ := x₀) T hT 0 = x₀ := by
  -- Unpack the choice witness.
  have h := (lipschitz_interval_ode_exists (f := f) (K := K) hf x₀ T hT).choose_spec
  simpa [posSol] using h.1

/-- Continuity for the chosen positive-time solution. -/
private theorem posSol_cont {T : ℝ} (hT : 0 < T) :
    ContinuousOn (posSol (hf := hf) (x₀ := x₀) T hT) (Icc 0 T) := by
  -- Use the continuity part of the witness.
  have h := (lipschitz_interval_ode_exists (f := f) (K := K) hf x₀ T hT).choose_spec
  simpa [posSol] using h.2.1

/-- Derivative property for the chosen positive-time solution. -/
private theorem posSol_deriv {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (posSol (hf := hf) (x₀ := x₀) T hT)
        (f ((posSol (hf := hf) (x₀ := x₀) T hT) t)) (Icc 0 T) t := by
  -- Use the derivative part of the witness.
  have h := (lipschitz_interval_ode_exists (f := f) (K := K) hf x₀ T hT).choose_spec
  simpa [posSol] using h.2.2

/-- Chosen negative-time solution for `x' = -f(x)` on `[0, T]`. -/
private noncomputable def negSol (T : ℝ) (hT : 0 < T) : ℝ → E :=
  -- Apply the interval existence theorem to `-f`.
  (lipschitz_interval_ode_exists (f := fun x => -f x) (K := K)
      (lipschitz_neg (hf := hf)) x₀ T hT).choose

/-- Initial condition for the chosen negative-time solution. -/
private theorem negSol_init {T : ℝ} (hT : 0 < T) :
    negSol (hf := hf) (x₀ := x₀) T hT 0 = x₀ := by
  -- Unpack the choice witness.
  have h := (lipschitz_interval_ode_exists (f := fun x => -f x) (K := K)
    (lipschitz_neg (hf := hf)) x₀ T hT).choose_spec
  simpa [negSol] using h.1

/-- Continuity for the chosen negative-time solution. -/
private theorem negSol_cont {T : ℝ} (hT : 0 < T) :
    ContinuousOn (negSol (hf := hf) (x₀ := x₀) T hT) (Icc 0 T) := by
  -- Use the continuity part of the witness.
  have h := (lipschitz_interval_ode_exists (f := fun x => -f x) (K := K)
    (lipschitz_neg (hf := hf)) x₀ T hT).choose_spec
  simpa [negSol] using h.2.1

/-- Derivative property for the chosen negative-time solution. -/
private theorem negSol_deriv {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (negSol (hf := hf) (x₀ := x₀) T hT)
        (-(f ((negSol (hf := hf) (x₀ := x₀) T hT) t))) (Icc 0 T) t := by
  -- Use the derivative part of the witness.
  have h := (lipschitz_interval_ode_exists (f := fun x => -f x) (K := K)
    (lipschitz_neg (hf := hf)) x₀ T hT).choose_spec
  simpa [negSol] using h.2.2

/-- Uniqueness of positive-time solutions on overlaps. -/
private theorem posSol_eq {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (t : ℝ) (ht₁ : t ∈ Icc 0 T₁) (ht₂ : t ∈ Icc 0 T₂) :
    posSol (hf := hf) (x₀ := x₀) T₁ hT₁ t =
    posSol (hf := hf) (x₀ := x₀) T₂ hT₂ t := by
  -- Apply uniqueness on the overlap interval.
  have hinit :
      posSol (hf := hf) (x₀ := x₀) T₁ hT₁ 0 =
      posSol (hf := hf) (x₀ := x₀) T₂ hT₂ 0 := by
    simp [posSol_init (hf := hf) (x₀ := x₀)]
  exact lipschitz_interval_ode_unique (f := f) (K := K) hf
    (posSol_cont (hf := hf) (x₀ := x₀) (T := T₁) (hT := hT₁))
    (posSol_cont (hf := hf) (x₀ := x₀) (T := T₂) (hT := hT₂))
    (posSol_deriv (hf := hf) (x₀ := x₀) (T := T₁) (hT := hT₁))
    (posSol_deriv (hf := hf) (x₀ := x₀) (T := T₂) (hT := hT₂))
    hinit t ht₁ ht₂

/-- Uniqueness of negative-time solutions on overlaps. -/
private theorem negSol_eq {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (t : ℝ) (ht₁ : t ∈ Icc 0 T₁) (ht₂ : t ∈ Icc 0 T₂) :
    negSol (hf := hf) (x₀ := x₀) T₁ hT₁ t =
    negSol (hf := hf) (x₀ := x₀) T₂ hT₂ t := by
  -- Apply uniqueness to the ODE with drift `-f`.
  have hinit :
      negSol (hf := hf) (x₀ := x₀) T₁ hT₁ 0 =
      negSol (hf := hf) (x₀ := x₀) T₂ hT₂ 0 := by
    simp [negSol_init (hf := hf) (x₀ := x₀)]
  exact lipschitz_interval_ode_unique (f := fun x => -f x) (K := K)
    (lipschitz_neg (hf := hf))
    (negSol_cont (hf := hf) (x₀ := x₀) (T := T₁) (hT := hT₁))
    (negSol_cont (hf := hf) (x₀ := x₀) (T := T₂) (hT := hT₂))
    (negSol_deriv (hf := hf) (x₀ := x₀) (T := T₁) (hT := hT₁))
    (negSol_deriv (hf := hf) (x₀ := x₀) (T := T₂) (hT := hT₂))
    hinit t ht₁ ht₂

/-- Global solution assembled from forward/backward solutions. -/
private noncomputable def globalSol (t : ℝ) : E :=
  -- Use forward solutions for `t ≥ 0` and reversed solutions for `t < 0`.
  if ht : 0 ≤ t then
    posSol (hf := hf) (x₀ := x₀) (t + 1) (by linarith) t
  else
    (reverseSol (negSol (hf := hf) (x₀ := x₀) (-t + 1)
      (by linarith [lt_of_not_ge ht]))) t

/-- The global solution matches the forward solution on `[0, T]`. -/
private theorem globalSol_eq_pos_on {T : ℝ} (hT : 0 < T) :
    EqOn (globalSol (hf := hf) (x₀ := x₀))
      (posSol (hf := hf) (x₀ := x₀) T hT) (Icc 0 T) := by
  -- Compare via uniqueness pointwise.
  intro t ht
  have hTt : 0 < t + 1 := by nlinarith [ht.1]
  have ht1 : t ∈ Icc 0 (t + 1) := ⟨ht.1, by linarith⟩
  have hEq := posSol_eq (hf := hf) (x₀ := x₀) (T₁ := t + 1) (T₂ := T) hTt hT t ht1 ht
  have hsol : globalSol (hf := hf) (x₀ := x₀) t =
      posSol (hf := hf) (x₀ := x₀) (t + 1) hTt t := by
    simp [globalSol, ht.1]
  exact hsol.trans hEq

/-- The global solution matches the reversed solution on `[-T, 0]`. -/
private theorem globalSol_eq_neg_on {T : ℝ} (hT : 0 < T) :
    EqOn (globalSol (hf := hf) (x₀ := x₀))
      (reverseSol (negSol (hf := hf) (x₀ := x₀) T hT)) (Icc (-T) 0) := by
  -- Compare via uniqueness for `-f`.
  intro t ht
  by_cases hpos : 0 ≤ t
  · have ht0 : t = 0 := le_antisymm ht.2 hpos
    subst ht0
    have hT1 : 0 < (1 : ℝ) := by linarith
    have h0 : (0 : ℝ) ∈ Icc 0 (1 : ℝ) := ⟨le_rfl, by linarith⟩
    have hEq := globalSol_eq_pos_on (hf := hf) (x₀ := x₀) (T := 1) hT1
    have hpos0 : globalSol (hf := hf) (x₀ := x₀) 0 =
        posSol (hf := hf) (x₀ := x₀) 1 hT1 0 := by
      simpa using hEq h0
    have hpos0' : posSol (hf := hf) (x₀ := x₀) 1 hT1 0 = x₀ :=
      posSol_init (hf := hf) (x₀ := x₀) (T := 1) (hT := hT1)
    have hneg0 : reverseSol (negSol (hf := hf) (x₀ := x₀) T hT) 0 = x₀ := by
      simpa [reverseSol] using
        (negSol_init (hf := hf) (x₀ := x₀) (T := T) (hT := hT))
    exact hpos0.trans (hpos0'.trans hneg0.symm)
  · have htlt : t < 0 := lt_of_not_ge hpos
    have hTt : 0 < -t + 1 := by linarith
    have ht1 : -t ∈ Icc 0 (-t + 1) := ⟨by linarith, by linarith⟩
    have ht' : -t ∈ Icc 0 T := reverse_mapsTo (T := T) ht
    have hEq := negSol_eq (hf := hf) (x₀ := x₀) (T₁ := -t + 1) (T₂ := T) hTt hT (-t) ht1 ht'
    have hsol : globalSol (hf := hf) (x₀ := x₀) t =
        (reverseSol (negSol (hf := hf) (x₀ := x₀) (-t + 1) hTt)) t := by
      simp [globalSol, hpos]
    have hEq' :
        (reverseSol (negSol (hf := hf) (x₀ := x₀) (-t + 1) hTt)) t =
        (reverseSol (negSol (hf := hf) (x₀ := x₀) T hT)) t := by
      simpa [reverseSol] using hEq
    exact hsol.trans hEq'

/-- Derivative on `[0, T]` for the global solution. -/
private theorem globalSol_deriv_pos {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (globalSol (hf := hf) (x₀ := x₀))
        (f ((globalSol (hf := hf) (x₀ := x₀)) t)) (Icc 0 T) t := by
  -- Transfer the derivative from the forward solution.
  intro t ht
  have hEq := globalSol_eq_pos_on (hf := hf) (x₀ := x₀) (T := T) hT
  have hderiv := posSol_deriv (hf := hf) (x₀ := x₀) (T := T) (hT := hT) t ht
  have hderiv' := hderiv.congr_of_mem (fun s hs => hEq hs) ht
  simpa [hEq ht] using hderiv'

/-- Derivative on `[-T, 0]` for the global solution. -/
private theorem globalSol_deriv_neg {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc (-T) 0,
      HasDerivWithinAt (globalSol (hf := hf) (x₀ := x₀))
        (f ((globalSol (hf := hf) (x₀ := x₀)) t)) (Icc (-T) 0) t := by
  -- Transfer the derivative from the reversed solution.
  intro t ht
  have hEq := globalSol_eq_neg_on (hf := hf) (x₀ := x₀) (T := T) hT
  have hrev := reverse_hasDerivWithinAt (f := f) (T := T)
    (sol := negSol (hf := hf) (x₀ := x₀) T hT)
    (negSol_deriv (hf := hf) (x₀ := x₀) (T := T) (hT := hT)) t ht
  have hderiv' := hrev.congr_of_mem (fun s hs => hEq hs) ht
  simpa [hEq ht] using hderiv'

/-- Global differentiability for positive times. -/
private theorem globalSol_hasDerivAt_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt (globalSol (hf := hf) (x₀ := x₀))
      (f ((globalSol (hf := hf) (x₀ := x₀)) t)) t := by
  -- Use an interval containing `t` in its interior.
  have hT : 0 < t + 1 := by linarith
  have htIcc : t ∈ Icc (0 : ℝ) (t + 1) := ⟨le_of_lt ht, by linarith⟩
  have hwithin := globalSol_deriv_pos (hf := hf) (x₀ := x₀) (T := t + 1) hT t htIcc
  have hnhds : Icc (0 : ℝ) (t + 1) ∈ 𝓝 t := by
    exact Icc_mem_nhds ht (by linarith)
  exact hwithin.hasDerivAt hnhds

/-- Global differentiability for negative times. -/
private theorem globalSol_hasDerivAt_neg {t : ℝ} (ht : t < 0) :
    HasDerivAt (globalSol (hf := hf) (x₀ := x₀))
      (f ((globalSol (hf := hf) (x₀ := x₀)) t)) t := by
  -- Use an interval containing `t` in its interior.
  let T : ℝ := -t + 1
  have hT : 0 < T := by linarith [T]
  have htIcc : t ∈ Icc (-T) 0 := by
    constructor <;> linarith [T, ht]
  have hwithin := globalSol_deriv_neg (hf := hf) (x₀ := x₀) (T := T) hT t htIcc
  have hnhds : Icc (-T) 0 ∈ 𝓝 t := by
    exact Icc_mem_nhds (by linarith [T, ht]) ht
  exact hwithin.hasDerivAt hnhds

/-- Global differentiability at the origin. -/
private theorem globalSol_hasDerivAt_zero :
    HasDerivAt (globalSol (hf := hf) (x₀ := x₀))
      (f ((globalSol (hf := hf) (x₀ := x₀)) 0)) 0 := by
  -- Combine left and right derivatives on a neighborhood of 0.
  have hT : 0 < (1 : ℝ) := by linarith
  have hleft := globalSol_deriv_neg (hf := hf) (x₀ := x₀) (T := 1) hT 0 ⟨by linarith, le_rfl⟩
  have hright := globalSol_deriv_pos (hf := hf) (x₀ := x₀) (T := 1) hT 0 ⟨le_rfl, by linarith⟩
  have hunion := HasDerivWithinAt.union hleft hright
  have hnhds : Icc (-1 : ℝ) 0 ∪ Icc 0 1 ∈ 𝓝 (0 : ℝ) := by
    have hsmall : Icc (-1 / 2 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := by
      exact Icc_mem_nhds (by linarith) (by linarith)
    have hsubset : Icc (-1 / 2 : ℝ) (1 / 2) ⊆ Icc (-1 : ℝ) 0 ∪ Icc 0 1 := by
      intro t ht
      by_cases hpos : 0 ≤ t
      · right; exact ⟨hpos, by linarith [ht.2]⟩
      · left; exact ⟨by linarith [ht.1], le_of_lt (lt_of_not_ge hpos)⟩
    exact Filter.mem_of_superset hsmall hsubset
  exact hunion.hasDerivAt hnhds

end

/-- **Global existence for globally Lipschitz autonomous ODEs.**

    For any globally Lipschitz function f : E → E, the ODE dx/dt = f(x)
    has a unique global solution defined for all t ∈ ℝ.

    **Proof strategy**:
    1. `lipschitz_interval_ode_exists` gives solutions on [0, T] for any T
    2. `lipschitz_interval_ode_unique` shows they agree on overlaps
    3. Define sol(t) = the interval solution at t (well-defined by uniqueness)
    4. `HasDerivAt` at each t follows from `HasDerivWithinAt` on an interval
       containing t in its interior, via `HasDerivWithinAt.hasDerivAt` +
       `Icc_mem_nhds`. -/
theorem lipschitz_global_ode_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (x₀ : E) :
    ∃ sol : ℝ → E,
      sol 0 = x₀ ∧
      Continuous sol ∧
      ∀ t, HasDerivAt sol (f (sol t)) t := by
  -- For each t, get a solution on an interval containing both 0 and t
  -- All such solutions agree by Gronwall uniqueness
  -- Define sol(t) using the solution on [min 0 t - 1, max 0 t + 1]
  classical
  -- Assemble the global solution and its properties.
  let sol : ℝ → E := globalSol (hf := hf) (x₀ := x₀)
  have hsol0 : sol 0 = x₀ := by
    -- Use the forward solution on `[0, 1]`.
    have hT : 0 < (1 : ℝ) := by linarith
    have h0 : (0 : ℝ) ∈ Icc 0 (1 : ℝ) := ⟨le_rfl, by linarith⟩
    have hEq := globalSol_eq_pos_on (hf := hf) (x₀ := x₀) (T := 1) hT
    have hsol0' : sol 0 = posSol (hf := hf) (x₀ := x₀) 1 hT 0 := by
      simpa [sol] using hEq h0
    exact hsol0'.trans (posSol_init (hf := hf) (x₀ := x₀) (T := 1) (hT := hT))
  have hderiv : ∀ t, HasDerivAt sol (f (sol t)) t := by
    -- Split by sign of `t`.
    intro t
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have ht' : t < 0 := ht
      simpa [sol] using
        (globalSol_hasDerivAt_neg (hf := hf) (x₀ := x₀) (t := t) ht')
    · subst ht
      simpa [sol] using (globalSol_hasDerivAt_zero (hf := hf) (x₀ := x₀))
    · have ht' : 0 < t := ht
      simpa [sol] using
        (globalSol_hasDerivAt_pos (hf := hf) (x₀ := x₀) (t := t) ht')
  have hcont : Continuous sol := by
    -- Differentiability implies continuity.
    exact continuous_iff_continuousAt.mpr (fun t => (hderiv t).continuousAt)
  exact ⟨sol, hsol0, hcont, hderiv⟩

/-! ## Scalar Comparison Helpers -/

/-- Right derivative of the linear function `t ↦ ε * t`. -/
private theorem hasDerivWithinAt_linear (ε t : ℝ) :
    HasDerivWithinAt (fun s => ε * s) ε (Ici t) t := by
  -- Use the derivative of `id` and constant multiplication.
  simpa using (hasDerivWithinAt_id t (Ici t)).const_mul ε

/-- Right derivative of `t ↦ u t + ε * t`. -/
private theorem hasDerivWithinAt_u_add_linear
    {u u' : ℝ → ℝ} {T ε : ℝ}
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t) :
    ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => u s + ε * s) (u' t + ε) (Ici t) t := by
  -- Combine the derivative of `u` with the linear term.
  intro t ht
  have hlin := hasDerivWithinAt_linear ε t
  simpa [add_comm, add_left_comm, add_assoc] using (hderiv t ht).add hlin

/-- Right derivative of `t ↦ -(u t + ε * t)`. -/
private theorem hasDerivWithinAt_neg_u_add_linear
    {u u' : ℝ → ℝ} {T ε : ℝ}
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t) :
    ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => -(u s + ε * s)) (-(u' t + ε)) (Ici t) t := by
  -- Negate the derivative of the sum.
  intro t ht
  exact (hasDerivWithinAt_u_add_linear (T := T) (ε := ε) hderiv t ht).neg

/-- Continuity of `t ↦ u t + ε * t` on the interval. -/
private theorem continuousOn_u_add_linear
    {u : ℝ → ℝ} {T ε : ℝ} (hcont : ContinuousOn u (Icc 0 T)) :
    ContinuousOn (fun s => u s + ε * s) (Icc 0 T) := by
  -- Add continuity of `u` and the linear term.
  have hlin : ContinuousOn (fun s => ε * s) (Icc 0 T) :=
    (continuous_const.mul continuous_id).continuousOn
  simpa using hcont.add hlin

/-- Continuity of `t ↦ -(u t + ε * t)` on the interval. -/
private theorem continuousOn_neg_u_add_linear
    {u : ℝ → ℝ} {T ε : ℝ} (hcont : ContinuousOn u (Icc 0 T)) :
    ContinuousOn (fun s => -(u s + ε * s)) (Icc 0 T) := by
  -- Negation preserves continuity.
  simpa using (continuousOn_u_add_linear (T := T) (ε := ε) hcont).neg

/-! ## Component Bounds from Boundary Conditions -/

/-- Zero out a single coordinate in a vector. -/
private def zeroAt (x : Q → ℝ) (q : Q) : Q → ℝ :=
  -- Keep all other components, set `q` to 0.
  fun p => if p = q then 0 else x p

/-- The norm of `x - zeroAt x q` is bounded by `|x q|`. -/
private theorem norm_sub_zeroAt_le (x : Q → ℝ) (q : Q) :
    ‖x - zeroAt x q‖ ≤ |x q| := by
  -- Only the `q` coordinate changes, so the sup norm is `|x q|`.
  have hnonneg : 0 ≤ |x q| := abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg hnonneg).mpr ?_
  intro p
  by_cases hp : p = q
  · subst hp
    simp [zeroAt]
  · simp [zeroAt, hp]

/-- Lower bound on a component using boundary inwardness and Lipschitzness. -/
private theorem component_lower_bound_of_boundary
    {F : (Q → ℝ) → (Q → ℝ)} {K : ℝ≥0} (hLip : LipschitzWith K F)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ F x q)
    (x : Q → ℝ) (q : Q) (hxq : x q ≤ 0) :
    (K : ℝ) * x q ≤ F x q := by
  -- Compare `x` to a point with the `q`-coordinate zeroed out.
  let x' := zeroAt x q
  have hcomp : |F x q - F x' q| ≤ ‖F x - F x'‖ := by
    simpa [Real.norm_eq_abs, Pi.sub_apply] using (norm_le_pi_norm (F x - F x') q)
  have hLip' : ‖F x - F x'‖ ≤ (K : ℝ) * ‖x - x'‖ := by
    simpa [dist_eq_norm] using (hLip.dist_le_mul x x')
  have hlower : F x q ≥ F x' q - (K : ℝ) * ‖x - x'‖ := by
    -- Use the absolute-value bound to get a one-sided inequality.
    have h := le_trans hcomp hLip'
    have h' := (abs_sub_le_iff.mp h).2
    linarith
  have hboundary' : 0 ≤ F x' q := by
    -- Apply the boundary condition at the zeroed coordinate.
    have hx' : x' q = 0 := by simp [x', zeroAt]
    exact hboundary x' q hx'
  have hnorm : ‖x - x'‖ ≤ -x q := by
    have habs : |x q| = -x q := by simp [abs_of_nonpos hxq]
    simpa [x', habs] using (norm_sub_zeroAt_le x q)
  -- Use `K ≥ 0` to compare the lower bound to `K * x q`.
  have hK : 0 ≤ (K : ℝ) := K.property
  have hlower' : F x q ≥ -(K : ℝ) * ‖x - x'‖ := by linarith [hlower, hboundary']
  have hmul : (K : ℝ) * ‖x - x'‖ ≤ (K : ℝ) * (-x q) :=
    mul_le_mul_of_nonneg_left hnorm hK
  have hneg : -(K : ℝ) * (-x q) ≤ -(K : ℝ) * ‖x - x'‖ := by
    nlinarith [hmul]
  nlinarith [hlower', hneg]

/-- Barrier lemma: `u(t) ≥ -ε * t` for any `ε > 0`. -/
private theorem scalar_ge_neg_eps {u u' : ℝ → ℝ} {K T ε : ℝ}
    (hK : 0 ≤ K)
    (hcont : ContinuousOn u (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hu0 : 0 ≤ u 0)
    (hbound : ∀ t ∈ Ico 0 T, u t ≤ 0 → -K * u t ≤ u' t)
    (hε : 0 < ε) :
    ∀ t ∈ Icc 0 T, -ε * t ≤ u t := by
  -- Apply the fencing lemma to `f(t) = -(u t + ε t)` with barrier `0`.
  have hf : ContinuousOn (fun s => -(u s + ε * s)) (Icc 0 T) :=
    continuousOn_neg_u_add_linear (T := T) (ε := ε) hcont
  have hf' := hasDerivWithinAt_neg_u_add_linear (T := T) (ε := ε) hderiv
  have hB : ∀ x, HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := by
    intro x; simpa using (hasDerivAt_const (x := x) (c := (0 : ℝ)))
  have hbound' : ∀ t ∈ Ico 0 T, -(u t + ε * t) = 0 → -(u' t + ε) < 0 := by
    intro t ht hft
    have hux : u t = -ε * t := by nlinarith [hft]
    have huxle : u t ≤ 0 := by nlinarith [hux, hε, ht.1]
    have hder : -K * u t ≤ u' t := hbound t ht huxle
    have hu'nonneg : 0 ≤ u' t := by
      have hKux : 0 ≤ -K * u t := by nlinarith [hK, huxle]
      exact le_trans hKux hder
    have hpos : 0 < u' t + ε := by nlinarith [hu'nonneg, hε]
    have hneg : -(u' t + ε) < 0 := by nlinarith [hpos]
    simpa using hneg
  have hle :=
    image_le_of_deriv_right_lt_deriv_boundary (f := fun s => -(u s + ε * s))
      (f' := fun t => -(u' t + ε)) (a := 0) (b := T) hf hf'
      (by simpa using (neg_nonpos.mpr hu0)) hB hbound'
  intro t ht
  have hft := hle ht
  nlinarith [hft]

/-- **Component non-negativity via a barrier argument.**

    If `u(0) ≥ 0` and `u'(t) ≥ -K·u(t)` whenever `u(t) ≤ 0`, then `u(t) ≥ 0`
    for all `t ∈ [0, T]`. The proof uses the fencing lemma applied to the
    perturbed function `u(t) + ε t`. -/
theorem scalar_nonneg_of_gronwall {u u' : ℝ → ℝ} {K : ℝ} {T : ℝ}
    (hK : 0 ≤ K)
    (hcont : ContinuousOn u (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hu0 : 0 ≤ u 0)
    (hbound : ∀ t ∈ Ico 0 T, u t ≤ 0 → -K * u t ≤ u' t) :
    ∀ t ∈ Icc 0 T, 0 ≤ u t := by
  -- Use the barrier inequality and a contradiction argument.
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0; simpa using hu0
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  by_contra hneg
  have hneg' : u t < 0 := lt_of_not_ge hneg
  let ε : ℝ := (-u t) / (2 * t)
  have hε : 0 < ε := by
    have hnum : 0 < -u t := by nlinarith [hneg']
    have hden : 0 < 2 * t := by nlinarith [htpos]
    exact div_pos hnum hden
  have hle := scalar_ge_neg_eps (u := u) (u' := u') (K := K) (T := T)
    hK hcont hderiv hu0 hbound hε t ht
  have hcalc : -ε * t = u t / 2 := by
    dsimp [ε]
    field_simp [ht0]
  have : u t ≥ u t / 2 := by nlinarith [hle, hcalc]
  nlinarith [hneg', this]

/-- Derivative of `t ↦ exp(-K t)` on a right interval. -/
private theorem hasDerivWithinAt_exp_neg_mul (K t : ℝ) :
    HasDerivWithinAt (fun s => Real.exp (-(K * s)))
      (-K * Real.exp (-(K * t))) (Ici t) t := by
  -- Differentiate the exponential of a linear function.
  have hlin : HasDerivAt (fun s => -(K * s)) (-K) t := by
    -- The derivative of `s ↦ (-K) * s` is `-K`.
    simpa [neg_mul] using (hasDerivAt_const_mul (-K) (x := t))
  have h := (Real.hasDerivAt_exp (-(K * t))).comp t hlin
  have h' : HasDerivAt (fun s => Real.exp (-(K * s))) (-K * Real.exp (-(K * t))) t := by
    -- Move the scalar to the left of the product.
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  exact h'.hasDerivWithinAt

/-! ## Exponential Weighting for Inwardness -/

/-- Exponential reweighting used to remove the linear term. -/
private def expWeight (K : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  -- Use `exp(-K t)` as a positive weight.
  (fun s => Real.exp (-(K * s))) * u

/-- Continuity of the exponential weight. -/
private theorem expWeight_continuousOn {u : ℝ → ℝ} {K T : ℝ}
    (hcont : ContinuousOn u (Icc 0 T)) :
    ContinuousOn (expWeight K u) (Icc 0 T) := by
  -- Product of continuous functions on the interval.
  have hlin : Continuous fun s => -(K * s) := (continuous_const.mul continuous_id).neg
  have hexp : ContinuousOn (fun s => Real.exp (-(K * s))) (Icc 0 T) := by
    -- Continuity of exp composed with a linear map.
    exact (Real.continuous_exp.comp hlin).continuousOn
  simpa [expWeight, Pi.mul_apply] using hexp.mul hcont

/-- Derivative of the exponential weight on the right interval. -/
private theorem expWeight_hasDerivWithinAt {u u' : ℝ → ℝ} {K T : ℝ}
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t) :
    ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (expWeight K u)
        (Real.exp (-(K * t)) * (u' t - K * u t)) (Ici t) t := by
  -- Differentiate `exp(-K t) * u t`.
  intro t ht
  have hexp := hasDerivWithinAt_exp_neg_mul K t
  have hmul := hexp.mul (hderiv t ht)
  have hlin :
      -(K * Real.exp (-(K * t)) * u t) + Real.exp (-(K * t)) * u' t
        = Real.exp (-(K * t)) * (u' t - K * u t) := by ring
  -- Rewrite the derivative into the compact form.
  simpa [expWeight, Pi.mul_apply, hlin] using hmul

/-- Sign of `expWeight` matches the sign of the original function. -/
private theorem expWeight_le_zero_iff {u : ℝ → ℝ} {K : ℝ} {t : ℝ} :
    expWeight K u t ≤ 0 ↔ u t ≤ 0 := by
  -- `exp` is positive, so it does not change the sign.
  simp [expWeight, Pi.mul_apply]
  have hpos : 0 < Real.exp (-(K * t)) := Real.exp_pos _
  constructor
  · intro hwt
    by_contra hut
    -- If `u t > 0` then the product is positive.
    have hut' : 0 < u t := lt_of_not_ge hut
    have hmul : 0 < Real.exp (-(K * t)) * u t := mul_pos hpos hut'
    exact (not_le_of_gt hmul) hwt
  · intro hut
    have hpos' : 0 ≤ Real.exp (-(K * t)) := hpos.le
    exact mul_nonpos_of_nonneg_of_nonpos hpos' hut

/-- Sign of `expWeight` matches the sign of the original function. -/
private theorem expWeight_nonneg_iff {u : ℝ → ℝ} {K : ℝ} {t : ℝ} :
    0 ≤ expWeight K u t ↔ 0 ≤ u t := by
  -- `exp` is positive, so it does not change the sign.
  simp [expWeight, Pi.mul_apply]
  have hpos : 0 < Real.exp (-(K * t)) := Real.exp_pos _
  constructor
  · intro hwt
    have hcases := (mul_nonneg_iff.mp hwt)
    rcases hcases with ⟨_, hnonneg⟩ | ⟨hneg, _⟩
    · exact hnonneg
    · linarith
  · intro hut
    have hpos' : 0 ≤ Real.exp (-(K * t)) := hpos.le
    exact mul_nonneg hpos' hut

/-- Inwardness implies nonnegative derivative for the weighted function. -/
private theorem expWeight_deriv_nonneg_of_inward {u u' : ℝ → ℝ} {K T : ℝ}
    (hbound : ∀ t ∈ Ico 0 T, u t ≤ 0 → K * u t ≤ u' t) :
    ∀ t ∈ Ico 0 T, expWeight K u t ≤ 0 →
      0 ≤ Real.exp (-(K * t)) * (u' t - K * u t) := by
  -- Use inwardness and positivity of `exp`.
  intro t ht hw
  have hsign : u t ≤ 0 := (expWeight_le_zero_iff (u := u) (K := K) (t := t)).1 hw
  have hineq : 0 ≤ u' t - K * u t := by
    have := hbound t ht hsign
    nlinarith
  have hpos : 0 ≤ Real.exp (-(K * t)) := (Real.exp_pos _).le
  exact mul_nonneg hpos hineq

/-- Nonnegativity from inwardness using an exponential change of variables. -/
private theorem scalar_nonneg_of_inward {u u' : ℝ → ℝ} {K T : ℝ}
    (_hK : 0 ≤ K)
    (hcont : ContinuousOn u (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hu0 : 0 ≤ u 0)
    (hbound : ∀ t ∈ Ico 0 T, u t ≤ 0 → K * u t ≤ u' t) :
    ∀ t ∈ Icc 0 T, 0 ≤ u t := by
  -- Apply `scalar_nonneg_of_gronwall` to the weighted function.
  let w : ℝ → ℝ := expWeight K u
  have hcont_w := expWeight_continuousOn (u := u) (K := K) (T := T) hcont
  have hderiv_w := expWeight_hasDerivWithinAt (u := u) (u' := u') (K := K) (T := T) hderiv
  have hw0 : 0 ≤ w 0 := by
    -- At t = 0, the exponential weight is 1, so w 0 = u 0.
    simpa [w, expWeight] using hu0
  have hbound_w : ∀ t ∈ Ico 0 T, w t ≤ 0 →
      - (0 : ℝ) * w t ≤ Real.exp (-(K * t)) * (u' t - K * u t) := by
    -- Reduce to `expWeight_deriv_nonneg_of_inward`.
    intro t ht hw
    have hnonneg := expWeight_deriv_nonneg_of_inward (u := u) (u' := u') (K := K) (T := T) hbound t ht
    simpa [w] using hnonneg hw
  have hnonneg_w := scalar_nonneg_of_gronwall
    (u := w) (u' := fun t => Real.exp (-(K * t)) * (u' t - K * u t))
    (K := 0) (T := T) (by nlinarith) hcont_w hderiv_w hw0
    hbound_w
  intro t ht
  have hnonneg := hnonneg_w t ht
  exact (expWeight_nonneg_iff (u := u) (K := K) (t := t)).1 (by simpa [w] using hnonneg)

omit [Fintype Q] in
/-- Continuity of a single component. -/
private theorem component_continuousOn
    (sol : ℝ → (Q → ℝ)) (hcont : Continuous sol) (q : Q) (t : ℝ) :
    ContinuousOn (fun s => sol s q) (Icc 0 t) := by
  -- Component continuity follows from continuity of `sol`.
  have hcont' : Continuous (fun s => sol s q) := (continuous_apply q).comp hcont
  exact hcont'.continuousOn

/-- Derivative of a single component on the right interval. -/
private theorem component_hasDerivWithinAt
    (C : MeanFieldChoreography Q) (sol : ℝ → (Q → ℝ))
    (hderiv : ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t)
    (q : Q) (t : ℝ) :
    ∀ s ∈ Ico 0 t,
      HasDerivWithinAt (fun u => sol u q) (C.drift (sol s) q) (Ici s) s := by
  -- Restrict the full derivative to a component.
  intro s hs
  have h := hderiv s hs.1
  let proj : (Q → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (ι := Q) (φ := fun _ => ℝ) q
  have hcompF : HasFDerivAt (fun u => proj (sol u))
      (proj.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (C.drift (sol s)))) s := by
    -- Compose the Frechet derivatives of `proj` and `sol`.
    simpa using (proj.hasFDerivAt.comp s h.hasFDerivAt)
  have hcomp :
      HasDerivAt (fun u => sol u q) (C.drift (sol s) q) s := by
    -- Convert to `HasDerivAt` and simplify the derivative at `1`.
    have hcomp' := hcompF.hasDerivAt
    simpa [proj, ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply] using hcomp'
  exact hcomp.hasDerivWithinAt

/-- A single component remains nonnegative under boundary inwardness. -/
private theorem component_nonneg_of_boundary
    (C : MeanFieldChoreography Q) (sol : ℝ → (Q → ℝ)) {K : ℝ≥0}
    (hLip : LipschitzWith K C.drift)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.drift x q)
    (hx₀ : sol 0 ∈ Simplex Q) (hcont : Continuous sol)
    (hderiv : ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t)
    (q : Q) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ sol t q := by
  -- Reduce to the scalar inwardness lemma on `[0, t]`.
  by_cases ht0 : t = 0
  · subst ht0; exact hx₀.1 q
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hcont_q := component_continuousOn sol hcont q t
  have hderiv_q := component_hasDerivWithinAt C sol hderiv q t
  have hbound : ∀ s ∈ Ico 0 t, (sol s q) ≤ 0 →
      (K : ℝ) * (sol s q) ≤ C.drift (sol s) q := by
    -- Use boundary inwardness and Lipschitzness.
    intro s _ hsq
    exact component_lower_bound_of_boundary hLip hboundary (sol s) q hsq
  have hK : 0 ≤ (K : ℝ) := K.property
  have hnonneg := scalar_nonneg_of_inward
    (u := fun s => sol s q) (u' := fun s => C.drift (sol s) q)
    (K := (K : ℝ)) (T := t)
    hK hcont_q hderiv_q (hx₀.1 q) hbound t ⟨le_of_lt htpos, le_rfl⟩
  simpa using hnonneg

/-- **Simplex forward-invariance** for conservative drift with boundary inwardness.

    If drift conserves probability and pushes inward at the boundary,
    then the ODE solution stays in the simplex for all t ≥ 0.

    **Proof structure**:
    1. **Sum = 1**: `sum_preserved` shows ∑ sol(t)_q = 1 for all t
    2. **Non-negativity**: For each q, `scalar_nonneg_of_inward` shows
       sol(t)(q) ≥ 0 using boundary inwardness + Lipschitzness

    The non-negativity step uses `scalar_nonneg_of_inward`. -/
theorem simplex_forward_invariant
    (C : MeanFieldChoreography Q) (sol : ℝ → (Q → ℝ)) {K : ℝ≥0}
    (hLip : LipschitzWith K C.drift)
    (hcons : ∀ x, ∑ q, C.drift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.drift x q)
    (hx₀ : sol 0 ∈ Simplex Q) (hcont : Continuous sol)
    (hderiv : ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t) :
    ∀ t ≥ 0, sol t ∈ Simplex Q := by
  -- Combine global sum conservation with component nonnegativity.
  intro t ht
  have hsum : ∑ q, sol t q = ∑ q, sol 0 q := by
    exact sum_preserved_of_conserves_all C sol hcont hderiv hcons t ht
  have hsum1 : ∑ q, sol t q = 1 := by simpa [hx₀.2] using hsum
  have hnonneg : ∀ q, 0 ≤ sol t q := by
    intro q
    exact component_nonneg_of_boundary C sol hLip hboundary hx₀ hcont hderiv q t ht
  exact ⟨hnonneg, hsum1⟩

/-! ## Extended Drift Helpers -/

/-- The extended drift is Lipschitz on the simplex with the NNReal constant. -/
private theorem extendDrift_isLipschitz (C : MeanFieldChoreography Q) :
    DriftFunction.IsLipschitz C.extendDrift (C.lipschitzConstNNReal : ℝ) := by
  -- Use global Lipschitzness and restrict to the simplex.
  intro x y _ _
  simpa [dist_eq_norm] using (C.extendDrift_lipschitz.dist_le_mul x y)

/-- The extended drift conserves probability on the simplex. -/
private theorem extendDrift_conserves (C : MeanFieldChoreography Q) :
    DriftFunction.Conserves C.extendDrift := by
  -- Reduce to the original drift on the simplex.
  intro x hx
  simpa [C.extendDrift_apply x hx] using C.drift_conserves x hx

/-- The extended drift is inward-pointing on the simplex boundary. -/
private theorem extendDrift_boundary_nonneg (C : MeanFieldChoreography Q) :
    ∀ x ∈ Simplex Q, ∀ q, x q = 0 → 0 ≤ C.extendDrift x q := by
  -- Reduce to the original drift on the simplex.
  intro x hx q hq
  simpa [C.extendDrift_apply x hx] using C.boundary_nonneg x hx q hq

/-- The choreography using the extended drift. -/
private def extendChoreo (C : MeanFieldChoreography Q) : MeanFieldChoreography Q :=
  -- Package the extended drift with inherited properties.
  { drift := C.extendDrift
    drift_lipschitz := ⟨(C.lipschitzConstNNReal : ℝ), extendDrift_isLipschitz C⟩
    drift_conserves := extendDrift_conserves C
    boundary_nonneg := extendDrift_boundary_nonneg C }

/-- Global existence for mean-field ODEs.

    Combines global existence for the extended drift (globally Lipschitz)
    with simplex forward-invariance (conservative drift). -/
theorem global_ode_exists [Nonempty Q] (C : MeanFieldChoreography Q)
    (x₀ : Q → ℝ) (hx₀ : x₀ ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) :
    ∃ sol : ℝ → (Q → ℝ),
      sol 0 = x₀ ∧
      Continuous sol ∧
      ∀ t ≥ 0, HasDerivAt sol (C.drift (sol t)) t ∧ sol t ∈ Simplex Q := by
  -- Step 1: Get global solution for the extended drift (globally Lipschitz)
  obtain ⟨sol, hsol0, hcont, hderiv⟩ :=
    lipschitz_global_ode_exists C.extendDrift_lipschitz x₀
  -- Step 2: Use simplex invariance for the extended drift.
  have hsimplex : ∀ t ≥ 0, sol t ∈ Simplex Q := by
    -- Apply simplex invariance to the extended choreography.
    have hx0' : sol 0 ∈ Simplex Q := by simpa [hsol0] using hx₀
    have hLip : LipschitzWith C.lipschitzConstNNReal (extendChoreo C).drift := by
      -- Use global Lipschitzness of the extended drift.
      simpa [extendChoreo] using C.extendDrift_lipschitz
    exact simplex_forward_invariant (C := extendChoreo C) (K := C.lipschitzConstNNReal)
      sol hLip hcons hboundary hx0' hcont
      (fun t ht => by simpa using hderiv t)
  -- Step 3: On the simplex, extendDrift = drift.
  refine ⟨sol, hsol0, hcont, fun t ht => ?_⟩
  have hmem := hsimplex t ht
  have hderiv' : HasDerivAt sol (C.drift (sol t)) t := by
    -- Rewrite the extended drift on simplex.
    simpa [C.extendDrift_apply _ hmem] using hderiv t
  exact ⟨hderiv', hmem⟩

/-! ## The Canonical ODE Solution -/

/-- The canonical ODE solution for a choreography. -/
def MeanFieldChoreography.solution [Nonempty Q] (C : MeanFieldChoreography Q)
    (x₀ : Q → ℝ) (hx₀ : x₀ ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) : ℝ → (Q → ℝ) :=
  -- Choose the global solution from the existence theorem.
  (global_ode_exists C x₀ hx₀ hcons hboundary).choose

/-- The solution satisfies the initial condition. -/
theorem MeanFieldChoreography.solution_init [Nonempty Q] (C : MeanFieldChoreography Q)
    (x₀ : Q → ℝ) (hx₀ : x₀ ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) :
    C.solution x₀ hx₀ hcons hboundary 0 = x₀ :=
  -- Unpack the chosen solution's initial condition.
  (global_ode_exists C x₀ hx₀ hcons hboundary).choose_spec.1

/-- The solution is continuous. -/
theorem MeanFieldChoreography.solution_continuous [Nonempty Q] (C : MeanFieldChoreography Q)
    (x₀ : Q → ℝ) (hx₀ : x₀ ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q) :
    Continuous (C.solution x₀ hx₀ hcons hboundary) :=
  -- Continuity is part of the existence package.
  (global_ode_exists C x₀ hx₀ hcons hboundary).choose_spec.2.1

/-- The solution satisfies the ODE. -/
theorem MeanFieldChoreography.solution_hasDerivAt [Nonempty Q] (C : MeanFieldChoreography Q)
    (x₀ : Q → ℝ) (hx₀ : x₀ ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q)
    (t : ℝ) (ht : t ≥ 0) :
    HasDerivAt (C.solution x₀ hx₀ hcons hboundary)
      (C.drift (C.solution x₀ hx₀ hcons hboundary t)) t :=
  -- The chosen solution satisfies the ODE on ℝ≥0.
  ((global_ode_exists C x₀ hx₀ hcons hboundary).choose_spec.2.2 t ht).1

/-- The solution stays in the simplex. -/
theorem MeanFieldChoreography.solution_mem_simplex [Nonempty Q] (C : MeanFieldChoreography Q)
    (x₀ : Q → ℝ) (hx₀ : x₀ ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q)
    (t : ℝ) (ht : t ≥ 0) :
    C.solution x₀ hx₀ hcons hboundary t ∈ Simplex Q :=
  -- The invariant guarantees simplex membership for all times.
  ((global_ode_exists C x₀ hx₀ hcons hboundary).choose_spec.2.2 t ht).2

end

end Gibbs.MeanField
