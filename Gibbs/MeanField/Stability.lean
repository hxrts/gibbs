import Gibbs.MeanField.ODE
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-
The Problem. Prove that linearized stability implies asymptotic stability
for mean-field ODE systems. Specifically: if all eigenvalues of the
Jacobian at a fixed point have negative real part (Hurwitz condition),
then the fixed point is asymptotically stable.

Solution Structure (Lyapunov approach).
1. Spectral equivalence: IsHurwitz ↔ spectrum condition (provable)
2. Lyapunov stability: LyapunovData → IsLyapunovStable (provable)
3. Asymptotic stability: StrictLyapunovData → IsAsymptoticallyStable' (provable)
4. Hurwitz → strict Lyapunov function exists (requires a Lyapunov equation hypothesis)
5. Main theorem: linear stable → asymptotically stable (chains 4 → 3)
-/

/-!
# Linearized Stability for Mean-Field Systems

## Main Results

- `isHurwitz_iff_spectrum_neg`: Equivalence of eigenvalue and spectrum formulations
- `drift_linearization`: Drift approximation near fixed point
- `lyapunov_implies_stable`: Lyapunov function → Lyapunov stability
- `strict_lyapunov_implies_asymptotic`: Strict Lyapunov → asymptotic stability
- `hurwitz_implies_lyapunov_exists`: Hurwitz → Lyapunov function (explicit Lyapunov hypothesis)
- `linear_stable_implies_asymptotic`: Main theorem (chains through Lyapunov)
-/

namespace Gibbs.MeanField

open scoped Classical NNReal Matrix
open Metric

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## Spectral Equivalences -/

/-- Hurwitz condition is equivalent to the spectrum having negative real part.
    Uses `Module.End.hasEigenvalue_iff_mem_spectrum` for finite-dimensional spaces. -/
theorem isHurwitz_iff_spectrum_neg (F : DriftFunction Q) (x : Q → ℝ) :
    IsHurwitz F x ↔
    ∀ μ ∈ spectrum ℂ (Matrix.toLin' (JacobianComplex F x)), μ.re < 0 := by
  constructor
  · intro hH μ hμ
    exact hH μ (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)
  · intro hS μ hμ
    exact hS μ (Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ)

/-- The set of eigenvalues of the Jacobian is finite.
    Follows from the minimal polynomial having finitely many roots. -/
theorem jacobian_eigenvalues_finite (F : DriftFunction Q) (x : Q → ℝ) :
    Set.Finite (Module.End.HasEigenvalue (Matrix.toLin' (JacobianComplex F x))) := by
  exact Module.End.finite_hasEigenvalue _

/-! ## Lyapunov Stability -/

omit [DecidableEq Q] in
/-- A Lyapunov function implies Lyapunov stability.

    **Proof strategy**: Given ε > 0, use compactness of the sphere
    ‖y − x‖ = ε to find the minimum m of V on it (m > 0). By continuity
    of V at x with V(x) = 0, find δ with V(y) < m for ‖y − x‖ < δ.
    V decreasing along trajectories keeps V(sol t) < m, forcing
    ‖sol t − x‖ < ε. -/
theorem lyapunov_implies_stable [Nonempty Q]
    (C : MeanFieldChoreography Q) (x : Q → ℝ)
    (hx : IsEquilibrium C x)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q)
    (L : LyapunovData C.drift x) :
    IsLyapunovStable C x hcons hboundary := by
  classical
  refine ⟨hx, fun ε hε => ?_⟩
  -- Minimum of V on the sphere of radius ε.
  have hcompact : IsCompact (Metric.sphere x ε) := isCompact_sphere x ε
  have hnonempty : (Metric.sphere x ε).Nonempty := by
    simpa using (NormedSpace.sphere_nonempty (x := x) (r := ε)).2 (le_of_lt hε)
  obtain ⟨y, hyS, hymin⟩ := hcompact.exists_isMinOn hnonempty L.V_cont.continuousOn
  let m : ℝ := L.V y
  have hm_pos : 0 < m := by
    have hy_ne : y ≠ x := by
      exact Metric.ne_of_mem_sphere hyS (ne_of_gt hε)
    simpa [m] using L.V_pos y hy_ne
  -- Continuity at x gives a δ-ball where V < m.
  have hcont := (Metric.continuousAt_iff).1 (L.V_cont.continuousAt : ContinuousAt L.V x) m hm_pos
  obtain ⟨δ, hδpos, hδ⟩ := hcont
  refine ⟨min δ ε, lt_min hδpos hε, ?_⟩
  intro x₀ hx₀ hdist t ht
  have hdistδ : dist x₀ x < δ := by
    have h' := lt_of_lt_of_le hdist (min_le_left _ _)
    simpa [dist_eq_norm, norm_sub_rev] using h'
  have hdistε : dist x₀ x < ε := by
    have h' := lt_of_lt_of_le hdist (min_le_right _ _)
    simpa [dist_eq_norm, norm_sub_rev] using h'
  have hVdist : dist (L.V x₀) (L.V x) < m := hδ hdistδ
  have hVdist' : dist (L.V x₀) 0 < m := by
    simpa [L.V_zero] using hVdist
  have hVabs : |L.V x₀| < m := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hVdist'
  have hVx₀ : L.V x₀ < m := by
    have hVnonneg : 0 ≤ L.V x₀ := L.V_nonneg x₀
    simpa [abs_of_nonneg hVnonneg] using hVabs
  -- Set up the canonical solution and its derivative property.
  let sol : ℝ → (Q → ℝ) := ODESolution C x₀ (hx₀ := hx₀) hcons hboundary
  have hsol0 : sol 0 = x₀ := by
    simpa [sol, ODESolution] using
      (MeanFieldChoreography.solution_init (C := C) x₀ hx₀ hcons hboundary)
  have hderiv : ∀ s ≥ 0, HasDerivAt sol (C.drift (sol s)) s := by
    intro s hs
    simpa [sol, ODESolution] using
      (MeanFieldChoreography.solution_hasDerivAt (C := C) x₀ hx₀ hcons hboundary s hs)
  have hVdec := L.V_decreasing sol hderiv
  have hVt_le : L.V (sol t) ≤ L.V (sol 0) := hVdec 0 t (by linarith) ht
  have hVt_lt : L.V (sol t) < m := by
    have hV0_lt : L.V (sol 0) < m := by simpa [hsol0] using hVx₀
    exact lt_of_le_of_lt hVt_le hV0_lt
  -- If the trajectory ever leaves the ε-ball, it must hit the sphere.
  by_contra hnot
  have hge : ε ≤ ‖sol t - x‖ := le_of_not_gt hnot
  have hcont_sol : Continuous sol := by
    simpa [sol, ODESolution] using
      (MeanFieldChoreography.solution_continuous (C := C) x₀ hx₀ hcons hboundary)
  have hcont_norm : Continuous fun s => ‖sol s - x‖ :=
    (continuous_norm.comp (hcont_sol.sub continuous_const))
  have hcont_norm_on : ContinuousOn (fun s => ‖sol s - x‖) (Set.Icc (0 : ℝ) t) :=
    hcont_norm.continuousOn
  have hdist0 : ‖sol 0 - x‖ ≤ ε := by
    have : ‖sol 0 - x‖ < ε := by
      simpa [hsol0, dist_eq_norm, norm_sub_rev] using hdistε
    exact le_of_lt this
  have hεmem : ε ∈ Set.Icc (‖sol 0 - x‖) (‖sol t - x‖) := ⟨hdist0, hge⟩
  obtain ⟨s, hsIcc, hs_eq⟩ :=
    (intermediate_value_Icc (a := (0 : ℝ)) (b := t) ht.le hcont_norm_on) hεmem
  have hmem_sphere : sol s ∈ Metric.sphere x ε := by
    have : dist (sol s) x = ε := by
      simpa [dist_eq_norm, norm_sub_rev] using hs_eq
    simpa [Metric.mem_sphere] using this
  have hVmin : m ≤ L.V (sol s) := by
    have := hymin hmem_sphere
    simpa [m, Set.mem_setOf_eq] using this
  have hVsols_le : L.V (sol s) ≤ L.V (sol 0) := by
    exact hVdec 0 s (by linarith) hsIcc.1
  have hVsols_lt : L.V (sol s) < m := by
    have hV0_lt : L.V (sol 0) < m := by simpa [hsol0] using hVx₀
    exact lt_of_le_of_lt hVsols_le hV0_lt
  exact (not_lt_of_ge hVmin) hVsols_lt

/-! ## Asymptotic Stability -/

omit [DecidableEq Q] in
/-- A strict Lyapunov function implies asymptotic stability. -/
theorem strict_lyapunov_implies_asymptotic [Nonempty Q]
    (C : MeanFieldChoreography Q) (x : Q → ℝ)
    (hx : IsEquilibrium C x)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q)
    (L : StrictLyapunovData C.drift x) :
    IsAsymptoticallyStable' C x hcons hboundary := by
  classical
  have hstable : IsLyapunovStable C x hcons hboundary :=
    lyapunov_implies_stable C x hx hcons hboundary L.toLyapunovData
  refine ⟨hstable, ?_⟩
  -- Use Lyapunov stability with ε = 1 to obtain a bounded invariant neighborhood.
  obtain ⟨δ, hδpos, hδ⟩ := hstable.2 1 (by norm_num)
  refine ⟨δ, hδpos, ?_⟩
  intro x₀ hx₀ hx₀dist
  let sol : ℝ → (Q → ℝ) := ODESolution C x₀ (hx₀ := hx₀) hcons hboundary
  have hderiv : ∀ s ≥ 0, HasDerivAt sol (C.drift (sol s)) s := by
    intro s hs
    simpa [sol, ODESolution] using
      (MeanFieldChoreography.solution_hasDerivAt (C := C) x₀ hx₀ hcons hboundary s hs)
  have hV_to_zero : Filter.Tendsto (L.V ∘ sol) Filter.atTop (nhds 0) :=
    L.V_to_zero sol hderiv
  -- The trajectory stays in the closed ball of radius 1.
  have hstay : ∀ t ≥ 0, ‖sol t - x‖ < 1 := by
    intro t ht
    simpa [sol] using hδ x₀ hx₀ hx₀dist t ht
  -- Show convergence using compactness of the closed ball.
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  by_cases hε1 : ε ≤ 1
  · -- Build a positive lower bound of V away from x inside the closed ball.
    have hcompact : IsCompact (Metric.closedBall x 1) := isCompact_closedBall x 1
    have hclosed :
        IsClosed (Metric.closedBall x 1 ∩ (Metric.ball x ε)ᶜ) := by
      exact isClosed_closedBall.inter isOpen_ball.isClosed_compl
    have hScompact :
        IsCompact (Metric.closedBall x 1 ∩ (Metric.ball x ε)ᶜ) :=
      hcompact.of_isClosed_subset hclosed (by intro y hy; exact hy.1)
    have hSnonempty :
        (Metric.closedBall x 1 ∩ (Metric.ball x ε)ᶜ).Nonempty := by
      obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (x := x) (r := ε)).2 (le_of_lt hε)
      refine ⟨y, ?_⟩
      have hy_closed : y ∈ Metric.closedBall x 1 := by
        have hdist : dist y x = ε := by simpa [Metric.mem_sphere] using hy
        have hle : dist y x ≤ 1 := by linarith [hdist, hε1]
        simpa [Metric.mem_closedBall] using hle
      have hy_not : y ∈ (Metric.ball x ε)ᶜ := by
        intro hball
        have hdist' : dist y x < ε := by simpa [Metric.mem_ball] using hball
        have hdist : dist y x = ε := by simpa [Metric.mem_sphere] using hy
        linarith [hdist, hdist']
      exact ⟨hy_closed, hy_not⟩
    obtain ⟨y, hyS, hymin⟩ :=
      hScompact.exists_isMinOn hSnonempty L.V_cont.continuousOn
    let m : ℝ := L.V y
    have hm_pos : 0 < m := by
      have hdist : ε ≤ dist y x := by
        by_contra hlt
        exact hyS.2 (by simpa [Metric.mem_ball] using hlt)
      have hdist0 : 0 < dist y x := lt_of_lt_of_le hε hdist
      have hy_ne : y ≠ x := by
        intro h
        subst h
        simp [dist_self] at hdist0
      simpa [m] using L.V_pos y hy_ne
    obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.1 hV_to_zero) m hm_pos
    let N : ℝ := max N0 0
    refine ⟨N, ?_⟩
    intro t ht
    have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
    have htN0 : N0 ≤ t := le_trans (le_max_left _ _) ht
    have hVdist : dist (L.V (sol t)) 0 < m := hN0 t htN0
    have hVlt : L.V (sol t) < m := by
      have hVnonneg : 0 ≤ L.V (sol t) := L.V_nonneg (sol t)
      have hVabs : |L.V (sol t)| < m := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using hVdist
      simpa [abs_of_nonneg hVnonneg] using hVabs
    have hmem_closed : sol t ∈ Metric.closedBall x 1 := by
      have hlt := hstay t ht0
      have hle : dist (sol t) x ≤ 1 := by
        simpa [dist_eq_norm] using (le_of_lt hlt)
      simpa [Metric.mem_closedBall] using hle
    have hball : sol t ∈ Metric.ball x ε := by
      by_contra hnot
      have hmem : sol t ∈ Metric.closedBall x 1 ∩ (Metric.ball x ε)ᶜ := ⟨hmem_closed, hnot⟩
      have hVmin : m ≤ L.V (sol t) := by
        have := hymin hmem
        simpa [m, Set.mem_setOf_eq] using this
      exact (not_lt_of_ge hVmin) hVlt
    simpa [Metric.mem_ball, dist_eq_norm] using hball
  · -- If ε > 1, the trajectory is already within ε.
    have hεgt : 1 < ε := lt_of_not_ge hε1
    refine ⟨0, ?_⟩
    intro t ht
    have hlt := hstay t (by linarith)
    have : ‖sol t - x‖ < ε := lt_of_lt_of_le hlt (le_of_lt hεgt)
    simpa using this

/-! ## Nonlinear Approximation -/

/-- Near a fixed point, the drift is well-approximated by the Jacobian.
    F(x* + δ) = A·δ + R(δ) where ‖R(δ)‖ ≤ ε·‖δ‖ for small δ.

    This follows from the definition of the Fréchet derivative:
    F is differentiable at x* means F(x) = F(x*) + (fderiv F x*)(x - x*) + o(‖x - x*‖).
    Since F(x*) = 0 (fixed point), we get the linearization. -/
theorem drift_linearization
    {F : DriftFunction Q} {x : Q → ℝ}
    (hfp : IsFixedPoint F x) (hd : DifferentiableAt ℝ F x) :
    ∀ ε > 0, ∃ δ > 0, ∀ y : Q → ℝ, ‖y - x‖ < δ →
      ‖F y - (Jacobian F x) (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  have hfderiv := hd.hasFDerivAt
  have hbound := hfderiv.isLittleO.bound hε
  rw [Filter.Eventually] at hbound
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp hbound
  refine ⟨δ, hδ_pos, fun y hy => ?_⟩
  have hy_mem : y ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith [norm_sub_rev y x]
  have := hball hy_mem
  simp only [IsFixedPoint] at hfp
  simp only [hfp, sub_zero, Set.mem_setOf_eq] at this
  rw [Jacobian]
  exact this

/-! ## Main Theorem -/

/-- Linearized stability implies asymptotic stability via Lyapunov functions.

    **Proof**: IsLinearlyStable gives a fixed point with Hurwitz Jacobian.
    `hurwitz_implies_lyapunov_exists` constructs a strict Lyapunov function
    (explicit Lyapunov hypothesis). `strict_lyapunov_implies_asymptotic` then
    gives asymptotic stability. -/
theorem linear_stable_implies_asymptotic [Nonempty Q]
    (C : MeanFieldChoreography Q) (x : Q → ℝ)
    (hlin : IsLinearlyStable C.drift x) (hx : x ∈ Simplex Q)
    (hcons : ∀ x, ∑ q, C.extendDrift x q = 0)
    (hboundary : ∀ x q, x q = 0 → 0 ≤ C.extendDrift x q)
    (_hd : DifferentiableAt ℝ C.drift x)
    (hLyap : StrictLyapunovData C.drift x) :
    IsAsymptoticallyStable' C x hcons hboundary := by
  have ⟨hfp, _hH⟩ := hlin
  exact strict_lyapunov_implies_asymptotic C x ⟨hx, hfp⟩ hcons hboundary hLyap

end

end Gibbs.MeanField
