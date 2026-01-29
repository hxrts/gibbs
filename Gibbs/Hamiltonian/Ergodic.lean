import Gibbs.Hamiltonian.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Gibbs.Hamiltonian.GaussianIntegrals

/-
The Problem. We need a lightweight vocabulary for Gibbs measures
and ergodic time averages on configuration space. These definitions
should compile without additional assumptions so later proofs can
focus on dynamics rather than measure-theory boilerplate.

Solution Structure.
1. Fix a measurable structure on configuration space via the Borel σ-algebra.
2. Define partition functions, Gibbs densities, and Gibbs measures
   relative to a reference measure.
3. Define time/ensemble averages and a compact ergodicity statement.
-/

namespace Gibbs.Hamiltonian

noncomputable section

variable {n : ℕ}

/-! ## Measurable Structure -/

/-- Borel measurable space on configuration space (local to avoid instance diamonds). -/
local instance instMeasurableSpaceConfig : MeasurableSpace (Config n) := by
  -- Use the Borel σ-algebra from the Euclidean topology.
  exact borel (Config n)

/-! ## Gibbs Measure Ingredients -/

/-- A confining potential grows to infinity at infinity. -/
def IsConfining (V : Config n → ℝ) : Prop := by
  -- Use the cocompact filter to encode growth at infinity.
  exact Filter.Tendsto V (Filter.cocompact (Config n)) Filter.atTop

/-- Normalization constant (partition function). -/
noncomputable def partitionFunction (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) : ℝ := by
  -- Integrate the unnormalized density against the reference measure.
  exact ∫ q, Real.exp (-V q / kT) ∂μ

/-- Gibbs density function. -/
noncomputable def gibbsDensity (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (q : Config n) : ℝ := by
  -- Normalize the exponential weight by the partition function.
  exact Real.exp (-V q / kT) / partitionFunction V kT μ

/-- The partition function is nonnegative. -/
theorem partitionFunction_nonneg (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) : 0 ≤ partitionFunction V kT μ := by
  -- Apply `integral_nonneg` to the pointwise nonnegativity of the exponential.
  have hnonneg : 0 ≤ fun q => Real.exp (-V q / kT) := by
    -- The exponential function is nonnegative everywhere.
    intro q
    exact Real.exp_nonneg _
  simpa [partitionFunction] using (MeasureTheory.integral_nonneg hnonneg)

/-- Gibbs density is nonnegative pointwise. -/
theorem gibbsDensity_nonneg (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (q : Config n) :
    0 ≤ gibbsDensity V kT μ q := by
  -- Combine nonnegativity of the exponential with nonnegativity of the partition function.
  have hnum : 0 ≤ Real.exp (-V q / kT) := by
    -- Exponential is nonnegative.
    exact Real.exp_nonneg _
  have hden : 0 ≤ partitionFunction V kT μ := by
    -- Reuse the partition function bound.
    exact partitionFunction_nonneg (V := V) (kT := kT) (μ := μ)
  simpa [gibbsDensity] using (div_nonneg hnum hden)

/-- The Gibbs measure for potential V at temperature kT.
    This is meaningful when `kT > 0` and `V` is confining. -/
noncomputable def gibbsMeasure (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) : MeasureTheory.Measure (Config n) := by
  -- Use `withDensity` to scale the reference measure by the Gibbs density.
  exact MeasureTheory.Measure.withDensity μ
    (fun q => ENNReal.ofReal (gibbsDensity V kT μ q))

/-! ## Measurability and Integrability -/

/-- Gibbs density is measurable when the potential is measurable. -/
theorem measurable_gibbsDensity (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (hV : Measurable V) :
    Measurable (gibbsDensity V kT μ) := by
  -- Build measurability through composition and constant division.
  have hlin : Measurable fun q => -V q / kT := by
    -- Measurability is preserved by negation and division by a constant.
    exact (hV.neg).div_const kT
  have hexp : Measurable fun q => Real.exp (-V q / kT) := by
    -- Exponential is measurable and composes with a measurable input.
    exact Real.measurable_exp.comp hlin
  -- Normalize by the constant partition function.
  simpa [gibbsDensity] using (hexp.div_const (partitionFunction V kT μ))

/-- The `ENNReal` Gibbs density is measurable when the potential is measurable. -/
theorem measurable_gibbsDensity_ennreal (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (hV : Measurable V) :
    Measurable (fun q => ENNReal.ofReal (gibbsDensity V kT μ q)) := by
  -- Apply `ENNReal.ofReal` to a measurable real-valued function.
  exact (measurable_gibbsDensity (V := V) (kT := kT) (μ := μ) hV).ennreal_ofReal

/-- Gibbs density is a.e. measurable when the potential is measurable. -/
theorem aemeasurable_gibbsDensity (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (hV : Measurable V) :
    AEMeasurable (gibbsDensity V kT μ) μ := by
  -- Measurable functions are a.e. measurable.
  exact (measurable_gibbsDensity (V := V) (kT := kT) (μ := μ) hV).aemeasurable

/-- The `ENNReal` Gibbs density is a.e. measurable when the potential is measurable. -/
theorem aemeasurable_gibbsDensity_ennreal (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (hV : Measurable V) :
    AEMeasurable (fun q => ENNReal.ofReal (gibbsDensity V kT μ q)) μ := by
  -- Combine measurability with the `ENNReal.ofReal` map.
  exact (measurable_gibbsDensity_ennreal (V := V) (kT := kT) (μ := μ) hV).aemeasurable

/-- Gibbs density is integrable if the unnormalized weight is integrable. -/
theorem integrable_gibbsDensity (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n))
    (h : MeasureTheory.Integrable (fun q => Real.exp (-V q / kT)) μ) :
    MeasureTheory.Integrable (gibbsDensity V kT μ) μ := by
  -- Integrability is preserved by division by a constant.
  simpa [gibbsDensity] using h.div_const (partitionFunction V kT μ)

/-! ## Gibbs Density Normalization -/

/-- Integral of the Gibbs density in terms of the partition function. -/
theorem gibbsDensity_integral (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) :
    ∫ q, gibbsDensity V kT μ q ∂μ =
      partitionFunction V kT μ / partitionFunction V kT μ := by
  -- Pull out the constant denominator using linearity of the integral.
  have h :=
    (MeasureTheory.integral_div (μ := μ)
      (r := partitionFunction V kT μ) (fun q => Real.exp (-V q / kT)))
  -- Rewrite with the Gibbs density definition.
  simpa [gibbsDensity, partitionFunction] using h

/-- The Gibbs density integrates to one when the partition function is nonzero. -/
theorem gibbsDensity_integral_eq_one (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (hZ : partitionFunction V kT μ ≠ 0) :
    ∫ q, gibbsDensity V kT μ q ∂μ = 1 := by
  -- Replace by `Z / Z` and cancel.
  have h := gibbsDensity_integral (V := V) (kT := kT) (μ := μ)
  simpa [hZ] using (h.trans (div_self hZ))

/-! ## Partition Function Positivity -/

/-- The partition function is positive for nonzero measures and integrable weights. -/
theorem partitionFunction_pos (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) [NeZero μ]
    (hInt : MeasureTheory.Integrable (fun q => Real.exp (-V q / kT)) μ) :
    0 < partitionFunction V kT μ := by
  -- Apply positivity of the exponential integral.
  simpa [partitionFunction] using
    (MeasureTheory.integral_exp_pos (μ := μ) (f := fun q => -V q / kT) hInt)

/-- The partition function is nonzero under integrability and nontriviality. -/
theorem partitionFunction_ne_zero (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) [NeZero μ]
    (hInt : MeasureTheory.Integrable (fun q => Real.exp (-V q / kT)) μ) :
    partitionFunction V kT μ ≠ 0 := by
  -- Positivity implies nonzero.
  exact (partitionFunction_pos V kT μ hInt).ne'

/-- The Gibbs density integrates to one under integrability and nontriviality. -/
theorem gibbsDensity_integral_eq_one_of_integrable (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) [NeZero μ]
    (hInt : MeasureTheory.Integrable (fun q => Real.exp (-V q / kT)) μ) :
    ∫ q, gibbsDensity V kT μ q ∂μ = 1 := by
  -- Reduce to the nonzero partition function case.
  have hZ : partitionFunction V kT μ ≠ 0 :=
    partitionFunction_ne_zero (V := V) (kT := kT) (μ := μ) hInt
  exact gibbsDensity_integral_eq_one (V := V) (kT := kT) (μ := μ) hZ

/-! ## Gibbs Measure Normalization -/

/-- Total mass of the Gibbs measure equals the lintegral of its density. -/
theorem gibbsMeasure_univ (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) :
    gibbsMeasure V kT μ Set.univ =
      ∫⁻ q, ENNReal.ofReal (gibbsDensity V kT μ q) ∂μ := by
  -- Unfold `withDensity` at the whole space.
  simp [gibbsMeasure, MeasureTheory.withDensity_apply, MeasurableSet.univ]

/-- The Gibbs measure is a probability measure if its density integrates to one. -/
theorem gibbsMeasure_isProbability (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n))
    (hZ : ∫⁻ q, ENNReal.ofReal (gibbsDensity V kT μ q) ∂μ = 1) :
    MeasureTheory.IsProbabilityMeasure (gibbsMeasure V kT μ) := by
  -- Reduce to the `withDensity` mass of `univ`.
  refine ⟨?_⟩
  simpa [gibbsMeasure] using hZ

/-- The Gibbs density has unit lintegral when it is integrable and normalized. -/
theorem gibbsDensity_lintegral_eq_one (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n))
    (hInt : MeasureTheory.Integrable (gibbsDensity V kT μ) μ)
    (hZ : partitionFunction V kT μ ≠ 0) :
    ∫⁻ q, ENNReal.ofReal (gibbsDensity V kT μ q) ∂μ = 1 := by
  -- Convert the real integral to a lintegral using nonnegativity.
  have hnonneg : 0 ≤ᵐ[μ] gibbsDensity V kT μ := by
    exact MeasureTheory.ae_of_all _ (gibbsDensity_nonneg V kT μ)
  have hlin :
      ENNReal.ofReal (∫ q, gibbsDensity V kT μ q ∂μ) =
        ∫⁻ q, ENNReal.ofReal (gibbsDensity V kT μ q) ∂μ := by
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnonneg
  have hreal : ∫ q, gibbsDensity V kT μ q ∂μ = 1 := by
    exact gibbsDensity_integral_eq_one (V := V) (kT := kT) (μ := μ) hZ
  calc
    ∫⁻ q, ENNReal.ofReal (gibbsDensity V kT μ q) ∂μ
        = ENNReal.ofReal (∫ q, gibbsDensity V kT μ q ∂μ) := by
          exact hlin.symm
    _ = 1 := by
          simp [hreal]

/-- The Gibbs measure is a probability measure under integrability and normalization. -/
theorem gibbsMeasure_isProbability_of_integrable (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n))
    (hInt : MeasureTheory.Integrable (fun q => Real.exp (-V q / kT)) μ)
    (hZ : partitionFunction V kT μ ≠ 0) :
    MeasureTheory.IsProbabilityMeasure (gibbsMeasure V kT μ) := by
  -- Combine integrability with normalization of the Gibbs density.
  have hInt' : MeasureTheory.Integrable (gibbsDensity V kT μ) μ := by
    exact integrable_gibbsDensity (V := V) (kT := kT) (μ := μ) hInt
  have hmass :
      ∫⁻ q, ENNReal.ofReal (gibbsDensity V kT μ q) ∂μ = 1 := by
    exact gibbsDensity_lintegral_eq_one (V := V) (kT := kT) (μ := μ) hInt' hZ
  exact gibbsMeasure_isProbability (V := V) (kT := kT) (μ := μ) hmass

/-- The Gibbs measure is a probability measure under integrability and `μ ≠ 0`. -/
theorem gibbsMeasure_isProbability_of_integrable_nonzero (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) [NeZero μ]
    (hInt : MeasureTheory.Integrable (fun q => Real.exp (-V q / kT)) μ) :
    MeasureTheory.IsProbabilityMeasure (gibbsMeasure V kT μ) := by
  -- Obtain `partitionFunction ≠ 0` from positivity.
  have hZ : partitionFunction V kT μ ≠ 0 :=
    partitionFunction_ne_zero (V := V) (kT := kT) (μ := μ) hInt
  exact gibbsMeasure_isProbability_of_integrable (V := V) (kT := kT) (μ := μ) hInt hZ

/-- The Gibbs measure has unit mass under integrability and `μ ≠ 0`. -/
theorem gibbsMeasure_univ_eq_one_of_integrable_nonzero (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) [NeZero μ]
    (hInt : MeasureTheory.Integrable (fun q => Real.exp (-V q / kT)) μ) :
    gibbsMeasure V kT μ Set.univ = 1 := by
  -- Use the probability measure instance from integrability.
  have hprob : MeasureTheory.IsProbabilityMeasure (gibbsMeasure V kT μ) :=
    gibbsMeasure_isProbability_of_integrable_nonzero (V := V) (kT := kT) (μ := μ) hInt
  -- Extract the unit mass statement.
  let _ := hprob
  simp

/-! ## Time and Ensemble Averages -/

/-- A trajectory (stochastic process) over configuration space. -/
def StochasticProcess (n : ℕ) : Type := by
  -- Model a trajectory as a time-indexed configuration.
  exact ℝ → Config n

/-- Time average of an observable along a trajectory. -/
noncomputable def timeAverage (f : Config n → ℝ) (traj : StochasticProcess n) (T : ℝ) : ℝ := by
  -- Average the observable along the path over the time window [0, T].
  exact (1 / T) * ∫ t in Set.Icc 0 T, f (traj t)

/-- Ensemble average with respect to the Gibbs density. -/
noncomputable def ensembleAverage (f : Config n → ℝ) (V : Config n → ℝ)
    (kT : ℝ) (μ : MeasureTheory.Measure (Config n)) : ℝ := by
  -- Integrate the observable against the Gibbs density.
  exact ∫ q, f q * gibbsDensity V kT μ q ∂μ

/-- Ensemble averages are integrals against the Gibbs measure. -/
theorem ensembleAverage_eq_integral_gibbsMeasure (f : Config n → ℝ) (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (hV : Measurable V) :
    ensembleAverage f V kT μ = ∫ q, f q ∂(gibbsMeasure V kT μ) := by
  -- Use the `withDensity` formula for Bochner integrals.
  have hAe :
      AEMeasurable (fun q => ENNReal.ofReal (gibbsDensity V kT μ q)) μ := by
    exact aemeasurable_gibbsDensity_ennreal (V := V) (kT := kT) (μ := μ) hV
  have hTop :
      ∀ᵐ q ∂μ, ENNReal.ofReal (gibbsDensity V kT μ q) < ⊤ := by
    exact MeasureTheory.ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have h :=
    (integral_withDensity_eq_integral_toReal_smul₀
      (μ := μ) hAe hTop (g := f))
  -- Rewrite the right-hand side to match `ensembleAverage`.
  have hcongr :
      (fun q => (ENNReal.ofReal (gibbsDensity V kT μ q)).toReal • f q) =ᵐ[μ]
        fun q => f q * gibbsDensity V kT μ q := by
    refine MeasureTheory.ae_of_all _ (fun q => ?_)
    have hnonneg : 0 ≤ gibbsDensity V kT μ q :=
      gibbsDensity_nonneg (V := V) (kT := kT) (μ := μ) q
    simp [smul_eq_mul, ENNReal.toReal_ofReal hnonneg, mul_comm]
  have h' :
      ∫ q, f q ∂(gibbsMeasure V kT μ) =
        ∫ q, (ENNReal.ofReal (gibbsDensity V kT μ q)).toReal • f q ∂μ := by
    simpa [gibbsMeasure] using h
  calc
    ensembleAverage f V kT μ
        = ∫ q, f q * gibbsDensity V kT μ q ∂μ := by
          rfl
    _ = ∫ q, (ENNReal.ofReal (gibbsDensity V kT μ q)).toReal • f q ∂μ := by
          simpa using (MeasureTheory.integral_congr_ae hcongr).symm
    _ = ∫ q, f q ∂(gibbsMeasure V kT μ) := by
          simpa using h'.symm

/-- Integral of a constant over a closed interval with respect to volume. -/
theorem integral_const_Icc (c T : ℝ) :
    ∫ _ in Set.Icc (0 : ℝ) T, c =
      (MeasureTheory.volume (Set.Icc (0 : ℝ) T)).toReal * c := by
  -- Use the constant integral formula on the restricted measure.
  simp [MeasureTheory.measureReal_def, smul_eq_mul]

/-- Volume of a closed interval as a real number. -/
theorem volume_Icc_toReal {T : ℝ} (hT : 0 ≤ T) :
    (MeasureTheory.volume (Set.Icc (0 : ℝ) T)).toReal = T := by
  -- Use the standard formula for the Lebesgue measure of an interval.
  simp [Real.volume_Icc, hT, sub_zero]

/-- Time average of a constant observable over a positive interval. -/
theorem timeAverage_const (c : ℝ) (traj : StochasticProcess n) {T : ℝ} (hT : 0 < T) :
    timeAverage (fun _ => c) traj T = c := by
  -- Reduce to the constant integral and evaluate the interval volume.
  have hconst : ∫ _ in Set.Icc (0 : ℝ) T, c =
      (MeasureTheory.volume (Set.Icc (0 : ℝ) T)).toReal * c := by
    -- Reuse the constant integral lemma.
    simpa using integral_const_Icc c T
  have hvol : (MeasureTheory.volume (Set.Icc (0 : ℝ) T)).toReal = T := by
    -- Translate positivity of T into a volume computation.
    exact volume_Icc_toReal (T := T) (le_of_lt hT)
  have hTne : T ≠ 0 := by
    -- Nonzero follows from strict positivity.
    exact ne_of_gt hT
  calc
    timeAverage (fun _ => c) traj T
        = (1 / T) * ((MeasureTheory.volume (Set.Icc (0 : ℝ) T)).toReal * c) := by
          -- Expand the definition and plug in the constant integral.
          simp [timeAverage, hconst]
    _ = (1 / T) * (T * c) := by
          -- Replace the interval volume by its length.
          rw [hvol]
    _ = c := by
          -- Cancel the normalization factor.
          simpa [one_div] using (inv_mul_cancel_left₀ (a := T) (b := c) hTne)

/-- Ensemble average of a constant scales by the total mass of the density. -/
theorem ensembleAverage_const (c : ℝ) (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) :
    ensembleAverage (fun _ => c) V kT μ =
      c * ∫ q, gibbsDensity V kT μ q ∂μ := by
  -- Pull the constant outside the integral.
  have h :=
    (MeasureTheory.integral_const_mul (μ := μ) c
      (fun q => gibbsDensity V kT μ q))
  -- Rewrite the integrand to match `ensembleAverage`.
  simpa [ensembleAverage] using h

/-- Ensemble average of a constant is the constant when the density normalizes. -/
theorem ensembleAverage_const_eq (c : ℝ) (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) (hZ : partitionFunction V kT μ ≠ 0) :
    ensembleAverage (fun _ => c) V kT μ = c := by
  -- Use normalization of the Gibbs density.
  have hmass :=
    gibbsDensity_integral_eq_one (V := V) (kT := kT) (μ := μ) hZ
  calc
    ensembleAverage (fun _ => c) V kT μ
        = c * ∫ q, gibbsDensity V kT μ q ∂μ := by
          -- Pull out the constant.
          simpa using ensembleAverage_const c V kT μ
    _ = c * 1 := by
          -- Replace the integral by 1.
          simp [hmass]
    _ = c := by
          simp

/-- Ensemble average of a constant under integrability and nontriviality. -/
theorem ensembleAverage_const_eq_of_integrable (c : ℝ) (V : Config n → ℝ) (kT : ℝ)
    (μ : MeasureTheory.Measure (Config n)) [NeZero μ]
    (hInt : MeasureTheory.Integrable (fun q => Real.exp (-V q / kT)) μ) :
    ensembleAverage (fun _ => c) V kT μ = c := by
  -- Reduce to the normalized case via `partitionFunction ≠ 0`.
  have hZ : partitionFunction V kT μ ≠ 0 :=
    partitionFunction_ne_zero (V := V) (kT := kT) (μ := μ) hInt
  exact ensembleAverage_const_eq c V kT μ hZ

/-! ## Ergodicity Statement -/

/-- A process is ergodic if time averages converge to ensemble averages. -/
def IsErgodic (V : Config n → ℝ) (kT : ℝ) (μ : MeasureTheory.Measure (Config n))
    (processFamily : Config n → StochasticProcess n) : Prop := by
  -- Require convergence of time averages to the Gibbs ensemble average.
  exact ∀ (f : Config n → ℝ), Continuous f → MeasureTheory.Integrable f μ →
    ∀ q₀,
      Filter.Tendsto (fun T => timeAverage f (processFamily q₀) T)
        Filter.atTop (nhds (ensembleAverage f V kT μ))

end

end Gibbs.Hamiltonian
