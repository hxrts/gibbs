import Gibbs.Hamiltonian.Channel
import Gibbs.Hamiltonian.Stochastic.Basic
import Mathlib.Tactic

/-!
# Channel Noise and Temperature

Connects noise variance to inverse temperature and channel capacity.
-/

namespace Gibbs.Hamiltonian.Stochastic.ChannelNoise

noncomputable section

/-! ## Gaussian Channel -/

/-- Additive white Gaussian noise channel. -/
structure GaussianChannel where
  /-- Noise variance. -/
  variance : ℝ
  /-- Variance is positive. -/
  variance_pos : 0 < variance

/-- Gaussian channel capacity (nats). -/
def gaussianCapacity (gc : GaussianChannel) (P : ℝ) : ℝ :=
  (1/2) * Real.log (1 + P / gc.variance)

/-- Capacity is nonnegative when power is nonnegative. -/
theorem gaussianCapacity_nonneg (gc : GaussianChannel) (P : ℝ) (hP : 0 ≤ P) :
    0 ≤ gaussianCapacity gc P := by
  unfold gaussianCapacity
  have hfrac : 0 ≤ P / gc.variance :=
    div_nonneg hP (le_of_lt gc.variance_pos)
  have harg : 1 ≤ 1 + P / gc.variance := by linarith
  have hlog : 0 ≤ Real.log (1 + P / gc.variance) := Real.log_nonneg harg
  have hhalf : 0 ≤ (1/2 : ℝ) := by norm_num
  exact mul_nonneg hhalf hlog

/-- Capacity increases with power on nonnegative inputs. -/
theorem gaussianCapacity_monotone_power (gc : GaussianChannel) :
    MonotoneOn (gaussianCapacity gc) {P : ℝ | 0 ≤ P} := by
  intro P1 hP1 P2 hP2 hle
  unfold gaussianCapacity
  have hden : 0 < gc.variance := gc.variance_pos
  have hdiv : P1 / gc.variance ≤ P2 / gc.variance :=
    div_le_div_of_nonneg_right hle (le_of_lt hden)
  have harg : 1 + P1 / gc.variance ≤ 1 + P2 / gc.variance := by linarith
  have hpos1 : 0 < 1 + P1 / gc.variance := by
    have : 0 ≤ P1 / gc.variance := div_nonneg hP1 (le_of_lt hden)
    linarith
  have hpos2 : 0 < 1 + P2 / gc.variance := by
    have : 0 ≤ P2 / gc.variance := div_nonneg hP2 (le_of_lt hden)
    linarith
  have hlog : Real.log (1 + P1 / gc.variance) ≤ Real.log (1 + P2 / gc.variance) :=
    Real.log_le_log hpos1 harg
  have hhalf : 0 ≤ (1/2 : ℝ) := by norm_num
  exact mul_le_mul_of_nonneg_left hlog hhalf

/-- Capacity decreases with noise variance. -/
theorem gaussianCapacity_antitone_variance (P : ℝ) (hP : 0 < P) :
    Antitone (fun σ2 : { v : ℝ // 0 < v } => gaussianCapacity ⟨σ2.val, σ2.property⟩ P) := by
  intro a b hab
  have ha : 0 < a.val := a.property
  have hb : 0 < b.val := b.property
  have hrecip : (1 / b.val) ≤ (1 / a.val) :=
    one_div_le_one_div_of_le ha (by simpa using hab)
  have hdiv : P / b.val ≤ P / a.val := by
    have hPnonneg : 0 ≤ P := le_of_lt hP
    simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_left hrecip hPnonneg)
  have harg : 1 + P / b.val ≤ 1 + P / a.val := by linarith
  have hpos_a : 0 < 1 + P / a.val := by
    have : 0 ≤ P / a.val := div_nonneg (le_of_lt hP) (le_of_lt ha)
    linarith
  have hpos_b : 0 < 1 + P / b.val := by
    have : 0 ≤ P / b.val := div_nonneg (le_of_lt hP) (le_of_lt hb)
    linarith
  have hlog : Real.log (1 + P / b.val) ≤ Real.log (1 + P / a.val) :=
    Real.log_le_log hpos_b harg
  have hhalf : 0 ≤ (1/2 : ℝ) := by norm_num
  exact mul_le_mul_of_nonneg_left hlog hhalf

/-! ## Noise-Temperature Correspondence -/

/-- Convert noise variance to inverse temperature. -/
def noiseToInvTemp (gc : GaussianChannel) : ℝ := 1 / gc.variance

/-- Convert inverse temperature to noise variance. -/
def invTempToNoise (β : ℝ) (hβ : 0 < β) : GaussianChannel where
  variance := 1 / β
  variance_pos := by positivity

/-- Round-trip between temperature and noise. -/
theorem noiseToInvTemp_invTempToNoise (β : ℝ) (hβ : 0 < β) :
    noiseToInvTemp (invTempToNoise β hβ) = β := by
  unfold noiseToInvTemp invTempToNoise
  field_simp [hβ.ne']

/-- Capacity is monotone in inverse temperature. -/
theorem capacity_monotone_invTemp (P : ℝ) (hP : 0 < P) :
    Monotone (fun β : { v : ℝ // 0 < v } =>
      gaussianCapacity (invTempToNoise β.val β.property) P) := by
  intro β1 β2 hβ
  have hrecip : (1 / β2.val) ≤ (1 / β1.val) :=
    one_div_le_one_div_of_le β1.property (by simpa using hβ)
  have hanti := gaussianCapacity_antitone_variance P hP
  have hσ : (⟨1 / β2.val, by exact one_div_pos.mpr β2.property⟩ : { v : ℝ // 0 < v }) ≤
            (⟨1 / β1.val, by exact one_div_pos.mpr β1.property⟩ : { v : ℝ // 0 < v }) := by
    simpa using hrecip
  exact hanti hσ

/-! ## Fluctuation-Dissipation and Capacity -/

/-- Capacity at the fluctuation-dissipation point. -/
def langevinCapacity (γ β P : ℝ) (hγ : 0 < γ) (hβ : 0 < β) : ℝ :=
  gaussianCapacity ⟨2 * γ / β, by positivity⟩ P

end

end Gibbs.Hamiltonian.Stochastic.ChannelNoise
