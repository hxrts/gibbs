import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

/-!
# Nakamoto consensus sketch

A Class I (gapless/critical) system. There is no hard energy gap between
competing chain histories, so reorganizations are always thermodynamically
possible. However, the probability of a reorg decays exponentially with
confirmation depth `k`, modelled here as `exp(-c·k)` for a protocol-
dependent rate `c > 0`.

This is "probabilistic finality" in the physics language: `ΔF = 0` but
the system is metastable, with the lifetime of the current consensus
growing exponentially in `k`. More confirmations lower the effective
temperature but never open a true gap.
-/

namespace Gibbs.Consensus.Examples

open scoped ENNReal

noncomputable section

/-! ## Nakamoto Sketch -/

/-- A gapless model has zero hard gap. -/
def gaplessGap : ℝ≥0∞ := 0

/-- Exponential reorg probability model with decay rate `c`. -/
def reorgProbability (c : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-c * (k : ℝ))

/-- The reorg probability decreases with confirmation depth when `c > 0`. -/
theorem reorgProbability_succ_le {c : ℝ} (hc : 0 < c) (k : ℕ) :
    reorgProbability c (k + 1) ≤ reorgProbability c k := by
  -- Compare exponents and use monotonicity of `exp`.
  have hk : (k : ℝ) ≤ (k + 1 : ℝ) := by
    exact_mod_cast (Nat.le_succ k)
  have hneg : (-c) ≤ 0 := by linarith
  have hexp : -c * (k + 1 : ℝ) ≤ -c * (k : ℝ) := by
    -- Multiply by a nonpositive constant flips the inequality.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonpos_left hk hneg)
  -- Apply `exp` to both sides.
  simpa [reorgProbability, mul_comm, mul_left_comm, mul_assoc] using
    (Real.exp_le_exp.mpr hexp)

end

end Gibbs.Consensus.Examples
