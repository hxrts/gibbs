import Mathlib.Data.ENNReal.Basic

/-!
# Universality Classes

Systems with qualitatively similar macroscopic behavior belong to the same
universality class, regardless of microscopic details. Three classes cover the
main cases: gapless (no macroscopic barrier, critical behavior), gapped (a
finite barrier separating phases, ordered behavior), and hybrid (a barrier
exists but rare tunneling events can cross it).
-/

namespace Gibbs.MeanField

noncomputable section

/-! ## Universality Classes -/

/-- Coarse universality classes for macroscopic behavior. -/
inductive UniversalityClass
  | gapless   -- no macroscopic barrier
  | gapped    -- macroscopic barrier
  | hybrid    -- barrier with rare tunneling
  deriving DecidableEq, Repr

/-- Classify a system using gap and tunneling indicators. -/
def classOf (hasGap : Prop) (hasTunneling : Prop) : UniversalityClass := by
  -- A gap with tunneling is classified as hybrid; a gap without tunneling as gapped.
  by_cases hgap : hasGap
  · by_cases htun : hasTunneling
    · exact UniversalityClass.hybrid
    · exact UniversalityClass.gapped
  · exact UniversalityClass.gapless

end

end Gibbs.MeanField
