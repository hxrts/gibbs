import Mathlib.Data.ENNReal.Basic

/-
The Problem. We need a minimal, application-agnostic vocabulary for
phase classification that later consensus results can reference.

Solution Structure.
1. Define a small enumeration of universality classes.
2. Provide a simple classifier based on gap and tunneling flags.
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
