import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Gibbs.MeanField.Universality
import Gibbs.Hamiltonian.EnergyGap
import Gibbs.Consensus.Gap
import Gibbs.Consensus.InteractiveDistance
import Mathlib.Order.LiminfLimsup

/-!
# Universality classes of consensus protocols

Protocols fall into universality classes determined by macroscopic gap behavior,
not by their microscopic message-passing details.

- **Class I (gapless/critical):** No energy gap between agreement and
  disagreement. Competing histories coexist and reorganizations are always
  possible. Nakamoto consensus lives here.
- **Class II (gapped/ordered):** Positive energy gap creates a barrier between
  phases. Once decided, alternative histories are thermodynamically forbidden.
  BFT protocols with quorum intersection live here.
- **Class III (hybrid):** Probabilistic finality with exponential suppression
  but no hard gap. Fast probabilistic agreement with BFT fallback.

The *thermodynamic gap* is the `liminf` of the normalized interactive distance
`(1/N) min Δ_H(Good, Bad)` as `N → ∞`. A positive thermodynamic gap at
corruption fraction `α < 1/3` characterizes the gapped (BFT) phase.
-/

namespace Gibbs.Consensus

open scoped ENNReal

noncomputable section

/-! ## Universality Classes -/

/-- Re-export the mean-field universality class type. -/
abbrev UniversalityClass : Type := Gibbs.MeanField.UniversalityClass

/-- Classifier for consensus protocols based on gap and tunneling flags. -/
def classOf (hasGap : Prop) (hasTunneling : Prop) : UniversalityClass := by
  -- Delegate to the mean-field classifier.
  exact Gibbs.MeanField.classOf hasGap hasTunneling

/-- A consensus system is gapped if it has a positive energy gap. -/
def IsGapped {Exec : Type} [Gibbs.Hamiltonian.EnergyDistance Exec]
    (A B : Set Exec) : Prop := by
  -- Use the physics-first gap notion.
  exact Gibbs.Hamiltonian.HasEnergyGap A B

/-! ## Thermodynamic Limit -/

/-- The per-size gap sequence induced by interactive distance. -/
def gapSequence {Exec : ℕ → Type} {M : ℕ → Type}
    (d : ∀ N, Exec N → Exec N → ℝ≥0∞)
    (dec : ∀ N, Exec N → M N)
    (Good Bad : ∀ N, Set (M N)) : ℕ → ℝ≥0∞ := by
  -- Take the infimum over good/bad macrostate pairs at each size.
  intro N
  exact sInf { r | ∃ m ∈ Good N, ∃ m' ∈ Bad N,
    r = interactiveDistance (d N) (dec N) m m' }

/-- Normalize a gap sequence by system size. -/
def normalizedGap (g : ℕ → ℝ≥0∞) (N : ℕ) : ℝ≥0∞ := by
  -- Divide by the system size as an `ℝ≥0∞` value.
  exact g N / (N : ℝ≥0∞)

/-- Thermodynamic-limit gap as the liminf of normalized gaps. -/
def thermodynamicGap (g : ℕ → ℝ≥0∞) : ℝ≥0∞ := by
  -- Use the filter liminf at infinity.
  exact Filter.liminf (fun N => normalizedGap g N) Filter.atTop

/-! ## Finite-N Lower Bounds Imply Thermodynamic Lower Bounds -/

/-- An eventual lower bound on normalized gaps lifts to the thermodynamic gap. -/
theorem thermodynamicGap_ge_of_eventually_ge {g : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ᶠ N in Filter.atTop, c ≤ normalizedGap g N) :
    c ≤ thermodynamicGap g := by
  exact (Filter.le_liminf_of_le (f := Filter.atTop)
    (u := fun N => normalizedGap g N) (a := c) (h := h))

end

end Gibbs.Consensus
