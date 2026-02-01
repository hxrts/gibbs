import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ENNReal.Basic
import Gibbs.Consensus.InteractiveDistance
import Gibbs.Consensus.TranscriptDistance

/-!
# Error-correcting codes as non-interactive consensus

An ECC is the degenerate case of interactive consensus: a single sender, one
round of communication (`T = 1`), and a memoryless channel. The "execution" is
just the received word, and the interactive distance between codewords reduces
to ordinary Hamming distance. Unique decoding within radius `t` corresponds to
the safety gap condition `Δ > f` with `f = t`.

This bridge makes the coding theory / consensus unification structural rather
than just an analogy. Any theorem about interactive distance specializes to a
theorem about code distance when the interaction is trivial.
-/

namespace Gibbs.Consensus

open scoped ENNReal

noncomputable section

/-! ## Coding Bridge -/

/-- A block code encoder. -/
structure Encoder (M α : Type) where
  /-- Encode a message into a codeword. -/
  encode : M → α

/-- A block code decoder. -/
structure Decoder (M α : Type) where
  /-- Decode a received word into a message (if possible). -/
  decode : α → Option M

/-- Unique decoding within radius `t` around each codeword. -/
def UniqueDecoding {M α : Type} (d : α → α → ℝ≥0∞)
    (E : Encoder M α) (D : Decoder M α) (t : ℝ≥0∞) : Prop := by
  -- All words within radius `t` decode to the original message.
  exact ∀ m, ∀ y, d (E.encode m) y ≤ t → D.decode y = some m

/-- Trivial decoder induced by a decision map on words. -/
def decoderOf {α M : Type} (dec : α → M) : Decoder M α := by
  -- Always decode to the chosen value.
  exact ⟨fun y => some (dec y)⟩

/-- Interactive distance specialized to the non-interactive case. -/
def interactiveDistanceWord {α M : Type} (d : α → α → ℝ≥0∞)
    (dec : α → M) (m m' : M) : ℝ≥0∞ := by
  -- Use `interactiveDistance` with executions = words.
  exact interactiveDistance d dec m m'

end

end Gibbs.Consensus
