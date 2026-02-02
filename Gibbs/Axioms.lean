import Gibbs.Hamiltonian.Coding

/-!
# Axioms

This file collects all axioms in the Gibbs library. Every other result in the
codebase is proved from Lean's type theory and Mathlib. These two statements
are the only unproved assumptions.

Both axioms are components of **Shannon's noisy channel coding theorem** (1948).
Their proofs require probabilistic combinatorics (random codebook generation,
joint typicality, the method of types) that is far beyond current Mathlib
infrastructure. Formalizing either would be a major standalone project comparable
in scope to the Kepler conjecture formalization.

## Axiom inventory

| # | Statement                      | Origin                                        |
|---|--------------------------------|-----------------------------------------------|
| 1 | `channel_coding_achievability` | Shannon 1948, Feinstein 1954 (rigorous proof) |
| 2 | `channel_coding_converse`      | Wolfowitz 1957 (strong converse)              |

## What depends on them

The Hamiltonian facade (`Gibbs.Hamiltonian`) imports this file, making the
axioms available to downstream modules. They are used only in
`Gibbs.Consensus.ChannelThreshold` to prove `codingSafe_iff_positive_gap`,
that reliable communication at rate R is possible if and only if R < C(W).
Everything else in the library, including entropy inequalities,
Bregman/Legendre duality, channel capacity bounds, and consensus thresholds,
is proved without axioms.

## References

- Shannon, C. E. "A Mathematical Theory of Communication."
  *Bell System Technical Journal* 27, pp. 379-423, 623-656, 1948.
- Feinstein, A. "A New Basic Theorem of Information Theory."
  *IRE Trans. Inform. Theory* IT-4, pp. 2-22, 1954.
- Wolfowitz, J. "The Coding of Messages Subject to Chance Errors."
  *Illinois J. Math.* 1, pp. 591-606, 1957.
- Wolfowitz, J. *Coding Theorems of Information Theory.* Springer, 1961.
- Cover, T. M. and Thomas, J. A. *Elements of Information Theory.* 2nd ed.,
  Wiley, 2006. Theorems 7.7.1 (achievability) and 7.9 (weak converse).
- Csiszar, I. and Korner, J. *Information Theory: Coding Theorems for Discrete
  Memoryless Systems.* 2nd ed., Cambridge, 2011, Ch. 5 (strong converse).
- Polyanskiy, Y., Poor, H. V. and Verdu, S. "Channel Coding Rate in the
  Finite Blocklength Regime." *IEEE Trans. Inform. Theory* 56(5),
  pp. 2307-2359, 2010.
-/

namespace Gibbs.Axioms

noncomputable section

open Gibbs.Hamiltonian.Coding

/-! ## Noisy Channel Coding Theorem

Shannon's 1948 paper established that every DMC has a computable quantity C
(channel capacity) that sharply separates achievable from unachievable
communication rates. The theorem has two parts.

**Achievability** (direct part). For any rate R < C and any target error
probability epsilon > 0, there exist block codes at rate R whose average error
probability is at most epsilon, provided the blocklength is large enough.
Shannon's original argument used random coding. Feinstein (1954) gave the first
rigorous proof. The standard textbook proof (Cover and Thomas, Theorem 7.7.1)
draws codewords i.i.d. from the capacity-achieving input distribution and
decodes by joint typicality.

**Strong converse**. For any rate R >= C, every sequence of codes at rate R has
error probability approaching 1 as the blocklength grows. The weak converse
(error bounded away from 0) follows from Fano's inequality. The strong form
stated here, where error converges to 1, was first proved by Wolfowitz (1957)
using sphere-packing arguments. The definitive modern treatment is Csiszar and
Korner (2011, Ch. 5) via the method of types. -/

/-- Achievability (direct part) of Shannon's noisy channel coding theorem.
    For any rate below capacity, codes with arbitrarily small error exist
    at all sufficiently large blocklengths.

    **Why it is true.** Draw 2^(nR) codewords independently from the
    capacity-achieving input distribution. For each received sequence, check
    whether it is jointly typical with exactly one codeword. The AEP
    (asymptotic equipartition property) guarantees that the true codeword is
    jointly typical with high probability, and the probability of a false match
    with any other codeword is roughly 2^(-nI(X;Y)). A union bound over the
    2^(nR) alternatives gives total error roughly 2^(-n(I(X;Y) - R)), which
    vanishes whenever R < C. -/
axiom channel_coding_achievability {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R ε : ℝ)
    (hR : R < Gibbs.Hamiltonian.Channel.channelCapacity W) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (M : Type) (_ : Fintype M)
        (enc : M → (Fin n → X)) (dec : (Fin n → Y) → Option M),
        Real.log (Fintype.card M) / (n : ℝ) ≥ R ∧
        avgErrorProb (blockChannel W n) enc dec ≤ ε

/-- Strong converse of Shannon's noisy channel coding theorem.
    For any rate at or above capacity, every code sequence has error
    probability approaching 1 as blocklength grows.

    **Why it is true.** Any code at rate R >= C must pack 2^(nR) codewords
    into the output space, but the channel can only reliably distinguish
    about 2^(nC) output sequences (the size of the typical set). When
    R > C the codewords vastly outnumber the distinguishable outputs, so
    most messages collide under decoding. Wolfowitz's sphere-packing
    argument makes this precise: the fraction of messages decoded correctly
    is at most roughly 2^(-n(R - C)), which tends to zero, forcing the
    error probability to 1. -/
axiom channel_coding_converse {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (R : ℝ)
    (hR : Gibbs.Hamiltonian.Channel.channelCapacity W ≤ R) :
    ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0,
      ∀ (M : Type) (_ : Fintype M) (enc : M → (Fin n → X))
        (dec : (Fin n → Y) → Option M),
        Real.log (Fintype.card M) / (n : ℝ) ≥ R →
        1 - ε ≤ avgErrorProb (blockChannel W n) enc dec

end

end Gibbs.Axioms
