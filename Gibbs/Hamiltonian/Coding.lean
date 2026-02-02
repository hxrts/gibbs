import Gibbs.Hamiltonian.Channel
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Block Coding Infrastructure

Defines the n-fold memoryless extension of a discrete memoryless channel and the
average error probability of a code. These are the basic objects needed to state
Shannon's noisy channel coding theorem.
-/

namespace Gibbs.Hamiltonian.Coding

noncomputable section

open scoped BigOperators

/-- Average error probability for a code over a DMC. -/
def avgErrorProb {M X Y : Type*} [Fintype M] [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (enc : M → X) (dec : Y → Option M) : ℝ :=
  by
    classical
    exact (1 / (Fintype.card M : ℝ)) * ∑ m : M, ∑ y : Y,
      W.transition (enc m) y * (if dec y = some m then 0 else 1)

/-- The n-fold memoryless extension of a DMC. The transition probability of the
    block channel is the product of per-coordinate transition probabilities. -/
def blockChannel {X Y : Type*} [Fintype X] [Fintype Y]
    (W : Gibbs.Hamiltonian.Channel.DMC X Y) (n : ℕ) :
    Gibbs.Hamiltonian.Channel.DMC (Fin n → X) (Fin n → Y) where
  transition := fun x y => ∏ i, W.transition (x i) (y i)
  transition_nonneg := by
    intro x y
    classical
    exact Finset.prod_nonneg (fun i _ => W.transition_nonneg (x i) (y i))
  transition_sum_one := by
    intro x
    classical
    -- ∑ y, ∏ i, W(x_i, y_i) = ∏ i, ∑ y_i, W(x_i, y_i) = ∏ i, 1 = 1
    have hfactor :
        (∏ i : Fin n, ∑ j : Y, W.transition (x i) j) =
          ∑ y : Fin n → Y, ∏ i, W.transition (x i) (y i) :=
      Fintype.prod_sum (fun (i : Fin n) (j : Y) => W.transition (x i) j)
    simp [← hfactor, W.transition_sum_one]

end

end Gibbs.Hamiltonian.Coding
