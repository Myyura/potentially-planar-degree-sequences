import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import HardnessReductions.Core

/-!
# KNAPSACK

The 0-1 decision form: each item has a size and a value; is there a selection
of total size at most the capacity and total value at least the goal? The two
thresholds run in *opposite* directions, which is the whole character of the
problem — and the reason its hardness proof is so short, a SUBSET SUM instance
being exactly the case where the two directions are forced to meet.

Sizes and values are carried as one list of `(size, value)` *pairs* rather than
as two parallel lists. Garey–Johnson's instance is a function pair `s, v : U →
ℕ`, which a two-list encoding would represent with a length agreement between
them — a well-formedness condition, and the library's decoding discipline
admits none: every value of the concrete type must mean some instance. Pairing
the two numbers puts the agreement in the type instead, at no cost to the size
model (a pair is charged by the bit length of both components).

Hardness proof (in `Knapsack/`): from SUBSET SUM (`FromSubsetSum.lean`, sizes
and values both the given numbers; certified in `FromSubsetSum/Certified.lean`).
The concrete encoding of KNAPSACK instances lives in `Numbers/Encoding.lean`.
-/

namespace Hardness

/-- An instance of KNAPSACK: a list of items, each with a size and a value, a
capacity, and a value goal. Duplicate entries of `items` are distinct items. -/
structure KnapsackInstance : Type where
  /-- The available items, each as a `(size, value)` pair. -/
  items : List (ℕ × ℕ)
  /-- The capacity: the total size a selection may not exceed. -/
  capacity : ℕ
  /-- The goal: the total value a selection must reach. -/
  goal : ℕ

/-- KNAPSACK: is there a selection of items whose total size is at most the
capacity and whose total value is at least the goal? Selections are finsets of
*indices*, so that duplicate items stay distinct. -/
def KNAPSACK : Problem KnapsackInstance :=
  fun x ↦ ∃ s : Finset (Fin x.items.length),
    (∑ i ∈ s, (x.items[i.1]'i.isLt).1) ≤ x.capacity ∧
      x.goal ≤ ∑ i ∈ s, (x.items[i.1]'i.isLt).2

end Hardness
