import HardnessReductions.Core
import HardnessReductions.Numbers.Defs

/-!
# 3-PARTITION

Can the numbers be partitioned into parts of exactly three indices, each part
summing to the target? Garey–Johnson [SP15], the seventh of their "basic"
NP-complete problems — the standard source of *strong* NP-hardness: its
descendants inherit hardness even when all numbers are polynomially small,
which in this library is the statement that the certified reduction chain
into it targets the unary-encoded concrete problem
(`Numbers/Encoding.lean`, `Numbers/Representation.lean`).

The instance type is the domain's shared `NumberTargetInstance`
(`Numbers/Defs.lean`), read with `target` as the bound `B`. As with
4-PARTITION, the predicate demands the part size outright and carries no
side conditions; Garey–Johnson's side conditions — every size strictly
between `B/4` and `B/2`, sizes totalling `m·B` — are the restriction
`ThreePartitionWindow`, and the hardness proof lands inside it.

Hardness proof (in `Partition3/`): from 4-PARTITION
(`FromPartition4.lean`, the regular/pairing/filler construction of
Garey–Johnson Theorem 4.4; certified in `FromPartition4/Code.lean` and
`FromPartition4/Adequacy.lean`, unary at both ends), and from 3-DIMENSIONAL
MATCHING by composition.
-/

namespace Hardness

/-- 3-PARTITION: can the indices be split into parts of size exactly three,
each part's entries summing to the target? -/
def THREE_PARTITION : Problem NumberTargetInstance := fun x ↦
  ∃ parts : Finset (Finset (Fin x.nums.length)),
    IsSizedPartition (fun i ↦ x.nums[i.1]) 3 x.target parts

/-- The Garey–Johnson side conditions on a 3-PARTITION instance: every size
lies strictly between `B/4` and `B/2` (phrased multiplicatively, so no
division appears), and the sizes total `m·B` where `m` is the number of
parts a partition must have (`3·m` numbers, so `3·sum = length·B`). -/
def ThreePartitionWindow (x : NumberTargetInstance) : Prop :=
  (∀ a ∈ x.nums, x.target < 4 * a ∧ 2 * a < x.target) ∧
    3 * x.nums.sum = x.nums.length * x.target

instance : DecidablePred ThreePartitionWindow := fun x ↦ by
  unfold ThreePartitionWindow
  infer_instance

end Hardness
