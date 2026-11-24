import HardnessReductions.Core
import HardnessReductions.Numbers.Defs

/-!
# 4-PARTITION

Can the numbers be partitioned into parts of exactly four indices, each part
summing to the target? The problem of Garey–Johnson §4.2 (Theorem 4.3): the
stepping stone between 3-DIMENSIONAL MATCHING and 3-PARTITION, with no
appendix code of its own but a genuine catalog identity — it is strongly
NP-hard, and the reduction into it is where the number gadget of the
3-PARTITION chain lives.

The instance type is the domain's shared `NumberTargetInstance`
(`Numbers/Defs.lean`), read with `target` as the bound `B`. Garey–Johnson
state the problem with side conditions — every size strictly between `B/5`
and `B/3`, sizes totalling `m·B` — which there force every part of a
`B`-per-part partition to have exactly four elements. Here the predicate
demands the part size outright and carries no side conditions; the side
conditions are the *restriction* `FourPartitionWindow`, and the hardness
proof lands inside the restriction (`Reduction.codRestrict`), which is the
sharpest statement the construction delivers.

Hardness proof (in `Partition4/`): from 3-DIMENSIONAL MATCHING
(`FromMatching3D.lean`, the actual/dummy copy construction over base-`r`
digits of Garey–Johnson Theorem 4.3; certified in `FromMatching3D/Code.lean`
and `FromMatching3D/Adequacy.lean`, against the unary encoding of the emitted
numbers). The renaming-invariance lemma the
gadget consumes is `exists_isSizedPartition_iff_map` (`Numbers/Defs.lean`),
shared with 3-PARTITION.
-/

namespace Hardness

/-- 4-PARTITION: can the indices be split into parts of size exactly four,
each part's entries summing to the target? -/
def FOUR_PARTITION : Problem NumberTargetInstance := fun x ↦
  ∃ parts : Finset (Finset (Fin x.nums.length)),
    IsSizedPartition (fun i ↦ x.nums[i.1]) 4 x.target parts

/-- The Garey–Johnson side conditions on a 4-PARTITION instance: every size
lies strictly between `B/5` and `B/3` (phrased multiplicatively, so no
division appears), and the sizes total `m·B` where `m` is the number of
parts a partition must have (`4·m` numbers, so `4·sum = length·B`). -/
def FourPartitionWindow (x : NumberTargetInstance) : Prop :=
  (∀ a ∈ x.nums, x.target < 5 * a ∧ 3 * a < x.target) ∧
    4 * x.nums.sum = x.nums.length * x.target

instance : DecidablePred FourPartitionWindow := fun x ↦ by
  unfold FourPartitionWindow
  infer_instance

end Hardness
