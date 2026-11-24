import HardnessReductions.Cert.Language
import HardnessReductions.Numbers.SubsetSum
import HardnessReductions.Numbers.Partition
import HardnessReductions.Numbers.Partition4
import HardnessReductions.Numbers.Partition3
import HardnessReductions.Numbers.Knapsack
import HardnessReductions.Numbers.BinPacking
import HardnessReductions.Numbers.Unary.Code

/-!
# Concrete encoding of number-problem instances

Concrete SUBSET SUM and PARTITION instances, with decoders, accessor
programs, and the concrete problems.

## Decoding discipline

Decoding must be **total**. In pleasant contrast to graphs
(`Graph/Encoding.lean`), the encodings here are junk-free: *every* pair of a
number list and a target is a SUBSET SUM instance, and *every* number list is
a PARTITION instance, so the decoders are plain repackagings and no
convention for ill-formed inputs is needed. The size-model discipline is
automatic as well: numbers are charged by bit length (`Ty.size`), and the
explicit lists represent every item, duplicates included.
-/

namespace Hardness
namespace Cert

/-- Concrete number-target instances: `(nums, target)`. Junk-free: every
value of this type is a meaningful instance. Shared by SUBSET SUM and
4-PARTITION, as the bundled `NumberTargetInstance` is. -/
abbrev NumberTargetTy : Ty := .pair (.list .nat) .nat

/-- Concrete *unary* number-target instances: the numbers and the target all
unary-encoded (`Numbers/Unary.lean`). The avatar the strong-hardness chain
certifies against: `Ty.size` charges a list by its length, so a reduction
into this type is polynomial in the *values* of the numbers it emits. -/
abbrev NumberTargetUnaryTy : Ty := .pair (.list Ty.unary) Ty.unary

/-- Decode a concrete SUBSET SUM instance. Total, and junk-free: a plain
repackaging. -/
def decodeNumberTarget (x : NumberTargetTy.denote) : NumberTargetInstance := ⟨x.1, x.2⟩

/-- Concrete PARTITION instances: the explicit list of numbers. Junk-free:
every value of this type is a meaningful instance. -/
abbrev PartitionTy : Ty := .list .nat

/-- Decode a concrete PARTITION instance. Total, and junk-free: a plain
repackaging. -/
def decodePartition (x : PartitionTy.denote) : PartitionInstance := ⟨x⟩

/-- Concrete KNAPSACK instances: `((items, capacity), goal)`, an item being a
`(size, value)` pair. Junk-free, and deliberately so: carrying sizes and values
as *one* list of pairs is what keeps it junk-free, where two parallel lists
would have to agree in length (`Numbers/Knapsack.lean`). -/
abbrev KnapsackTy : Ty := .pair (.pair (.list (.pair .nat .nat)) .nat) .nat

/-- Decode a concrete KNAPSACK instance. Total, and junk-free: a plain
repackaging. -/
def decodeKnapsack (x : KnapsackTy.denote) : KnapsackInstance := ⟨x.1.1, x.1.2, x.2⟩

/-- Concrete BIN PACKING instances: `(sizes, (capacity, bins))`. Junk-free:
every value of this type is a meaningful instance, `bins = 0` included (a
no-instance as soon as there is an item to place). -/
abbrev BinPackingTy : Ty := .pair (.list .nat) (.pair .nat .nat)

/-- Decode a concrete BIN PACKING instance. Total, and junk-free: a plain
repackaging. -/
def decodeBinPacking (x : BinPackingTy.denote) : BinPackingInstance :=
  ⟨x.1, x.2.1, x.2.2⟩

/-- Concrete *unary* BIN PACKING instances: the sizes, the capacity and the bin
count all unary-encoded. The avatar the strong-hardness chain targets — and the
bin count is unary too, which costs nothing and spares the program a crossing:
the count arises as the length of a list it has already built. -/
abbrev BinPackingUnaryTy : Ty := .pair (.list Ty.unary) (.pair Ty.unary Ty.unary)

/-- Decode a concrete unary BIN PACKING instance: every number is read off as a
length. Total, and junk-free. -/
def decodeBinPackingUnary (x : BinPackingUnaryTy.denote) : BinPackingInstance :=
  ⟨x.1.map unaryVal, unaryVal x.2.1, unaryVal x.2.2⟩

/-- Decode a concrete unary number-target instance: every number is read off
as a length (`unaryVal`). Total, and junk-free: any list of any lists of
booleans means something. -/
def decodeNumberTargetUnary (x : NumberTargetUnaryTy.denote) :
    NumberTargetInstance :=
  ⟨x.1.map unaryVal, unaryVal x.2⟩

/-! ### Accessors -/

/-- The numbers of a concrete SUBSET SUM instance. -/
def ntNums : Code NumberTargetTy (.list .nat) := .fst

/-- The target of a concrete SUBSET SUM instance. -/
def ntTarget : Code NumberTargetTy .nat := .snd

/-- The total of the numbers, via the aggregate combinator `Code.listSum`. -/
def ntTotal : Code NumberTargetTy .nat := .comp ntNums .listSum

/-! ### Readers for the unary avatar

The unary counterparts of the readers above, shared by every annex that takes a
unary number-target instance apart. A number's *value* is read with
`unaryToNat` — the certified direction; the reverse is `no_binary_to_unary`. -/

/-- The list of unary numbers. -/
def ntuNums : Code NumberTargetUnaryTy (.list .unary) := .fst

/-- The unary target. -/
def ntuTarget : Code NumberTargetUnaryTy .unary := .snd

/-- The target's value, in binary — the form comparisons need. -/
def ntuTargetVal : Code NumberTargetUnaryTy .nat := .comp ntuTarget unaryToNat

/-- How many numbers there are. -/
def ntuLen : Code NumberTargetUnaryTy .nat := .comp ntuNums .listLen

/-- The total of the numbers, in binary. -/
def ntuTotal : Code NumberTargetUnaryTy .nat :=
  .comp (.comp ntuNums (.listMap unaryToNat)) .listSum

/-- The item sizes of a concrete BIN PACKING instance. -/
def bpSizes : Code BinPackingTy (.list .nat) := .fst

/-- The bin capacity of a concrete BIN PACKING instance. -/
def bpCapacity : Code BinPackingTy .nat := .comp .snd .fst

/-- The number of bins of a concrete BIN PACKING instance. -/
def bpBins : Code BinPackingTy .nat := .comp .snd .snd

/-- The item sizes of a concrete *unary* BIN PACKING instance. -/
def bpuSizes : Code BinPackingUnaryTy (.list Ty.unary) := .fst

/-- The bin capacity of a concrete unary BIN PACKING instance. -/
def bpuCapacity : Code BinPackingUnaryTy Ty.unary := .comp .snd .fst

/-- The number of bins of a concrete unary BIN PACKING instance. -/
def bpuBins : Code BinPackingUnaryTy Ty.unary := .comp .snd .snd

@[simp] theorem bpuSizes_eval (y : BinPackingUnaryTy.denote) : bpuSizes.eval y = y.1 := rfl

@[simp] theorem bpuCapacity_eval (y : BinPackingUnaryTy.denote) :
    bpuCapacity.eval y = y.2.1 := rfl

@[simp] theorem bpuBins_eval (y : BinPackingUnaryTy.denote) :
    bpuBins.eval y = y.2.2 := rfl

namespace Concrete

/-- SUBSET SUM on concrete instances. -/
def SUBSET_SUM : Problem NumberTargetTy.denote :=
  Hardness.SUBSET_SUM.comap decodeNumberTarget

/-- PARTITION on concrete instances. -/
def PARTITION : Problem PartitionTy.denote :=
  Hardness.PARTITION.comap decodePartition

/-- KNAPSACK on concrete instances. -/
def KNAPSACK : Problem KnapsackTy.denote :=
  Hardness.KNAPSACK.comap decodeKnapsack

/-- BIN PACKING on concrete instances. -/
def BIN_PACKING : Problem BinPackingTy.denote :=
  Hardness.BIN_PACKING.comap decodeBinPacking

/-- 3-PARTITION on concrete instances. -/
def THREE_PARTITION : Problem NumberTargetTy.denote :=
  Hardness.THREE_PARTITION.comap decodeNumberTarget

/-- 4-PARTITION on concrete instances. -/
def FOUR_PARTITION : Problem NumberTargetTy.denote :=
  Hardness.FOUR_PARTITION.comap decodeNumberTarget

/-- 4-PARTITION on concrete unary instances — the target of the strong
hardness chain. -/
def FOUR_PARTITION_UNARY : Problem NumberTargetUnaryTy.denote :=
  Hardness.FOUR_PARTITION.comap decodeNumberTargetUnary

/-- 4-PARTITION on concrete unary instances, restricted to the Garey–Johnson
window. Restricting the decoded problem and decoding the restricted problem
agree definitionally, so this is at once "the concrete avatar of
`FOUR_PARTITION.restrict FourPartitionWindow`" and "`FOUR_PARTITION_UNARY`
restricted to instances whose decoding sits in the window". -/
def FOUR_PARTITION_UNARY_WINDOW : Problem NumberTargetUnaryTy.denote :=
  (Hardness.FOUR_PARTITION.restrict FourPartitionWindow).comap
    decodeNumberTargetUnary

/-- 3-PARTITION on concrete unary instances — the end of the strong hardness
chain, and the shape every descendant of 3-PARTITION will reduce from. -/
def THREE_PARTITION_UNARY : Problem NumberTargetUnaryTy.denote :=
  Hardness.THREE_PARTITION.comap decodeNumberTargetUnary

/-- BIN PACKING on concrete *unary* instances — the strong-hardness target. -/
def BIN_PACKING_UNARY : Problem BinPackingUnaryTy.denote :=
  Hardness.BIN_PACKING.comap decodeBinPackingUnary

/-- 3-PARTITION on concrete unary instances, restricted to the Garey–Johnson
window — the sharp target, as `FOUR_PARTITION_UNARY_WINDOW` is for its
predecessor. -/
def THREE_PARTITION_UNARY_WINDOW : Problem NumberTargetUnaryTy.denote :=
  (Hardness.THREE_PARTITION.restrict ThreePartitionWindow).comap
    decodeNumberTargetUnary

end Concrete

end Cert
end Hardness
