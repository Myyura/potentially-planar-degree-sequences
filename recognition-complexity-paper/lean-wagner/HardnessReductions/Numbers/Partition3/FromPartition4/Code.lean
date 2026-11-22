import HardnessReductions.Numbers.Encoding

/-!
# 4-PARTITION → 3-PARTITION: the program

The instance map of `Partition3/FromPartition4.lean` as a `Code` program.
Source and target are both the *unary* concrete number-target type
(`NumberTargetUnaryTy`), so this is a link of the strong-hardness chain with
unary at both ends: the input numbers arrive as numerals whose length is their
value, and the emitted numbers — all of magnitude `O(B)` — are built from them
by unary arithmetic alone, never by decoding a number and re-materializing it.

The program mirrors the construction:

* *the pool*: every ordered pair of distinct input positions, as a `Code.cross`
  of the enumerated number list with itself, diagonal filtered out. Enumerating
  rather than indexing is what makes the pool entries carry their two unary
  numerals directly, so a pool entry's value `v = s p₁ + s p₂` is one `uadd`
  and no lookup;
* *the part count*: `n = m/4`, obtained without a division primitive — the
  language deliberately has none — as the length of the enumerated positions
  `i` satisfying `4i < m`, which are exactly the `⌈m/4⌉` first ones;
* *branch*: the Garey–Johnson window on the source, recomputed concretely, and
  `m = 4n`; offenders map to the parity no-instance;
* *emit*: the regular numbers (one per input), then the pairing numbers (two
  per pool entry, low then high), then the fillers (one per pool entry past
  the first `n`), and the bound `64B + 4`.

The three blocks are laid end to end in exactly the order the adequacy proof's
numbering reads them (`FromPartition4/Adequacy.lean`), and every unary value
goes through the sugar of `Numbers/Unary/Code.lean`, so that proof works in
`ℕ` throughout.
-/

namespace Hardness
namespace Cert

namespace TpCode

/-- A pool entry: two enumerated input numbers, each a unary numeral paired
with its position. Carrying the numeral alongside the position is what spares
the program a lookup when it needs the pair's value. -/
abbrev PoolTy : Ty := .pair (.pair Ty.unary .nat) (.pair Ty.unary .nat)

/-! ## Reading the instance

The instance readers themselves are domain-level (`Numbers/Encoding.lean`,
the `ntu*` programs); what belongs here is only the environment-threaded form
this gadget's per-element passes need. -/

/-- The bound, read from an environment that carries the instance in its first
component — the form every per-element and per-pool-entry program needs. -/
def envTgt {τ : Ty} : Code (.pair NumberTargetUnaryTy τ) .unary := .comp .fst ntuTarget

/-! ## The part count, without a division primitive -/

/-- The test behind `quarterList`: an enumerated position `i` with `4i` below
the length carried in the environment. -/
def quarterTest : Code (.pair .nat (.pair Ty.unary .nat)) .bool :=
  Code.lt (Code.mul (.const .nat 4) (.comp .snd .snd)) .fst

/-- The enumerated positions `i` with `4i < m` — the first `⌈m/4⌉` of them.
The language has no division or remainder primitive, and needs none: a
quarter is taken by enumerating and filtering, and the surviving *length* is
the quotient. -/
def quarterList : Code NumberTargetUnaryTy (.list (.pair Ty.unary .nat)) :=
  .comp (.pair ntuLen (.comp ntuNums .listEnum)) (Code.filterEnv quarterTest)

/-- The number of parts a 4-partition of the source must have. -/
def partCount : Code NumberTargetUnaryTy .nat := .comp quarterList .listLen

/-- The same count as a unary numeral, for the filler arithmetic. -/
def partCountU : Code NumberTargetUnaryTy .unary :=
  .comp quarterList unaryOfList

theorem quarterList_eval (x : NumberTargetUnaryTy.denote) :
    quarterList.eval x
      = x.1.zipIdx.filter fun q ↦ decide (4 * q.2 < x.1.length) := by
  have h : quarterList.eval x
      = (Code.filterEnv quarterTest).eval (x.1.length, x.1.zipIdx) := rfl
  rw [h, filterEnv_eval]
  refine List.filter_congr fun q _ ↦ ?_
  have h2 : quarterTest.eval (x.1.length, q)
      = Code.natLt.eval (4 * q.2, x.1.length) := rfl
  rw [h2, natLt_eval]

theorem length_quarterList_eval (x : NumberTargetUnaryTy.denote) :
    (quarterList.eval x).length = (x.1.length + 3) / 4 := by
  rw [quarterList_eval,
    List.filter_congr (q := fun q : (List Bool) × ℕ ↦
      decide (q.2 < (x.1.length + 3) / 4))
      fun q _ ↦ by rw [decide_eq_decide]; omega,
    length_filter_zipIdx_lt]
  omega

@[simp] theorem partCount_eval (x : NumberTargetUnaryTy.denote) :
    partCount.eval x = (x.1.length + 3) / 4 := length_quarterList_eval x

@[simp] theorem partCountU_eval (x : NumberTargetUnaryTy.denote) :
    unaryVal (partCountU.eval x) = (x.1.length + 3) / 4 := by
  have h : unaryVal (partCountU.eval x) = (quarterList.eval x).length :=
    unaryOfList_eval _
  rw [h, length_quarterList_eval]

/-! ## The pool -/

/-- The distinctness test on a pool candidate: the two enumerated entries sit
at different positions. -/
def distinctTest : Code (.pair (.pair Ty.unary .nat) (.pair Ty.unary .nat)) .bool :=
  .comp (.pair (.comp .fst .snd) (.comp .snd .snd)) Code.natNe

/-- The pool: every ordered pair of distinct input positions, each side
carrying its own unary numeral. -/
def poolList : Code NumberTargetUnaryTy (.list PoolTy) :=
  .comp
    (.comp (.pair (.comp ntuNums .listEnum) (.comp ntuNums .listEnum)) Code.cross)
    (.listFilter distinctTest)

/-- The pool candidates before the diagonal is dropped. -/
abbrev poolSquare (x : NumberTargetUnaryTy.denote) : List PoolTy.denote :=
  (Code.cross (σ := .pair Ty.unary .nat) (τ := .pair Ty.unary .nat)).eval
    (x.1.zipIdx, x.1.zipIdx)

theorem poolList_eval (x : NumberTargetUnaryTy.denote) :
    poolList.eval x
      = (poolSquare x).filter fun q ↦ decide (q.1.2 ≠ q.2.2) := by
  have h : poolList.eval x
      = (poolSquare x).filter fun q ↦ distinctTest.eval q := rfl
  rw [h]
  refine List.filter_congr fun q _ ↦ ?_
  have h2 : distinctTest.eval q = !decide (q.1.2 = q.2.2) := rfl
  rw [h2, ← decide_not]

theorem mem_poolList_eval (x : NumberTargetUnaryTy.denote) (q : PoolTy.denote) :
    q ∈ poolList.eval x ↔
      q.1 ∈ x.1.zipIdx ∧ q.2 ∈ x.1.zipIdx ∧ q.1.2 ≠ q.2.2 := by
  rw [poolList_eval, List.mem_filter, mem_cross_eval]
  simp only [decide_eq_true_eq]
  tauto

theorem nodup_poolList_eval (x : NumberTargetUnaryTy.denote) :
    (poolList.eval x).Nodup := by
  have hz : x.1.zipIdx.Nodup := by
    refine List.Nodup.of_map Prod.snd ?_
    rw [List.zipIdx_map_snd, ← List.range_eq_range']
    exact List.nodup_range
  rw [poolList_eval]
  refine List.Nodup.filter _ ?_
  have h : poolSquare x
      = x.1.zipIdx.flatMap fun a ↦ x.1.zipIdx.map fun b ↦ (a, b) := rfl
  rw [h]
  refine List.nodup_flatMap.mpr
    ⟨fun a _ ↦ hz.map fun b c hbc ↦ congrArg Prod.snd hbc, ?_⟩
  refine hz.pairwise_of_forall_ne fun a _ b _ hab ↦ ?_
  refine List.disjoint_left.mpr fun p hp hp' ↦ hab ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
  obtain ⟨d, -, hd⟩ := List.mem_map.mp hp'
  exact (congrArg Prod.fst hd).symm

/-! ## The emitted numbers -/

/-- A regular number: `20B + 4·s a + 1`, one per input number. -/
def regSize : Code (.pair NumberTargetUnaryTy .unary) .unary :=
  uadd (uadd (umul (unaryConst 20) envTgt) (umul (unaryConst 4) .snd))
    (unaryConst 1)

/-- The regular block. -/
def regsCode : Code NumberTargetUnaryTy (.list .unary) :=
  .comp (.pair .id ntuNums) (.listMapEnv regSize)

/-- A pool entry's value `v = s p₁ + s p₂`, read straight off the entry. -/
def poolVal : Code (.pair NumberTargetUnaryTy PoolTy) .unary :=
  uadd (.comp .snd (.comp .fst .fst)) (.comp .snd (.comp .snd .fst))

/-- The low member of a matched pair: `24B + 2 − 4v`. -/
def loSize : Code (.pair NumberTargetUnaryTy PoolTy) .unary :=
  usub (uadd (umul (unaryConst 24) envTgt) (unaryConst 2))
    (umul (unaryConst 4) poolVal)

/-- The high member: `20B + 4v + 2`. -/
def hiSize : Code (.pair NumberTargetUnaryTy PoolTy) .unary :=
  uadd (uadd (umul (unaryConst 20) envTgt) (umul (unaryConst 4) poolVal))
    (unaryConst 2)

/-- A pool entry's two numbers, low first. -/
def pairBlock : Code (.pair NumberTargetUnaryTy PoolTy) (.list .unary) :=
  Code.cons loSize (.comp hiSize .listSingle)

/-- The pairing block: two numbers per pool entry, flattened. -/
def pairsCode : Code NumberTargetUnaryTy (.list .unary) :=
  .comp (.comp (.pair .id poolList) (.listMapEnv pairBlock)) .listJoin

/-- The filler count: one per pool entry the parts cannot claim. -/
def fillerCount : Code NumberTargetUnaryTy .unary :=
  usub (.comp poolList unaryOfList) partCountU

/-- The filler block: that many copies of `20B`. -/
def fillersCode : Code NumberTargetUnaryTy (.list .unary) :=
  .comp (.pair .id fillerCount) (.listMapEnv (umul (unaryConst 20) envTgt))

/-- All the numbers: regulars, then pairings, then fillers. -/
def numsCode : Code NumberTargetUnaryTy (.list .unary) :=
  Code.append regsCode (Code.append pairsCode fillersCode)

/-- The bound: `64B + 4`. -/
def targetCode : Code NumberTargetUnaryTy .unary :=
  uadd (umul (unaryConst 64) ntuTarget) (unaryConst 4)

/-! ## What the blocks are worth

One lemma per block, phrased through `unaryVal`: from here on the adequacy
proof sees only `ℕ`. -/

theorem regsCode_val (x : NumberTargetUnaryTy.denote) :
    (regsCode.eval x).map unaryVal
      = (x.1.map unaryVal).map fun a ↦ 20 * unaryVal x.2 + 4 * a + 1 := by
  have h : regsCode.eval x = x.1.map fun u ↦ regSize.eval (x, u) := rfl
  rw [h, List.map_map, List.map_map]
  refine List.map_congr_left fun u _ ↦ ?_
  simp only [Function.comp_apply, regSize, uadd_eval, umul_eval, unaryConst_eval]
  rfl

theorem pairBlock_val (x : NumberTargetUnaryTy.denote) (q : PoolTy.denote) :
    (pairBlock.eval (x, q)).map unaryVal
      = [24 * unaryVal x.2 + 2 - 4 * (unaryVal q.1.1 + unaryVal q.2.1),
          20 * unaryVal x.2 + 4 * (unaryVal q.1.1 + unaryVal q.2.1) + 2] := by
  have h : pairBlock.eval (x, q) = [loSize.eval (x, q), hiSize.eval (x, q)] :=
    rfl
  have hv : unaryVal (poolVal.eval (x, q)) = unaryVal q.1.1 + unaryVal q.2.1 :=
    uadd_eval _ _ _
  rw [h, List.map_cons, List.map_cons, List.map_nil]
  simp only [loSize, hiSize, usub_eval, uadd_eval, umul_eval, unaryConst_eval, hv]
  rfl

theorem pairsCode_val (x : NumberTargetUnaryTy.denote) :
    (pairsCode.eval x).map unaryVal
      = (poolList.eval x).flatMap fun q ↦
          [24 * unaryVal x.2 + 2 - 4 * (unaryVal q.1.1 + unaryVal q.2.1),
            20 * unaryVal x.2 + 4 * (unaryVal q.1.1 + unaryVal q.2.1) + 2] := by
  have h : pairsCode.eval x
      = ((poolList.eval x).map fun q ↦ pairBlock.eval (x, q)).flatten := rfl
  rw [h, List.map_flatten, List.map_map, List.flatMap_def]
  refine congrArg List.flatten (List.map_congr_left fun q _ ↦ ?_)
  exact pairBlock_val x q

theorem fillerCount_val (x : NumberTargetUnaryTy.denote) :
    unaryVal (fillerCount.eval x)
      = (poolList.eval x).length - (x.1.length + 3) / 4 := by
  have h : unaryVal (fillerCount.eval x)
      = unaryVal ((Code.comp poolList unaryOfList).eval x)
        - unaryVal (partCountU.eval x) := usub_eval _ _ _
  rw [h, partCountU_eval]
  exact congrArg (· - _) (unaryOfList_eval (poolList.eval x))

theorem fillersCode_val (x : NumberTargetUnaryTy.denote) :
    (fillersCode.eval x).map unaryVal
      = List.replicate ((poolList.eval x).length - (x.1.length + 3) / 4)
          (20 * unaryVal x.2) := by
  have h : fillersCode.eval x
      = (fillerCount.eval x).map fun b ↦
          (umul (unaryConst 20) envTgt).eval (x, b) := rfl
  rw [h, List.map_map,
    List.map_congr_left (l := fillerCount.eval x)
      (g := fun _ ↦ 20 * unaryVal x.2)
      (fun b _ ↦ by
        simp only [Function.comp_apply, umul_eval, unaryConst_eval]; rfl),
    List.map_const', ← fillerCount_val]
  rfl

theorem numsCode_val (x : NumberTargetUnaryTy.denote) :
    (numsCode.eval x).map unaryVal
      = ((x.1.map unaryVal).map fun a ↦ 20 * unaryVal x.2 + 4 * a + 1)
        ++ (((poolList.eval x).flatMap fun q ↦
              [24 * unaryVal x.2 + 2 - 4 * (unaryVal q.1.1 + unaryVal q.2.1),
                20 * unaryVal x.2 + 4 * (unaryVal q.1.1 + unaryVal q.2.1) + 2])
          ++ List.replicate ((poolList.eval x).length - (x.1.length + 3) / 4)
              (20 * unaryVal x.2)) := by
  have h : numsCode.eval x
      = regsCode.eval x ++ (pairsCode.eval x ++ fillersCode.eval x) := rfl
  rw [h, List.map_append, List.map_append, regsCode_val, pairsCode_val,
    fillersCode_val]

@[simp] theorem targetCode_val (x : NumberTargetUnaryTy.denote) :
    unaryVal (targetCode.eval x) = 64 * unaryVal x.2 + 4 := by
  simp only [targetCode, uadd_eval, umul_eval, unaryConst_eval]
  rfl

/-! ## The branch condition -/

/-- A number outside the Garey–Johnson window: `B < 5a` and `3a < B` do not
both hold. -/
def outOfWindow : Code (.pair NumberTargetUnaryTy .unary) .bool :=
  .comp
    (Code.and
      (Code.lt (.comp .fst ntuTargetVal)
        (Code.mul (.const .nat 5) (.comp .snd unaryToNat)))
      (Code.lt (Code.mul (.const .nat 3) (.comp .snd unaryToNat))
        (.comp .fst ntuTargetVal)))
    .boolNot

/-- The input numbers violating the window. -/
def offenders : Code NumberTargetUnaryTy (.list .unary) :=
  .comp (.pair .id ntuNums) (Code.filterEnv outOfWindow)

/-- The window's second half: `4·sum = m·B`. -/
def totalTest : Code NumberTargetUnaryTy .bool :=
  .comp (.pair (Code.mul (.const .nat 4) ntuTotal) (Code.mul ntuLen ntuTargetVal)) .natEq

/-- Divisibility of the number count by four, tested as `m = 4n` against the
part count — the language has no remainder primitive, and this is what stands
in for one. -/
def divTest : Code NumberTargetUnaryTy .bool :=
  .comp (.pair ntuLen (Code.mul (.const .nat 4) partCount)) .natEq

/-- The branch condition: the Garey–Johnson window on the source, and a number
count divisible by four. -/
def goodTest : Code NumberTargetUnaryTy .bool :=
  Code.and (Code.and (Code.isNil offenders) totalTest) divTest

/-- The parity no-instance, unary-encoded: all sizes even, bound odd — and
windowed, so the degenerate branch lands inside the restriction too. -/
def noInstance : NumberTargetUnaryTy.denote :=
  ([List.replicate 4 true, List.replicate 4 true, List.replicate 4 true,
    List.replicate 6 true, List.replicate 6 true, List.replicate 6 true],
    List.replicate 15 true)

end TpCode

/-- The program: 4-PARTITION → 3-PARTITION, unary at both ends. -/
def fourPartitionToThreePartitionCode :
    Code NumberTargetUnaryTy NumberTargetUnaryTy :=
  .branch TpCode.goodTest (.pair TpCode.numsCode TpCode.targetCode)
    (.const NumberTargetUnaryTy TpCode.noInstance)

end Cert
end Hardness
