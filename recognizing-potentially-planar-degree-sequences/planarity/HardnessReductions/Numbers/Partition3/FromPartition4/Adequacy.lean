import HardnessReductions.Cert.Bridge
import HardnessReductions.Cert.Numbering
import HardnessReductions.Counting
import HardnessReductions.Numbers.Partition3.FromPartition4
import HardnessReductions.Numbers.Partition3.FromPartition4.Code
import HardnessReductions.Numbers.Partition4.FromMatching3D.Adequacy

/-!
# 4-PARTITION → 3-PARTITION, certified

The bridged correctness of `fourPartitionToThreePartitionCode`. Cost and
output-size bounds are free (`Code.cost_size_le_polyBound`); what is proved
here is that the program's output decodes to a yes-instance of 3-PARTITION —
inside the Garey–Johnson window — exactly when the input decodes to a
windowed yes-instance of 4-PARTITION. Both sides are the *unary* avatar, so
the bounds are bounds in the numbers' values: this is the strong-hardness
reading, and the last link of the chain from 3-DIMENSIONAL MATCHING.

## The shape of the argument

The mathematical layer's correctness lemmas
(`exists_tpPartition_of_isSizedPartition`,
`exists_isSizedPartition_of_tpPartition`) are parametric in the index type,
the sizes and the filler count, so this file feeds them what the program
computes: the index type is the positions of the decoded number list, and the
pool of ordered pairs of distinct positions is realized by the program's
filtered `Code.cross`, deduplication-free because the cross of two
repetition-free lists already is.

The tagged element type `α ⊕ (TpPair α × Bool) ⊕ Fin F` becomes positions of
the emitted list through the block numbering `Cert/Numbering.lean`: the
regular block first, then the pairing block laid out two per pool entry (low
then high, so `Numbering.prod … Numbering.bool` reads it), then the fillers.
The pool ↔ position bijection is the one the emitted order defines, obtained
from membership plus `Nodup` exactly as the 4-PARTITION annex obtains its
triple ↔ position bijection.
-/

namespace Hardness
namespace Cert

namespace TpCode

/-! ## The source instance, read off the encoding -/

/-- The index type of the decoded source instance: the positions of its
numbers. -/
abbrev SrcIdx (x : NumberTargetUnaryTy.denote) : Type :=
  Fin (x.1.map unaryVal).length

/-- The decoded source sizes. -/
def srcSize (x : NumberTargetUnaryTy.denote) (i : SrcIdx x) : ℕ :=
  (x.1.map unaryVal)[i.1]

/-- 4-PARTITION of the decoded source, read over the positions of the number
list. Definitional: the decoder is a repackaging. -/
theorem fourPartition_decode_iff (x : NumberTargetUnaryTy.denote) :
    Hardness.FOUR_PARTITION (decodeNumberTargetUnary x) ↔
      ∃ parts : Finset (Finset (SrcIdx x)),
        IsSizedPartition (srcSize x) 4 (unaryVal x.2) parts := Iff.rfl

/-- The enumerated input entry at a source position — the shape the pool
carries. -/
def srcEnt (x : NumberTargetUnaryTy.denote) (i : SrcIdx x) : List Bool × ℕ :=
  (x.1[i.1]'(by simpa using i.isLt), i.1)

theorem srcSize_eq_ent (x : NumberTargetUnaryTy.denote) (i : SrcIdx x) :
    srcSize x i = unaryVal (srcEnt x i).1 := List.getElem_map _

theorem srcEnt_mem (x : NumberTargetUnaryTy.denote) (i : SrcIdx x) :
    srcEnt x i ∈ x.1.zipIdx := by
  have hi : i.val < x.1.length := by simpa using i.isLt
  rw [List.mem_zipIdx_iff_getElem?]
  change x.1[i.val]? = some (x.1[i.val]'hi)
  exact List.getElem?_eq_getElem hi

/-- The pool entry a pair of distinct source positions names. -/
def srcPair (x : NumberTargetUnaryTy.denote) (p : TpPair (SrcIdx x)) :
    PoolTy.denote :=
  (srcEnt x p.val.1, srcEnt x p.val.2)

theorem srcPair_mem (x : NumberTargetUnaryTy.denote) (p : TpPair (SrcIdx x)) :
    srcPair x p ∈ poolList.eval x :=
  (mem_poolList_eval x _).mpr
    ⟨srcEnt_mem x _, srcEnt_mem x _, fun h ↦ p.property (Fin.ext h)⟩

theorem srcPair_inj (x : NumberTargetUnaryTy.denote) :
    Function.Injective (srcPair x) := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
  have h1 : a.val = c.val := congrArg (fun q ↦ q.1.2) h
  have h2 : b.val = d.val := congrArg (fun q ↦ q.2.2) h
  exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))

theorem srcPair_surj (x : NumberTargetUnaryTy.denote) {q : PoolTy.denote}
    (hq : q ∈ poolList.eval x) : ∃ p : TpPair (SrcIdx x), srcPair x p = q := by
  obtain ⟨h1, h2, hne⟩ := (mem_poolList_eval x q).mp hq
  rw [List.mem_zipIdx_iff_getElem?] at h1 h2
  obtain ⟨hb1, he1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hb2, he2⟩ := List.getElem?_eq_some_iff.mp h2
  refine ⟨⟨(⟨q.1.2, by simpa using hb1⟩, ⟨q.2.2, by simpa using hb2⟩),
    fun h ↦ hne (congrArg Fin.val h)⟩, ?_⟩
  exact Prod.ext (Prod.ext he1 rfl) (Prod.ext he2 rfl)

/-! ## The pool, as positions -/

theorem idxOf_srcPair_lt (x : NumberTargetUnaryTy.denote)
    (p : TpPair (SrcIdx x)) :
    (poolList.eval x).idxOf (srcPair x p) < (poolList.eval x).length :=
  List.idxOf_lt_length_iff.mpr (srcPair_mem x p)

theorem srcPair_idx_bijective (x : NumberTargetUnaryTy.denote) :
    Function.Bijective fun p : TpPair (SrcIdx x) ↦
      (⟨(poolList.eval x).idxOf (srcPair x p), idxOf_srcPair_lt x p⟩ :
        Fin (poolList.eval x).length) := by
  constructor
  · intro a b hab
    exact srcPair_inj x
      ((List.idxOf_inj (srcPair_mem x a)).mp (congrArg Fin.val hab))
  · intro j
    obtain ⟨p, hp⟩ := srcPair_surj x (List.getElem_mem j.isLt)
    refine ⟨p, Fin.ext ?_⟩
    change (poolList.eval x).idxOf (srcPair x p) = j.val
    rw [hp]
    exact (nodup_poolList_eval x).getElem_inj_iff.mp
      (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (List.getElem_mem j.isLt)))

/-- The pool list enumerates the pairs of distinct source positions, each
exactly once: the bijection the block numbering is built on. -/
noncomputable def poolEquiv (x : NumberTargetUnaryTy.denote) :
    TpPair (SrcIdx x) ≃ Fin (poolList.eval x).length :=
  Equiv.ofBijective _ (srcPair_idx_bijective x)

theorem card_tpPair_eq (x : NumberTargetUnaryTy.denote) :
    Fintype.card (TpPair (SrcIdx x)) = (poolList.eval x).length :=
  Numbering.card_eq (Numbering.ofEquiv (poolEquiv x))

/-- The number of fillers the program emits. -/
def tpF (x : NumberTargetUnaryTy.denote) : ℕ :=
  (poolList.eval x).length - (x.1.length + 3) / 4

/-- The layout of the emitted list: the regular block, then the pairing block
two per pool entry (low first), then the fillers. -/
noncomputable def tpNumbering (x : NumberTargetUnaryTy.denote) :
    Numbering (TpElt (SrcIdx x) (tpF x)) :=
  (Numbering.fin (x.1.map unaryVal).length).sum
    (((Numbering.ofEquiv (poolEquiv x)).prod Numbering.bool).sum
      (Numbering.fin (tpF x)))

theorem tpNumbering_reg (x : NumberTargetUnaryTy.denote) (i : SrcIdx x) :
    (tpNumbering x).num (.inl i) = i.val := rfl

theorem tpNumbering_pair (x : NumberTargetUnaryTy.denote)
    (p : TpPair (SrcIdx x)) (b : Bool) :
    (tpNumbering x).num (.inr (.inl (p, b)))
      = (x.1.map unaryVal).length
        + ((poolList.eval x).idxOf (srcPair x p) * 2 + b.toNat) := rfl

theorem tpNumbering_filler (x : NumberTargetUnaryTy.denote) (k : Fin (tpF x)) :
    (tpNumbering x).num (.inr (.inr k))
      = (x.1.map unaryVal).length
        + ((poolList.eval x).length * 2 + k.val) := rfl

theorem tpNumbering_size (x : NumberTargetUnaryTy.denote) :
    (tpNumbering x).size
      = (x.1.map unaryVal).length + ((poolList.eval x).length * 2 + tpF x) :=
  rfl

/-! ## The emitted list, block by block -/

/-- The regular block, decoded. -/
def tpRegs (x : NumberTargetUnaryTy.denote) : List ℕ :=
  (x.1.map unaryVal).map fun a ↦ 20 * unaryVal x.2 + 4 * a + 1

/-- The pairing block, decoded. -/
def tpPairs (x : NumberTargetUnaryTy.denote) : List ℕ :=
  (poolList.eval x).flatMap fun q ↦
    [24 * unaryVal x.2 + 2 - 4 * (unaryVal q.1.1 + unaryVal q.2.1),
      20 * unaryVal x.2 + 4 * (unaryVal q.1.1 + unaryVal q.2.1) + 2]

/-- The filler block, decoded. -/
def tpFills (x : NumberTargetUnaryTy.denote) : List ℕ :=
  List.replicate (tpF x) (20 * unaryVal x.2)

theorem emitted_eq (x : NumberTargetUnaryTy.denote) :
    (numsCode.eval x).map unaryVal = tpRegs x ++ (tpPairs x ++ tpFills x) :=
  numsCode_val x

theorem length_tpRegs (x : NumberTargetUnaryTy.denote) :
    (tpRegs x).length = (x.1.map unaryVal).length := List.length_map _

theorem length_tpPairs (x : NumberTargetUnaryTy.denote) :
    (tpPairs x).length = (poolList.eval x).length * 2 := by
  unfold tpPairs
  rw [List.length_flatMap]
  exact sum_map_const fun q _ ↦ rfl

theorem length_tpFills (x : NumberTargetUnaryTy.denote) :
    (tpFills x).length = tpF x := List.length_replicate

/-- The emitted number at a tagged position is the constructed size — the one
place where the program's layout is checked against the construction. -/
theorem emitted_getElem? (x : NumberTargetUnaryTy.denote)
    (e : TpElt (SrcIdx x) (tpF x)) :
    ((numsCode.eval x).map unaryVal)[(tpNumbering x).num e]?
      = some (tpSize (srcSize x) (unaryVal x.2) e) := by
  rw [emitted_eq]
  match e with
  | .inl i =>
    rw [tpNumbering_reg,
      List.getElem?_append_left (by rw [length_tpRegs]; exact i.isLt)]
    unfold tpRegs
    rw [List.getElem?_map, List.getElem?_eq_getElem i.isLt]
    rfl
  | .inr (.inl (p, b)) =>
    have hidx := idxOf_srcPair_lt x p
    have hb : b.toNat < 2 := by cases b <;> simp
    rw [tpNumbering_pair,
      List.getElem?_append_right (by rw [length_tpRegs]; omega), length_tpRegs,
      show (x.1.map unaryVal).length
          + ((poolList.eval x).idxOf (srcPair x p) * 2 + b.toNat)
          - (x.1.map unaryVal).length
        = (poolList.eval x).idxOf (srcPair x p) * 2 + b.toNat from by omega,
      List.getElem?_append_left (by rw [length_tpPairs]; omega)]
    unfold tpPairs
    obtain ⟨q0, q1⟩ := getElem?_flatMap_two
      (fun q : PoolTy.denote ↦
        24 * unaryVal x.2 + 2 - 4 * (unaryVal q.1.1 + unaryVal q.2.1))
      (fun q : PoolTy.denote ↦
        20 * unaryVal x.2 + 4 * (unaryVal q.1.1 + unaryVal q.2.1) + 2)
      (poolList.eval x) ((poolList.eval x).idxOf (srcPair x p))
    have hq : (poolList.eval x)[(poolList.eval x).idxOf (srcPair x p)]?
        = some (srcPair x p) := List.getElem?_idxOf (srcPair_mem x p)
    cases b
    · rw [show ((poolList.eval x).idxOf (srcPair x p) * 2
            + Bool.toNat false)
          = 2 * (poolList.eval x).idxOf (srcPair x p) from by
        simp [Nat.mul_comm]]
      refine q0.trans ?_
      rw [hq]
      refine congrArg some ?_
      simp only [tpSize_pair_false, pairVal, srcSize_eq_ent, srcPair]
    · rw [show ((poolList.eval x).idxOf (srcPair x p) * 2 + Bool.toNat true)
          = 2 * (poolList.eval x).idxOf (srcPair x p) + 1 from by
        simp [Nat.mul_comm]]
      refine q1.trans ?_
      rw [hq]
      refine congrArg some ?_
      simp only [tpSize_pair_true, pairVal, srcSize_eq_ent, srcPair]
  | .inr (.inr k) =>
    have hk := k.isLt
    rw [tpNumbering_filler,
      List.getElem?_append_right (by rw [length_tpRegs]; omega), length_tpRegs,
      show (x.1.map unaryVal).length + ((poolList.eval x).length * 2 + k.val)
          - (x.1.map unaryVal).length
        = (poolList.eval x).length * 2 + k.val from by omega,
      List.getElem?_append_right (by rw [length_tpPairs]; omega),
      length_tpPairs,
      show (poolList.eval x).length * 2 + k.val
          - (poolList.eval x).length * 2 = k.val from by omega]
    unfold tpFills
    rw [List.getElem?_replicate, if_pos hk]
    rfl

/-! ## The good branch -/

set_option maxHeartbeats 1000000 in
-- the block numbering, the two correctness lemmas and the window in one pass
theorem good_branch (x : NumberTargetUnaryTy.denote)
    (hwin : FourPartitionWindow (decodeNumberTargetUnary x))
    (hdvd : 4 ∣ x.1.length) :
    ((Hardness.FOUR_PARTITION.restrict FourPartitionWindow)
        (decodeNumberTargetUnary x) ↔
      Hardness.THREE_PARTITION
        (decodeNumberTargetUnary (numsCode.eval x, targetCode.eval x))) ∧
      ThreePartitionWindow
        (decodeNumberTargetUnary (numsCode.eval x, targetCode.eval x)) := by
  have hmlen : (x.1.map unaryVal).length = x.1.length := List.length_map _
  obtain ⟨n, hn⟩ := hdvd
  have hs : ∀ i : SrcIdx x, 3 * srcSize x i < unaryVal x.2 := fun i ↦
    (hwin.1 _ (List.getElem_mem i.isLt)).2
  have hcardα : Fintype.card (SrcIdx x) = 4 * n := by
    rw [Fintype.card_fin, hmlen]; omega
  have hle : n ≤ Fintype.card (TpPair (SrcIdx x)) :=
    le_card_tpPair (by omega)
  have hcardP : Fintype.card (TpPair (SrcIdx x)) = (poolList.eval x).length :=
    card_tpPair_eq x
  have hn4 : (x.1.length + 3) / 4 = n := by omega
  have hFn : tpF x + n = Fintype.card (TpPair (SrcIdx x)) := by
    have h1 : tpF x = (poolList.eval x).length - n := by unfold tpF; rw [hn4]
    rw [h1, ← hcardP]
    omega
  -- the emitted list, and the tagged positions of it
  have hlenE : ((numsCode.eval x).map unaryVal).length = (tpNumbering x).size := by
    rw [emitted_eq, tpNumbering_size, List.length_append, List.length_append,
      length_tpRegs, length_tpPairs, length_tpFills]
  obtain ⟨E', hEval⟩ : ∃ e : TpElt (SrcIdx x) (tpF x) ≃
        Fin ((numsCode.eval x).map unaryVal).length,
      ∀ y, (e y).val = (tpNumbering x).num y :=
    ⟨(tpNumbering x).equivFin.trans (finCongr hlenE.symm), fun _ ↦ rfl⟩
  have hgetp : ∀ i : Fin ((numsCode.eval x).map unaryVal).length,
      ((numsCode.eval x).map unaryVal)[i.val]
        = tpSize (srcSize x) (unaryVal x.2) (E'.symm i) := by
    intro i
    have h := emitted_getElem? x (E'.symm i)
    rw [← hEval, Equiv.apply_symm_apply, List.getElem?_eq_getElem i.isLt] at h
    exact Option.some_inj.mp h
  have hfun : (fun i : Fin ((numsCode.eval x).map unaryVal).length ↦
        tpSize (srcSize x) (unaryVal x.2) (E'.symm i))
      = fun i ↦ ((numsCode.eval x).map unaryVal)[i.val] :=
    funext fun i ↦ (hgetp i).symm
  have hdec : decodeNumberTargetUnary (numsCode.eval x, targetCode.eval x)
      = ⟨(numsCode.eval x).map unaryVal, tpBound (unaryVal x.2)⟩ := by
    have hT : unaryVal (targetCode.eval x) = tpBound (unaryVal x.2) :=
      targetCode_val x
    unfold decodeNumberTargetUnary
    rw [hT]
  rw [hdec]
  -- transport: 3-PARTITION of the emitted instance is the tagged question
  have htrans : Hardness.THREE_PARTITION
        ⟨(numsCode.eval x).map unaryVal, tpBound (unaryVal x.2)⟩ ↔
      ∃ π : Finset (Finset (TpElt (SrcIdx x) (tpF x))),
        IsSizedPartition (tpSize (srcSize x) (unaryVal x.2)) 3
          (tpBound (unaryVal x.2)) π := by
    refine Iff.trans ?_ (exists_isSizedPartition_iff_map E' _ 3 _).symm
    rw [hfun]
    unfold Hardness.THREE_PARTITION
    exact Iff.rfl
  constructor
  · rw [htrans]
    constructor
    · rintro ⟨-, hex⟩
      obtain ⟨parts, hparts⟩ := (fourPartition_decode_iff x).mp hex
      have hpc : parts.card = n := by
        have hcu : Fintype.card (SrcIdx x) = parts.card * 4 := hparts.card_univ
        rw [hcardα] at hcu
        omega
      exact exists_tpPartition_of_isSizedPartition (F := tpF x) (srcSize x) hs
        hparts (by omega)
    · rintro ⟨π, hπ⟩
      exact ⟨hwin, (fourPartition_decode_iff x).mpr
        (exists_isSizedPartition_of_tpPartition (srcSize x) hs hπ)⟩
  · have hB : 0 < tpF x → 0 < unaryVal x.2 := by
      intro hFpos
      have hP : 0 < Fintype.card (TpPair (SrcIdx x)) := by
        rw [hcardP]; unfold tpF at hFpos; omega
      obtain ⟨p⟩ := Fintype.card_pos_iff.mp hP
      have := hs p.val.1
      omega
    have hsum : 4 * ∑ i : SrcIdx x, srcSize x i
        = Fintype.card (SrcIdx x) * unaryVal x.2 := by
      have hw2 : 4 * (x.1.map unaryVal).sum
          = (x.1.map unaryVal).length * unaryVal x.2 := hwin.2
      rw [Fintype.card_fin, ← hw2]
      refine congrArg (4 * ·) ?_
      conv_rhs => rw [← List.ofFn_getElem (xs := x.1.map unaryVal)]
      exact List.sum_ofFn.symm
    unfold ThreePartitionWindow
    dsimp only
    constructor
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      rw [hgetp ⟨i, hi⟩]
      exact tp_window (srcSize x) hs hB _
    · have hL : ((numsCode.eval x).map unaryVal).sum
          = ∑ i : Fin ((numsCode.eval x).map unaryVal).length,
              ((numsCode.eval x).map unaryVal)[i.val] := by
        conv_lhs => rw [← List.ofFn_getElem
          (xs := (numsCode.eval x).map unaryVal)]
        exact List.sum_ofFn
      have hsum3 : ∑ i : Fin ((numsCode.eval x).map unaryVal).length,
            ((numsCode.eval x).map unaryVal)[i.val]
          = ∑ e : TpElt (SrcIdx x) (tpF x),
              ((numsCode.eval x).map unaryVal)[(E' e).val] :=
        (Equiv.sum_comp E'
          fun i ↦ ((numsCode.eval x).map unaryVal)[i.val]).symm
      have hsum2 : ∑ e : TpElt (SrcIdx x) (tpF x),
            ((numsCode.eval x).map unaryVal)[(E' e).val]
          = ∑ e : TpElt (SrcIdx x) (tpF x),
              tpSize (srcSize x) (unaryVal x.2) e :=
        Finset.sum_congr rfl fun e _ ↦ by
          have h := hgetp (E' e)
          rw [Equiv.symm_apply_apply] at h
          exact h
      have htot := tp_total_sum (F := tpF x) (srcSize x) hs hcardα hFn hsum
      have hcardE : Fintype.card (TpElt (SrcIdx x) (tpF x))
          = ((numsCode.eval x).map unaryVal).length :=
        (Numbering.card_eq (tpNumbering x)).trans hlenE.symm
      rw [hL, hsum3, hsum2, htot, hcardE]

/-! ## The branch condition, resolved -/

theorem offenders_eval (x : NumberTargetUnaryTy.denote) :
    offenders.eval x = x.1.filter fun u ↦ outOfWindow.eval (x, u) := by
  have h : offenders.eval x = (Code.filterEnv outOfWindow).eval (x, x.1) := rfl
  rw [h, filterEnv_eval]

theorem outOfWindow_eval_true (x : NumberTargetUnaryTy.denote) (u : List Bool) :
    outOfWindow.eval (x, u) = true ↔
      ¬ (unaryVal x.2 < 5 * unaryVal u ∧ 3 * unaryVal u < unaryVal x.2) := by
  have h : outOfWindow.eval (x, u)
      = !(Code.natLt.eval (unaryVal x.2, 5 * unaryVal u)
          && Code.natLt.eval (3 * unaryVal u, unaryVal x.2)) := rfl
  rw [h, natLt_eval, natLt_eval, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, decide_eq_false_iff_not]
  omega

theorem isNil_offenders_iff (x : NumberTargetUnaryTy.denote) :
    (Code.isNil offenders).eval x = true ↔
      ∀ a ∈ (decodeNumberTargetUnary x).nums,
        (decodeNumberTargetUnary x).target < 5 * a ∧
          3 * a < (decodeNumberTargetUnary x).target := by
  rw [isNil_eval_true, offenders_eval, List.filter_eq_nil_iff]
  constructor
  · intro h a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact not_not.mp fun hc ↦ h u hu ((outOfWindow_eval_true x u).mpr hc)
  · intro h u hu hc
    exact ((outOfWindow_eval_true x u).mp hc)
      (h (unaryVal u) (List.mem_map_of_mem hu))

theorem totalTest_eval_true (x : NumberTargetUnaryTy.denote) :
    totalTest.eval x = true ↔
      4 * (decodeNumberTargetUnary x).nums.sum
        = (decodeNumberTargetUnary x).nums.length
          * (decodeNumberTargetUnary x).target := by
  have h : totalTest.eval x
      = decide (4 * (x.1.map unaryVal).sum = x.1.length * unaryVal x.2) := rfl
  have hm : (x.1.map unaryVal).length = x.1.length := List.length_map _
  rw [h, decide_eq_true_iff]
  change _ ↔ 4 * (x.1.map unaryVal).sum
    = (x.1.map unaryVal).length * unaryVal x.2
  rw [hm]

theorem divTest_eval_true (x : NumberTargetUnaryTy.denote) :
    divTest.eval x = true ↔ 4 ∣ x.1.length := by
  have h : divTest.eval x = decide (x.1.length = 4 * partCount.eval x) := rfl
  rw [h, decide_eq_true_iff, partCount_eval]
  omega

theorem goodTest_eval_true_iff (x : NumberTargetUnaryTy.denote) :
    goodTest.eval x = true ↔
      FourPartitionWindow (decodeNumberTargetUnary x) ∧ 4 ∣ x.1.length := by
  rw [goodTest, and_eval_true, and_eval_true, isNil_offenders_iff,
    totalTest_eval_true, divTest_eval_true]
  unfold FourPartitionWindow
  tauto

/-- A windowed yes-instance of 4-PARTITION passes the branch test: the window
is half of it, and a 4-partition forces the number count to be a multiple of
four. -/
theorem goodTest_of_source {x : NumberTargetUnaryTy.denote}
    (h : (Hardness.FOUR_PARTITION.restrict FourPartitionWindow)
      (decodeNumberTargetUnary x)) : goodTest.eval x = true := by
  obtain ⟨hwin, hex⟩ := h
  obtain ⟨parts, hparts⟩ := (fourPartition_decode_iff x).mp hex
  refine (goodTest_eval_true_iff x).mpr ⟨hwin, ?_⟩
  have hcu : Fintype.card (SrcIdx x) = parts.card * 4 := hparts.card_univ
  rw [Fintype.card_fin, List.length_map _] at hcu
  exact ⟨parts.card, by omega⟩

/-- The degenerate branch's output, decoded: the parity no-instance of the
mathematical layer. -/
theorem decode_noInstance :
    decodeNumberTargetUnary noInstance = ⟨[4, 4, 4, 6, 6, 6], 15⟩ := rfl

end TpCode

/-! ## The certificate -/

/-- The program's two obligations at once: on the decoded output, 3-PARTITION
answers windowed 4-PARTITION, and the output always sits inside the
Garey–Johnson window. Both branches deliver both — the parity no-instance is
chosen so that it, too, is windowed. -/
theorem fourPartitionToThreePartitionCode_spec
    (x : NumberTargetUnaryTy.denote) :
    (Concrete.FOUR_PARTITION_UNARY_WINDOW x ↔
        Concrete.THREE_PARTITION_UNARY
          (fourPartitionToThreePartitionCode.eval x)) ∧
      ThreePartitionWindow
        (decodeNumberTargetUnary
          (fourPartitionToThreePartitionCode.eval x)) := by
  by_cases hg : TpCode.goodTest.eval x = true
  · obtain ⟨hwin, hdvd⟩ := (TpCode.goodTest_eval_true_iff x).mp hg
    have heval : fourPartitionToThreePartitionCode.eval x
        = (TpCode.numsCode.eval x, TpCode.targetCode.eval x) :=
      branch_eval_true _ _ hg
    rw [heval]
    exact TpCode.good_branch x hwin hdvd
  · have hgf : TpCode.goodTest.eval x = false := by simpa using hg
    have heval : fourPartitionToThreePartitionCode.eval x = TpCode.noInstance :=
      branch_eval_false _ _ hgf
    rw [heval, TpCode.decode_noInstance]
    refine ⟨iff_of_false (fun hy ↦ hg (TpCode.goodTest_of_source hy)) ?_,
      by decide, by decide⟩
    change ¬ Hardness.THREE_PARTITION
      (decodeNumberTargetUnary TpCode.noInstance)
    rw [TpCode.decode_noInstance]
    exact not_threePartition_parityNo

/-- **The bridged reduction**: windowed 4-PARTITION reduces to 3-PARTITION on
unary instances, inside the Garey–Johnson window — the sharp form, matching
`fourPartitionToThreePartition` of the mathematical layer. Both ends being
unary avatars, the polynomial bounds the generic theorem supplies are bounds
in the numbers' values, which is what strong NP-hardness asks for. -/
def fourPartitionToThreePartitionCertified :
    CertifiedReduction Concrete.FOUR_PARTITION_UNARY_WINDOW
      Concrete.THREE_PARTITION_UNARY_WINDOW where
  code := fourPartitionToThreePartitionCode
  correct x :=
    ⟨fun h ↦ ⟨(fourPartitionToThreePartitionCode_spec x).2,
        (fourPartitionToThreePartitionCode_spec x).1.mp h⟩,
      fun h ↦ (fourPartitionToThreePartitionCode_spec x).1.mpr h.2⟩

/-- The same certificate, read against the unrestricted target. -/
def fourPartitionToThreePartitionUnaryCertified :
    CertifiedReduction Concrete.FOUR_PARTITION_UNARY_WINDOW
      Concrete.THREE_PARTITION_UNARY where
  code := fourPartitionToThreePartitionCode
  correct x := (fourPartitionToThreePartitionCode_spec x).1

/-- Sanity check: the certified reduction projects to a plain reduction. -/
example :
    Concrete.FOUR_PARTITION_UNARY_WINDOW ⟶ᵣ Concrete.THREE_PARTITION_UNARY_WINDOW :=
  fourPartitionToThreePartitionCertified.toReduction

/-- **The chain, composed**: 3-DIMENSIONAL MATCHING reduces to 3-PARTITION on
unary instances, inside the Garey–Johnson window, with a program at every
step. Strong NP-hardness of 3-PARTITION, certified end to end. -/
def matching3DToThreePartitionCertified :
    CertifiedReduction Concrete.MATCHING_3D
      Concrete.THREE_PARTITION_UNARY_WINDOW :=
  matching3DToFourPartitionCertified.comp fourPartitionToThreePartitionCertified

/-- The same chain, read against the unrestricted target. -/
def matching3DToThreePartitionUnaryCertified :
    CertifiedReduction Concrete.MATCHING_3D Concrete.THREE_PARTITION_UNARY :=
  matching3DToFourPartitionCertified.comp
    fourPartitionToThreePartitionUnaryCertified

end Cert
end Hardness
