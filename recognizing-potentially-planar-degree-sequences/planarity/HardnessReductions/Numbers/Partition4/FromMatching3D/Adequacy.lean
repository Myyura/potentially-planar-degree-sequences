import HardnessReductions.Cert.Bridge
import HardnessReductions.Cert.Numbering
import HardnessReductions.Counting
import HardnessReductions.Numbers.Partition4.FromMatching3D
import HardnessReductions.Numbers.Partition4.FromMatching3D.Code

/-!
# 3-dimensional matching → 4-PARTITION, certified

The bridged correctness of `matching3DToFourPartitionCode`. Cost and
output-size bounds are free (`Code.cost_size_le_polyBound`); what is proved
here is that the program's output decodes to a yes-instance of 4-PARTITION —
inside the Garey–Johnson window — exactly when the input decodes to a
yes-instance of 3-DIMENSIONAL MATCHING.

## The shape of the argument

The mathematical layer's correctness lemmas
(`exists_isSizedPartition_of_matching`,
`exists_matching_of_isSizedPartition`) are *parametric* in the index maps and
in the designation of actual copies, so this file feeds them the concrete
data the program computes: indices are the triple's own entries
(`iW = Fin.val`), and the designated occurrence of an element is the first
surviving triple through it (`matchedW x i |>.headI`). The emitted list is
four numbers per surviving triple; the passage from the tagged element type
`↥T × Fin 4` to positions is the rectangle numbering
`(ofEquiv …).prod (fin 4)` (`Cert/Numbering.lean`), with the deduplicated
triple list supplying the triple ↔ position bijection.

Everything about unary values goes through the `unaryVal` simp set of
`Numbers/Unary/Code.lean`, so the proofs below manipulate ordinary `ℕ`
expressions throughout.
-/

namespace Hardness
namespace Cert

namespace MfpCode

/-- The head of a nonempty list is its first element. -/
theorem headI_eq_getElem_zero {α : Type*} [Inhabited α] {l : List α}
    (h : 0 < l.length) : l.headI = l[0] := by
  obtain ⟨a, tl, rfl⟩ :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos h)
  rfl

/-! ## Values of the emitted pieces -/

/-- The radix, on the decoded side. -/
def mfpRVal (x : Matching3DTy.denote) : ℕ := 33 * (x.1.length + 1)

theorem radix_val' (x : Matching3DTy.denote) :
    unaryVal (radix.eval x) = mfpRVal x := radix_val x

/-- The surviving triples through the `W`-element `i` — the list whose head
is the designated occurrence of `i`. -/
def matchedW (x : Matching3DTy.denote) (i : ℕ) : List TripleTy.denote :=
  (dedupTriples.eval x).filter fun t ↦ decide (i = t.1)

/-- Through the `X`-element `j`. -/
def matchedX (x : Matching3DTy.denote) (j : ℕ) : List TripleTy.denote :=
  (dedupTriples.eval x).filter fun t ↦ decide (j = t.2.1)

/-- Through the `Y`-element `k`. -/
def matchedY (x : Matching3DTy.denote) (k : ℕ) : List TripleTy.denote :=
  (dedupTriples.eval x).filter fun t ↦ decide (k = t.2.2)

/-- The value triple of a decoded triple: the concrete tuple its `Fin`
entries denote. The bridge between subtype points of the decoded instance
and entries of the survivor list. -/
def pval {x : Matching3DTy.denote} (th : ↥(decodeMatching3D x).triples) :
    TripleTy.denote :=
  (Fin.val th.val.1, Fin.val th.val.2.1, Fin.val th.val.2.2)

theorem matchesAt_fst_eval (x : Matching3DTy.denote) (i : ℕ) :
    (matchesAt fstEq).eval (dedupTriples.eval x, i) = matchedW x i := by
  rw [matchesAt_eval]
  rfl

theorem matchesAt_snd_eval (x : Matching3DTy.denote) (j : ℕ) :
    (matchesAt sndEq).eval (dedupTriples.eval x, j) = matchedX x j := by
  rw [matchesAt_eval]
  rfl

theorem matchesAt_trd_eval (x : Matching3DTy.denote) (k : ℕ) :
    (matchesAt trdEq).eval (dedupTriples.eval x, k) = matchedY x k := by
  rw [matchesAt_eval]
  rfl

/-- A surviving triple is among the matches of its own `W`-element. -/
theorem self_mem_matchedW {x : Matching3DTy.denote} {t : TripleTy.denote}
    (ht : t ∈ dedupTriples.eval x) : t ∈ matchedW x t.1 :=
  List.mem_filter.mpr ⟨ht, by simp⟩

theorem self_mem_matchedX {x : Matching3DTy.denote} {t : TripleTy.denote}
    (ht : t ∈ dedupTriples.eval x) : t ∈ matchedX x t.2.1 :=
  List.mem_filter.mpr ⟨ht, by simp⟩

theorem self_mem_matchedY {x : Matching3DTy.denote} {t : TripleTy.denote}
    (ht : t ∈ dedupTriples.eval x) : t ∈ matchedY x t.2.2 :=
  List.mem_filter.mpr ⟨ht, by simp⟩

/-- The designation test, resolved: a surviving triple is *actual* along `W`
exactly when it heads the matches of its element. -/
theorem isActAt_fst_eval {x : Matching3DTy.denote} {t : TripleTy.denote}
    (hlen : 0 < (matchedW x t.1).length) :
    (isActAt fstEq (.comp .snd .fst)).eval (x, t) = true ↔
      t = (matchedW x t.1).headI := by
  have hfirst : (firstAt fstEq (.comp .snd .fst)).eval (x, t)
      = [(matchedW x t.1)[0]] := by
    have h : (firstAt fstEq (.comp .snd .fst)).eval (x, t)
        = Code.listNth.eval
            ((matchesAt fstEq).eval (dedupTriples.eval x, t.1), 0) := rfl
    rw [h, matchesAt_fst_eval, listNth_eval hlen]
  have h : (isActAt fstEq (.comp .snd .fst)).eval (x, t)
      = decide (((Code.filterEnv tripleEq).eval
          (t, (firstAt fstEq (.comp .snd .fst)).eval (x, t))).length = 1) := rfl
  rw [h, filterEnv_eval, decide_eq_true_iff, hfirst,
    List.filter_congr fun s _ ↦ tripleEq_eval t s,
    headI_eq_getElem_zero hlen, List.filter_singleton]
  by_cases he : t = (matchedW x t.1)[0]
  · rw [decide_eq_true he, Bool.cond_true]
    exact iff_of_true rfl he
  · rw [decide_eq_false he, Bool.cond_false]
    exact iff_of_false (by simp) he

/-- The designation test along `X`. -/
theorem isActAt_snd_eval {x : Matching3DTy.denote} {t : TripleTy.denote}
    (hlen : 0 < (matchedX x t.2.1).length) :
    (isActAt sndEq (.comp .snd (.comp .snd .fst))).eval (x, t) = true ↔
      t = (matchedX x t.2.1).headI := by
  have hfirst : (firstAt sndEq (.comp .snd (.comp .snd .fst))).eval (x, t)
      = [(matchedX x t.2.1)[0]] := by
    have h : (firstAt sndEq (.comp .snd (.comp .snd .fst))).eval (x, t)
        = Code.listNth.eval
            ((matchesAt sndEq).eval (dedupTriples.eval x, t.2.1), 0) := rfl
    rw [h, matchesAt_snd_eval, listNth_eval hlen]
  have h : (isActAt sndEq (.comp .snd (.comp .snd .fst))).eval (x, t)
      = decide (((Code.filterEnv tripleEq).eval
          (t, (firstAt sndEq (.comp .snd (.comp .snd .fst))).eval (x, t))).length = 1) := rfl
  rw [h, filterEnv_eval, decide_eq_true_iff, hfirst,
    List.filter_congr fun s _ ↦ tripleEq_eval t s,
    headI_eq_getElem_zero hlen, List.filter_singleton]
  by_cases he : t = (matchedX x t.2.1)[0]
  · rw [decide_eq_true he, Bool.cond_true]
    exact iff_of_true rfl he
  · rw [decide_eq_false he, Bool.cond_false]
    exact iff_of_false (by simp) he

/-- The designation test along `Y`. -/
theorem isActAt_trd_eval {x : Matching3DTy.denote} {t : TripleTy.denote}
    (hlen : 0 < (matchedY x t.2.2).length) :
    (isActAt trdEq (.comp .snd (.comp .snd .snd))).eval (x, t) = true ↔
      t = (matchedY x t.2.2).headI := by
  have hfirst : (firstAt trdEq (.comp .snd (.comp .snd .snd))).eval (x, t)
      = [(matchedY x t.2.2)[0]] := by
    have h : (firstAt trdEq (.comp .snd (.comp .snd .snd))).eval (x, t)
        = Code.listNth.eval
            ((matchesAt trdEq).eval (dedupTriples.eval x, t.2.2), 0) := rfl
    rw [h, matchesAt_trd_eval, listNth_eval hlen]
  have h : (isActAt trdEq (.comp .snd (.comp .snd .snd))).eval (x, t)
      = decide (((Code.filterEnv tripleEq).eval
          (t, (firstAt trdEq (.comp .snd (.comp .snd .snd))).eval (x, t))).length = 1) := rfl
  rw [h, filterEnv_eval, decide_eq_true_iff, hfirst,
    List.filter_congr fun s _ ↦ tripleEq_eval t s,
    headI_eq_getElem_zero hlen, List.filter_singleton]
  by_cases he : t = (matchedY x t.2.2)[0]
  · rw [decide_eq_true he, Bool.cond_true]
    exact iff_of_true rfl he
  · rw [decide_eq_false he, Bool.cond_false]
    exact iff_of_false (by simp) he

/-! ## The four size values -/

/-- The values of the radix powers in the per-triple environment. -/
theorem rpow_vals (x : Matching3DTy.denote) (t : TripleTy.denote) :
    unaryVal (rpow1.eval (x, t)) = mfpRVal x ∧
    unaryVal (rpow2.eval (x, t)) = mfpRVal x ^ 2 ∧
    unaryVal (rpow3.eval (x, t)) = mfpRVal x ^ 3 ∧
    unaryVal (rpow4.eval (x, t)) = mfpRVal x ^ 4 := by
  have h1 : unaryVal (rpow1.eval (x, t)) = mfpRVal x := by
    have h : rpow1.eval (x, t) = radix.eval x := rfl
    rw [h, radix_val']
  have h2 : unaryVal (rpow2.eval (x, t)) = mfpRVal x ^ 2 := by
    rw [rpow2, umul_eval, h1]
    ring
  have h3 : unaryVal (rpow3.eval (x, t)) = mfpRVal x ^ 3 := by
    rw [rpow3, umul_eval, h1, h2]
    ring
  exact ⟨h1, h2, h3, by rw [rpow4, umul_eval, h2]; ring⟩

/-- The values of the unary index terms, for an in-range triple. -/
theorem uIdx_vals (x : Matching3DTy.denote) {t : TripleTy.denote}
    (h1 : t.1 < x.1.length) (h2 : t.2.1 < x.2.1.length)
    (h3 : t.2.2 < x.2.2.1.length) :
    unaryVal (uIdxW.eval (x, t)) = t.1 ∧
    unaryVal (uIdxX.eval (x, t)) = t.2.1 ∧
    unaryVal (uIdxY.eval (x, t)) = t.2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · have h : uIdxW.eval (x, t) = unaryOfBounded.eval (t.1, x.1) := rfl
    rw [h, unaryOfBounded_eval]
    exact Nat.min_eq_left h1.le
  · have h : uIdxX.eval (x, t) = unaryOfBounded.eval (t.2.1, x.2.1) := rfl
    rw [h, unaryOfBounded_eval]
    exact Nat.min_eq_left h2.le
  · have h : uIdxY.eval (x, t) = unaryOfBounded.eval (t.2.2, x.2.2.1) := rfl
    rw [h, unaryOfBounded_eval]
    exact Nat.min_eq_left h3.le

/-- The four decoded sizes of a surviving triple, as `mfp` sizes: the block
the program emits for `t` carries exactly the sizes of the mathematical
construction, with `Fin.val` indices and head-of-matches designation. The
cardinality hypotheses keep every index below the radix. -/
theorem blockOf_map_val (x : Matching3DTy.denote)
    (hXW : x.2.1.length = x.1.length) (hYW : x.2.2.1.length = x.1.length)
    {t : TripleTy.denote} (ht : t ∈ dedupTriples.eval x) :
    (blockOf.eval (x, t)).map unaryVal
      = [10 * mfpRVal x ^ 4 + 8
            - (t.2.2 * mfpRVal x ^ 3 + t.2.1 * mfpRVal x ^ 2
                + t.1 * mfpRVal x),
          (if t = (matchedW x t.1).headI then 10 else 11) * mfpRVal x ^ 4
            + t.1 * mfpRVal x + 1,
          (if t = (matchedX x t.2.1).headI then 10 else 11) * mfpRVal x ^ 4
            + t.2.1 * mfpRVal x ^ 2 + 2,
          (if t = (matchedY x t.2.2).headI then 10 else 8) * mfpRVal x ^ 4
            + t.2.2 * mfpRVal x ^ 3 + 4] := by
  obtain ⟨-, hb1, hb2, hb3⟩ := (mem_dedupTriples_eval x t).mp ht
  obtain ⟨hr1, hr2, hr3, hr4⟩ := rpow_vals x t
  obtain ⟨hi1, hi2, hi3⟩ := uIdx_vals x hb1 hb2 hb3
  have hblock : blockOf.eval (x, t)
      = [uSizeCode.eval (x, t), wSizeCode.eval (x, t), xSizeCode.eval (x, t),
          ySizeCode.eval (x, t)] := rfl
  have hRdef : mfpRVal x = 33 * (x.1.length + 1) := rfl
  have hb1' : t.1 < mfpRVal x :=
    Nat.lt_of_lt_of_le hb1 (by rw [hRdef]; omega)
  have hb2' : t.2.1 < mfpRVal x :=
    Nat.lt_of_lt_of_le hb2 (by rw [hRdef, ← hXW]; omega)
  have hb3' : t.2.2 < mfpRVal x :=
    Nat.lt_of_lt_of_le hb3 (by rw [hRdef, ← hYW]; omega)
  have hWne : 0 < (matchedW x t.1).length :=
    List.length_pos_of_mem (self_mem_matchedW ht)
  have hXne : 0 < (matchedX x t.2.1).length :=
    List.length_pos_of_mem (self_mem_matchedX ht)
  have hYne : 0 < (matchedY x t.2.2).length :=
    List.length_pos_of_mem (self_mem_matchedY ht)
  -- the triple element
  have hu : unaryVal (uSizeCode.eval (x, t))
      = 10 * mfpRVal x ^ 4 + 8
          - (t.2.2 * mfpRVal x ^ 3 + t.2.1 * mfpRVal x ^ 2
              + t.1 * mfpRVal x) := by
    rw [uSizeCode, uadd_eval, usub_eval, umul_eval, unaryConst_eval,
      uadd_eval, umul_eval, uadd_eval, umul_eval, umul_eval, unaryConst_eval,
      hr4, hr3, hr2, hr1, hi1, hi2, hi3]
    have hRpos : 0 < mfpRVal x := by rw [hRdef]; omega
    have p3 : mfpRVal x ^ 3 ≤ mfpRVal x ^ 4 :=
      Nat.pow_le_pow_right hRpos (by omega)
    have p2 : mfpRVal x ^ 2 ≤ mfpRVal x ^ 4 :=
      Nat.pow_le_pow_right hRpos (by omega)
    have s3 : t.2.2 * mfpRVal x ^ 3 ≤ mfpRVal x ^ 4 := by
      calc t.2.2 * mfpRVal x ^ 3 ≤ mfpRVal x * mfpRVal x ^ 3 :=
            Nat.mul_le_mul_right _ hb3'.le
        _ = mfpRVal x ^ 4 := by ring
    have s2 : t.2.1 * mfpRVal x ^ 2 ≤ mfpRVal x ^ 4 := by
      calc t.2.1 * mfpRVal x ^ 2 ≤ mfpRVal x * mfpRVal x ^ 2 :=
            Nat.mul_le_mul_right _ hb2'.le
        _ = mfpRVal x ^ 3 := by ring
        _ ≤ mfpRVal x ^ 4 := p3
    have s1 : t.1 * mfpRVal x ≤ mfpRVal x ^ 4 := by
      calc t.1 * mfpRVal x ≤ mfpRVal x * mfpRVal x :=
            Nat.mul_le_mul_right _ hb1'.le
        _ = mfpRVal x ^ 2 := by ring
        _ ≤ mfpRVal x ^ 4 := p2
    have hSle : t.2.2 * mfpRVal x ^ 3 + (t.2.1 * mfpRVal x ^ 2
        + t.1 * mfpRVal x) ≤ 10 * mfpRVal x ^ 4 := by
      have h1 := Nat.add_le_add s3 (Nat.add_le_add s2 s1)
      have h2 : mfpRVal x ^ 4 + (mfpRVal x ^ 4 + mfpRVal x ^ 4)
          ≤ 10 * mfpRVal x ^ 4 := by
        have h3 : mfpRVal x ^ 4 + (mfpRVal x ^ 4 + mfpRVal x ^ 4)
            = 3 * mfpRVal x ^ 4 := by ring
        rw [h3]
        exact Nat.mul_le_mul_right _ (by omega)
      exact h1.trans h2
    have hS12 : t.2.2 * mfpRVal x ^ 3 + t.2.1 * mfpRVal x ^ 2
        + t.1 * mfpRVal x
        = t.2.2 * mfpRVal x ^ 3 + (t.2.1 * mfpRVal x ^ 2
            + t.1 * mfpRVal x) := by ring
    rw [hS12, Nat.sub_add_comm hSle]
  -- the W-copy
  have hw : unaryVal (wSizeCode.eval (x, t))
      = (if t = (matchedW x t.1).headI then 10 else 11) * mfpRVal x ^ 4
          + t.1 * mfpRVal x + 1 := by
    rw [wSizeCode, uadd_eval, uadd_eval, umul_eval, unaryConst_eval, hi1, hr1]
    by_cases hact : t = (matchedW x t.1).headI
    · rw [leadTerm, branch_eval_true _ _ ((isActAt_fst_eval hWne).mpr hact),
        umul_eval, unaryConst_eval, hr4, if_pos hact]
      ring
    · have hfalse : (isActAt fstEq (.comp .snd .fst)).eval (x, t) = false :=
        Bool.eq_false_iff.mpr fun hc ↦ hact ((isActAt_fst_eval hWne).mp hc)
      rw [leadTerm, branch_eval_false _ _ hfalse, umul_eval, unaryConst_eval,
        hr4, if_neg hact]
      ring
  -- the X-copy
  have hx : unaryVal (xSizeCode.eval (x, t))
      = (if t = (matchedX x t.2.1).headI then 10 else 11) * mfpRVal x ^ 4
          + t.2.1 * mfpRVal x ^ 2 + 2 := by
    rw [xSizeCode, uadd_eval, uadd_eval, umul_eval, unaryConst_eval, hi2, hr2]
    by_cases hact : t = (matchedX x t.2.1).headI
    · rw [leadTerm, branch_eval_true _ _ ((isActAt_snd_eval hXne).mpr hact),
        umul_eval, unaryConst_eval, hr4, if_pos hact]
      ring
    · have hfalse : (isActAt sndEq (.comp .snd (.comp .snd .fst))).eval
          (x, t) = false :=
        Bool.eq_false_iff.mpr fun hc ↦ hact ((isActAt_snd_eval hXne).mp hc)
      rw [leadTerm, branch_eval_false _ _ hfalse, umul_eval, unaryConst_eval,
        hr4, if_neg hact]
      ring
  -- the Y-copy
  have hy : unaryVal (ySizeCode.eval (x, t))
      = (if t = (matchedY x t.2.2).headI then 10 else 8) * mfpRVal x ^ 4
          + t.2.2 * mfpRVal x ^ 3 + 4 := by
    rw [ySizeCode, uadd_eval, uadd_eval, umul_eval, unaryConst_eval, hi3, hr3]
    by_cases hact : t = (matchedY x t.2.2).headI
    · rw [leadTerm, branch_eval_true _ _ ((isActAt_trd_eval hYne).mpr hact),
        umul_eval, unaryConst_eval, hr4, if_pos hact]
      ring
    · have hfalse : (isActAt trdEq (.comp .snd (.comp .snd .snd))).eval
          (x, t) = false :=
        Bool.eq_false_iff.mpr fun hc ↦ hact ((isActAt_trd_eval hYne).mp hc)
      rw [leadTerm, branch_eval_false _ _ hfalse, umul_eval, unaryConst_eval,
        hr4, if_neg hact]
      ring
  rw [hblock, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.map_nil, hu, hw, hx, hy]

/-! ## The emitted list and the bound -/

/-- The emitted numbers, decoded: four sizes per surviving triple. -/
theorem numsCode_map_val (x : Matching3DTy.denote)
    (hXW : x.2.1.length = x.1.length) (hYW : x.2.2.1.length = x.1.length) :
    (numsCode.eval x).map unaryVal
      = (dedupTriples.eval x).flatMap fun t ↦
          [10 * mfpRVal x ^ 4 + 8
              - (t.2.2 * mfpRVal x ^ 3 + t.2.1 * mfpRVal x ^ 2
                  + t.1 * mfpRVal x),
            (if t = (matchedW x t.1).headI then 10 else 11) * mfpRVal x ^ 4
              + t.1 * mfpRVal x + 1,
            (if t = (matchedX x t.2.1).headI then 10 else 11) * mfpRVal x ^ 4
              + t.2.1 * mfpRVal x ^ 2 + 2,
            (if t = (matchedY x t.2.2).headI then 10 else 8) * mfpRVal x ^ 4
              + t.2.2 * mfpRVal x ^ 3 + 4] := by
  have h : numsCode.eval x
      = ((dedupTriples.eval x).map fun t ↦ blockOf.eval (x, t)).flatten := rfl
  rw [h, List.map_flatten, List.map_map, List.flatMap]
  exact congrArg List.flatten (List.map_congr_left fun t ht ↦
    blockOf_map_val x hXW hYW ht)

/-- The emitted bound, decoded. -/
theorem targetCode_val (x : Matching3DTy.denote) :
    unaryVal (targetCode.eval x) = mfpB (mfpRVal x) := by
  rw [targetCode]
  simp only [uadd_eval, umul_eval, unaryConst_eval, radix_val']
  unfold mfpB
  ring

/-! ## The branch condition, decoded -/

/-- Coverage along `W`, recomputed concretely: the uncovered-list is empty
exactly when every decoded `W`-element lies in some decoded triple. -/
theorem isNil_uncoveredW_iff (x : Matching3DTy.denote) :
    (Code.isNil uncoveredW).eval x = true ↔
      ∀ w : (decodeMatching3D x).W,
        ∃ t ∈ (decodeMatching3D x).triples, t.1 = w := by
  rw [isNil_eval_true]
  have he : uncoveredW.eval x
      = (List.range x.1.length).filter fun i ↦
          (uncovTest fstEq).eval (goodTriples.eval x, i) := by
    have h : uncoveredW.eval x = (Code.filterEnv (uncovTest fstEq)).eval
        (goodTriples.eval x, (Code.indices (τ := .nat)).eval x.1) := rfl
    rw [h, filterEnv_eval, indices_eval]
  rw [he, List.filter_eq_nil_iff]
  constructor
  · intro hall w
    have hnu := hall (Fin.val w) (List.mem_range.mpr (Fin.isLt w))
    have hex : ∃ t ∈ goodTriples.eval x, fstEq.eval (Fin.val w, t) = true := by
      by_contra hc
      exact hnu ((uncovTest_eval_true fstEq _ _).mpr fun t ht hteq ↦
        hc ⟨t, ht, hteq⟩)
    obtain ⟨t, htg, hteq⟩ := hex
    rw [fstEq_eval, decide_eq_true_iff] at hteq
    obtain ⟨hts, h1, h2, h3⟩ := (mem_goodTriples_eval x t).mp htg
    refine ⟨(⟨t.1, h1⟩, ⟨t.2.1, h2⟩, ⟨t.2.2, h3⟩), ?_, ?_⟩
    · exact (mem_decodeMatching3D_triples x _).mpr hts
    · exact Fin.ext hteq.symm
  · intro hcov i hi hu
    rw [uncovTest_eval_true] at hu
    obtain ⟨th, htmem, hteq⟩ := hcov ⟨i, List.mem_range.mp hi⟩
    have hvals : (Fin.val th.1, Fin.val th.2.1, Fin.val th.2.2)
        ∈ goodTriples.eval x := by
      rw [mem_goodTriples_eval]
      exact ⟨(mem_decodeMatching3D_triples x th).mp htmem, Fin.isLt th.1,
        Fin.isLt th.2.1, Fin.isLt th.2.2⟩
    refine hu _ hvals ?_
    rw [fstEq_eval, decide_eq_true_iff]
    exact (congrArg Fin.val hteq).symm

/-- Coverage along `X`. -/
theorem isNil_uncoveredX_iff (x : Matching3DTy.denote) :
    (Code.isNil uncoveredX).eval x = true ↔
      ∀ xe : (decodeMatching3D x).X,
        ∃ t ∈ (decodeMatching3D x).triples, t.2.1 = xe := by
  rw [isNil_eval_true]
  have he : uncoveredX.eval x
      = (List.range x.2.1.length).filter fun j ↦
          (uncovTest sndEq).eval (goodTriples.eval x, j) := by
    have h : uncoveredX.eval x = (Code.filterEnv (uncovTest sndEq)).eval
        (goodTriples.eval x, (Code.indices (τ := .nat)).eval x.2.1) := rfl
    rw [h, filterEnv_eval, indices_eval]
  rw [he, List.filter_eq_nil_iff]
  constructor
  · intro hall xe
    have hnu := hall (Fin.val xe) (List.mem_range.mpr (Fin.isLt xe))
    have hex : ∃ t ∈ goodTriples.eval x, sndEq.eval (Fin.val xe, t) = true := by
      by_contra hc
      exact hnu ((uncovTest_eval_true sndEq _ _).mpr fun t ht hteq ↦
        hc ⟨t, ht, hteq⟩)
    obtain ⟨t, htg, hteq⟩ := hex
    rw [sndEq_eval, decide_eq_true_iff] at hteq
    obtain ⟨hts, h1, h2, h3⟩ := (mem_goodTriples_eval x t).mp htg
    refine ⟨(⟨t.1, h1⟩, ⟨t.2.1, h2⟩, ⟨t.2.2, h3⟩), ?_, ?_⟩
    · exact (mem_decodeMatching3D_triples x _).mpr hts
    · exact Fin.ext hteq.symm
  · intro hcov j hj hu
    rw [uncovTest_eval_true] at hu
    obtain ⟨th, htmem, hteq⟩ := hcov ⟨j, List.mem_range.mp hj⟩
    have hvals : (Fin.val th.1, Fin.val th.2.1, Fin.val th.2.2)
        ∈ goodTriples.eval x := by
      rw [mem_goodTriples_eval]
      exact ⟨(mem_decodeMatching3D_triples x th).mp htmem, Fin.isLt th.1,
        Fin.isLt th.2.1, Fin.isLt th.2.2⟩
    refine hu _ hvals ?_
    rw [sndEq_eval, decide_eq_true_iff]
    exact (congrArg Fin.val hteq).symm

/-- Coverage along `Y`. -/
theorem isNil_uncoveredY_iff (x : Matching3DTy.denote) :
    (Code.isNil uncoveredY).eval x = true ↔
      ∀ ye : (decodeMatching3D x).Y,
        ∃ t ∈ (decodeMatching3D x).triples, t.2.2 = ye := by
  rw [isNil_eval_true]
  have he : uncoveredY.eval x
      = (List.range x.2.2.1.length).filter fun k ↦
          (uncovTest trdEq).eval (goodTriples.eval x, k) := by
    have h : uncoveredY.eval x = (Code.filterEnv (uncovTest trdEq)).eval
        (goodTriples.eval x, (Code.indices (τ := .nat)).eval x.2.2.1) := rfl
    rw [h, filterEnv_eval, indices_eval]
  rw [he, List.filter_eq_nil_iff]
  constructor
  · intro hall ye
    have hnu := hall (Fin.val ye) (List.mem_range.mpr (Fin.isLt ye))
    have hex : ∃ t ∈ goodTriples.eval x, trdEq.eval (Fin.val ye, t) = true := by
      by_contra hc
      exact hnu ((uncovTest_eval_true trdEq _ _).mpr fun t ht hteq ↦
        hc ⟨t, ht, hteq⟩)
    obtain ⟨t, htg, hteq⟩ := hex
    rw [trdEq_eval, decide_eq_true_iff] at hteq
    obtain ⟨hts, h1, h2, h3⟩ := (mem_goodTriples_eval x t).mp htg
    refine ⟨(⟨t.1, h1⟩, ⟨t.2.1, h2⟩, ⟨t.2.2, h3⟩), ?_, ?_⟩
    · exact (mem_decodeMatching3D_triples x _).mpr hts
    · exact Fin.ext hteq.symm
  · intro hcov k hk hu
    rw [uncovTest_eval_true] at hu
    obtain ⟨th, htmem, hteq⟩ := hcov ⟨k, List.mem_range.mp hk⟩
    have hvals : (Fin.val th.1, Fin.val th.2.1, Fin.val th.2.2)
        ∈ goodTriples.eval x := by
      rw [mem_goodTriples_eval]
      exact ⟨(mem_decodeMatching3D_triples x th).mp htmem, Fin.isLt th.1,
        Fin.isLt th.2.1, Fin.isLt th.2.2⟩
    refine hu _ hvals ?_
    rw [trdEq_eval, decide_eq_true_iff]
    exact (congrArg Fin.val hteq).symm

/-- The program's branch condition agrees with the mathematical layer's
(`Matching3DGood`) on the decoded instance — the agreement lemma a branching
certificate owes its reduction. -/
theorem goodInstance_eval_true_iff (x : Matching3DTy.denote) :
    goodInstance.eval x = true ↔ Matching3DGood (decodeMatching3D x) := by
  have h : goodInstance.eval x
      = (decide (x.1.length = x.2.1.length) &&
          (decide (x.1.length = x.2.2.1.length) &&
            ((Code.isNil uncoveredW).eval x &&
              ((Code.isNil uncoveredX).eval x && (Code.isNil uncoveredY).eval x)))) :=
    rfl
  rw [h]
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  rw [isNil_uncoveredW_iff, isNil_uncoveredX_iff, isNil_uncoveredY_iff]
  unfold Matching3DGood
  have hcW : Fintype.card (decodeMatching3D x).W = x.1.length :=
    Fintype.card_fin _
  have hcX : Fintype.card (decodeMatching3D x).X = x.2.1.length :=
    Fintype.card_fin _
  have hcY : Fintype.card (decodeMatching3D x).Y = x.2.2.1.length :=
    Fintype.card_fin _
  rw [hcW, hcX, hcY]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1.symm, h2.symm, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1.symm, h2.symm, h3, h4, h5⟩

/-! ## The good branch, assembled -/

set_option maxHeartbeats 1000000 in
-- the assembly below is long, not hard: the default budget runs out on its
-- sheer length, not on any one step
/-- The gadget branch, in full: with the branch condition satisfied, the
decoded output is 4-partitionable exactly when the decoded input has a
matching — and it sits inside the Garey–Johnson window. One proof serves
both conclusions because they share the designation functions and the
position bijection. (The heartbeat raise is for the sheer length of the
assembly, not any single hard step.) -/
theorem good_branch (x : Matching3DTy.denote)
    (hXW : x.2.1.length = x.1.length) (hYW : x.2.2.1.length = x.1.length)
    (hcovW : ∀ w : (decodeMatching3D x).W,
      ∃ t ∈ (decodeMatching3D x).triples, t.1 = w)
    (hcovX : ∀ xe : (decodeMatching3D x).X,
      ∃ t ∈ (decodeMatching3D x).triples, t.2.1 = xe)
    (hcovY : ∀ ye : (decodeMatching3D x).Y,
      ∃ t ∈ (decodeMatching3D x).triples, t.2.2 = ye) :
    (MATCHING_3D (decodeMatching3D x) ↔
      Hardness.FOUR_PARTITION (decodeNumberTargetUnary
        (numsCode.eval x, targetCode.eval x))) ∧
    FourPartitionWindow (decodeNumberTargetUnary
      (numsCode.eval x, targetCode.eval x)) := by
  have hnodup := nodup_dedupTriples_eval x
  have hRdef : mfpRVal x = 33 * (x.1.length + 1) := rfl
  -- membership of a decoded triple's value tuple in the survivors
  have hvals_mem : ∀ th : ↥(decodeMatching3D x).triples,
      pval th ∈ dedupTriples.eval x := by
    intro th
    change (Fin.val th.val.1, Fin.val th.val.2.1, Fin.val th.val.2.2)
      ∈ dedupTriples.eval x
    rw [mem_dedupTriples_eval]
    exact ⟨(mem_decodeMatching3D_triples x th.val).mp th.2, Fin.isLt th.val.1,
      Fin.isLt th.val.2.1, Fin.isLt th.val.2.2⟩
  have hlift : ∀ t ∈ dedupTriples.eval x,
      ∃ th : ↥(decodeMatching3D x).triples, pval th = t := by
    intro t ht
    obtain ⟨hts, h1, h2, h3⟩ := (mem_dedupTriples_eval x t).mp ht
    exact ⟨⟨(⟨t.1, h1⟩, ⟨t.2.1, h2⟩, ⟨t.2.2, h3⟩),
      (mem_decodeMatching3D_triples x _).mpr hts⟩, rfl⟩
  have hvals_inj : ∀ th₁ th₂ : ↥(decodeMatching3D x).triples,
      pval th₁ = pval th₂ → th₁ = th₂ := by
    intro th₁ th₂ h
    rw [Prod.ext_iff, Prod.ext_iff] at h
    obtain ⟨e1, e2, e3⟩ := h
    exact Subtype.ext
      (Prod.ext (Fin.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e3)))
  -- numeric bounds on radix and indices
  have h33 : (33 : ℕ) ≤ mfpRVal x := by rw [hRdef]; omega
  have hq33 : 33 * x.1.length ≤ mfpRVal x := by rw [hRdef]; omega
  have hlen1 : x.1.length ≤ mfpRVal x := by rw [hRdef]; omega
  have hiWq : ∀ w : (decodeMatching3D x).W, Fin.val w < x.1.length :=
    fun w ↦ Fin.isLt w
  have hiXq : ∀ xe : (decodeMatching3D x).X, Fin.val xe < x.1.length :=
    fun xe ↦ Nat.lt_of_lt_of_le (Fin.isLt xe) (le_of_eq hXW)
  have hiYq : ∀ ye : (decodeMatching3D x).Y, Fin.val ye < x.1.length :=
    fun ye ↦ Nat.lt_of_lt_of_le (Fin.isLt ye) (le_of_eq hYW)
  have hiW : ∀ w : (decodeMatching3D x).W, Fin.val w < mfpRVal x :=
    fun w ↦ Nat.lt_of_lt_of_le (hiWq w) hlen1
  have hiX : ∀ xe : (decodeMatching3D x).X, Fin.val xe < mfpRVal x :=
    fun xe ↦ Nat.lt_of_lt_of_le (hiXq xe) hlen1
  have hiY : ∀ ye : (decodeMatching3D x).Y, Fin.val ye < mfpRVal x :=
    fun ye ↦ Nat.lt_of_lt_of_le (hiYq ye) hlen1
  have hinjW : Function.Injective (Fin.val : Fin x.1.length → ℕ) :=
    Fin.val_injective
  have hinjX : Function.Injective (Fin.val : Fin x.2.1.length → ℕ) :=
    Fin.val_injective
  have hinjY : Function.Injective (Fin.val : Fin x.2.2.1.length → ℕ) :=
    Fin.val_injective
  -- what membership in a match list says
  have hmatchW : ∀ (i : ℕ), ∀ m ∈ matchedW x i,
      m ∈ dedupTriples.eval x ∧ i = m.1 := fun i m hm ↦
    ⟨(List.mem_filter.mp hm).1, of_decide_eq_true (List.mem_filter.mp hm).2⟩
  have hmatchX : ∀ (i : ℕ), ∀ m ∈ matchedX x i,
      m ∈ dedupTriples.eval x ∧ i = m.2.1 := fun i m hm ↦
    ⟨(List.mem_filter.mp hm).1, of_decide_eq_true (List.mem_filter.mp hm).2⟩
  have hmatchY : ∀ (i : ℕ), ∀ m ∈ matchedY x i,
      m ∈ dedupTriples.eval x ∧ i = m.2.2 := fun i m hm ↦
    ⟨(List.mem_filter.mp hm).1, of_decide_eq_true (List.mem_filter.mp hm).2⟩
  -- coverage makes every match list nonempty, so heads are honest members
  have hheadW : ∀ w : (decodeMatching3D x).W,
      (matchedW x (Fin.val w)).headI ∈ matchedW x (Fin.val w) := by
    intro w
    obtain ⟨t, htT, htw⟩ := hcovW w
    have hmem : pval (⟨t, htT⟩ : ↥(decodeMatching3D x).triples)
        ∈ matchedW x (Fin.val w) :=
      List.mem_filter.mpr ⟨hvals_mem _,
        decide_eq_true (congrArg Fin.val htw.symm)⟩
    rw [headI_eq_getElem_zero (List.length_pos_of_mem hmem)]
    exact List.getElem_mem _
  have hheadX : ∀ xe : (decodeMatching3D x).X,
      (matchedX x (Fin.val xe)).headI ∈ matchedX x (Fin.val xe) := by
    intro xe
    obtain ⟨t, htT, htx⟩ := hcovX xe
    have hmem : pval (⟨t, htT⟩ : ↥(decodeMatching3D x).triples)
        ∈ matchedX x (Fin.val xe) :=
      List.mem_filter.mpr ⟨hvals_mem _,
        decide_eq_true (congrArg Fin.val htx.symm)⟩
    rw [headI_eq_getElem_zero (List.length_pos_of_mem hmem)]
    exact List.getElem_mem _
  have hheadY : ∀ ye : (decodeMatching3D x).Y,
      (matchedY x (Fin.val ye)).headI ∈ matchedY x (Fin.val ye) := by
    intro ye
    obtain ⟨t, htT, hty⟩ := hcovY ye
    have hmem : pval (⟨t, htT⟩ : ↥(decodeMatching3D x).triples)
        ∈ matchedY x (Fin.val ye) :=
      List.mem_filter.mpr ⟨hvals_mem _,
        decide_eq_true (congrArg Fin.val hty.symm)⟩
    rw [headI_eq_getElem_zero (List.length_pos_of_mem hmem)]
    exact List.getElem_mem _
  -- the designated triples, as subtype points
  have hpickW : ∀ w : (decodeMatching3D x).W,
      ∃ th : ↥(decodeMatching3D x).triples,
        pval th = (matchedW x (Fin.val w)).headI :=
    fun w ↦ hlift _ (hmatchW _ _ (hheadW w)).1
  have hpickX : ∀ xe : (decodeMatching3D x).X,
      ∃ th : ↥(decodeMatching3D x).triples,
        pval th = (matchedX x (Fin.val xe)).headI :=
    fun xe ↦ hlift _ (hmatchX _ _ (hheadX xe)).1
  have hpickY : ∀ ye : (decodeMatching3D x).Y,
      ∃ th : ↥(decodeMatching3D x).triples,
        pval th = (matchedY x (Fin.val ye)).headI :=
    fun ye ↦ hlift _ (hmatchY _ _ (hheadY ye)).1
  choose pw hpw using hpickW
  choose px hpx using hpickX
  choose py hpy using hpickY
  have hpW : ∀ w : (decodeMatching3D x).W,
      (pw w).val ∈ (decodeMatching3D x).triples ∧ ((pw w).val).1 = w := by
    intro w
    refine ⟨(pw w).2, Fin.ext ?_⟩
    have h1 : (pval (pw w)).1 = ((matchedW x (Fin.val w)).headI).1 :=
      congrArg Prod.fst (hpw w)
    exact h1.trans ((hmatchW _ _ (hheadW w)).2).symm
  have hpX : ∀ xe : (decodeMatching3D x).X,
      (px xe).val ∈ (decodeMatching3D x).triples ∧ ((px xe).val).2.1 = xe := by
    intro xe
    refine ⟨(px xe).2, Fin.ext ?_⟩
    have h1 : (pval (px xe)).2.1 = ((matchedX x (Fin.val xe)).headI).2.1 :=
      congrArg (fun v : TripleTy.denote ↦ v.2.1) (hpx xe)
    exact h1.trans ((hmatchX _ _ (hheadX xe)).2).symm
  have hpY : ∀ ye : (decodeMatching3D x).Y,
      (py ye).val ∈ (decodeMatching3D x).triples ∧ ((py ye).val).2.2 = ye := by
    intro ye
    refine ⟨(py ye).2, Fin.ext ?_⟩
    have h1 : (pval (py ye)).2.2 = ((matchedY x (Fin.val ye)).headI).2.2 :=
      congrArg (fun v : TripleTy.denote ↦ v.2.2) (hpy ye)
    exact h1.trans ((hmatchY _ _ (hheadY ye)).2).symm
  -- designation agrees with the program's head-of-matches test
  have hdesW : ∀ th : ↥(decodeMatching3D x).triples,
      (pw th.val.1).val = th.val ↔
        pval th = (matchedW x (Fin.val th.val.1)).headI := by
    intro th
    constructor
    · intro h
      rw [← hpw th.val.1]
      exact congrArg pval (Subtype.ext h).symm
    · intro h
      exact congrArg Subtype.val
        (hvals_inj (pw th.val.1) th ((hpw th.val.1).trans h.symm))
  have hdesX : ∀ th : ↥(decodeMatching3D x).triples,
      (px th.val.2.1).val = th.val ↔
        pval th = (matchedX x (Fin.val th.val.2.1)).headI := by
    intro th
    constructor
    · intro h
      rw [← hpx th.val.2.1]
      exact congrArg pval (Subtype.ext h).symm
    · intro h
      exact congrArg Subtype.val
        (hvals_inj (px th.val.2.1) th ((hpx th.val.2.1).trans h.symm))
  have hdesY : ∀ th : ↥(decodeMatching3D x).triples,
      (py th.val.2.2).val = th.val ↔
        pval th = (matchedY x (Fin.val th.val.2.2)).headI := by
    intro th
    constructor
    · intro h
      rw [← hpy th.val.2.2]
      exact congrArg pval (Subtype.ext h).symm
    · intro h
      exact congrArg Subtype.val
        (hvals_inj (py th.val.2.2) th ((hpy th.val.2.2).trans h.symm))
  -- the survivor positions, as a bijection with the subtype
  have hltIdx : ∀ th : ↥(decodeMatching3D x).triples,
      (dedupTriples.eval x).idxOf (pval th) < (dedupTriples.eval x).length :=
    fun th ↦ List.idxOf_lt_length_iff.mpr (hvals_mem th)
  have hbij : Function.Bijective
      (fun th : ↥(decodeMatching3D x).triples ↦
        (⟨(dedupTriples.eval x).idxOf (pval th), hltIdx th⟩ :
          Fin (dedupTriples.eval x).length)) := by
    constructor
    · intro a b hab
      exact hvals_inj a b
        ((List.idxOf_inj (hvals_mem a)).mp (congrArg Fin.val hab))
    · intro j
      obtain ⟨th, hth⟩ := hlift _ (List.getElem_mem j.isLt)
      refine ⟨th, Fin.ext ?_⟩
      change (dedupTriples.eval x).idxOf (pval th) = Fin.val j
      rw [hth]
      exact hnodup.getElem_inj_iff.mp
        (List.getElem_idxOf
          (List.idxOf_lt_length_iff.mpr (List.getElem_mem j.isLt)))
  have hcardT : Fintype.card ↥(decodeMatching3D x).triples
      = (dedupTriples.eval x).length :=
    Numbering.card_eq (Numbering.ofEquiv (Equiv.ofBijective _ hbij))
  have hlen : ((numsCode.eval x).map unaryVal).length
      = (dedupTriples.eval x).length * 4 := by
    rw [numsCode_map_val x hXW hYW, List.length_flatMap]
    exact sum_map_const fun t _ ↦ rfl
  -- the position bijection for the tagged element type, by its formula
  obtain ⟨E', hEval⟩ : ∃ e : ↥(decodeMatching3D x).triples × Fin 4 ≃
        Fin ((numsCode.eval x).map unaryVal).length,
      ∀ (th : ↥(decodeMatching3D x).triples) (c : Fin 4),
        (e (th, c)).val
          = (dedupTriples.eval x).idxOf (pval th) * 4 + Fin.val c :=
    ⟨((Numbering.ofEquiv (Equiv.ofBijective _ hbij)).prod
        (Numbering.fin 4)).equivFin.trans (finCongr hlen.symm),
      fun th c ↦ rfl⟩
  -- the emitted number at a tagged position is the constructed size
  have hfin4 : ∀ c : Fin 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by decide
  have hpoint : ∀ p : ↥(decodeMatching3D x).triples × Fin 4,
      ((numsCode.eval x).map unaryVal)[(E' p).val]?
        = some (mfpSize (mfpRVal x) Fin.val Fin.val Fin.val
            (fun w ↦ (pw w).val) (fun xe ↦ (px xe).val)
            (fun ye ↦ (py ye).val) (decodeMatching3D x).triples p) := by
    rintro ⟨th, c⟩
    rw [hEval th c, numsCode_map_val x hXW hYW]
    obtain ⟨q0, q1, q2, q3⟩ := getElem?_flatMap_four
      (fun t : TripleTy.denote ↦ 10 * mfpRVal x ^ 4 + 8
        - (t.2.2 * mfpRVal x ^ 3 + t.2.1 * mfpRVal x ^ 2 + t.1 * mfpRVal x))
      (fun t : TripleTy.denote ↦
        (if t = (matchedW x t.1).headI then (10 : ℕ) else 11) * mfpRVal x ^ 4
          + t.1 * mfpRVal x + 1)
      (fun t : TripleTy.denote ↦
        (if t = (matchedX x t.2.1).headI then (10 : ℕ) else 11) * mfpRVal x ^ 4
          + t.2.1 * mfpRVal x ^ 2 + 2)
      (fun t : TripleTy.denote ↦
        (if t = (matchedY x t.2.2).headI then (10 : ℕ) else 8) * mfpRVal x ^ 4
          + t.2.2 * mfpRVal x ^ 3 + 4)
      (dedupTriples.eval x) ((dedupTriples.eval x).idxOf (pval th))
    have hDk : (dedupTriples.eval x)[(dedupTriples.eval x).idxOf (pval th)]?
        = some (pval th) := List.getElem?_idxOf (hvals_mem th)
    rcases hfin4 c with rfl | rfl | rfl | rfl
    · rw [show Fin.val (0 : Fin 4) = 0 from rfl, Nat.add_zero,
        Nat.mul_comm ((dedupTriples.eval x).idxOf (pval th)) 4]
      refine q0.trans ?_
      rw [hDk]
      rfl
    · rw [show Fin.val (1 : Fin 4) = 1 from rfl,
        Nat.mul_comm ((dedupTriples.eval x).idxOf (pval th)) 4]
      refine q1.trans ?_
      rw [hDk]
      refine congrArg some ?_
      change _ = mfpWSize (mfpRVal x) Fin.val (fun w ↦ (pw w).val) th.val
      unfold mfpWSize
      simp only [show (pval th).1 = Fin.val th.val.1 from rfl, (hdesW th).symm]
      rfl
    · rw [show Fin.val (2 : Fin 4) = 2 from rfl,
        Nat.mul_comm ((dedupTriples.eval x).idxOf (pval th)) 4]
      refine q2.trans ?_
      rw [hDk]
      refine congrArg some ?_
      change _ = mfpXSize (mfpRVal x) Fin.val (fun xe ↦ (px xe).val) th.val
      unfold mfpXSize
      simp only [show (pval th).2.1 = Fin.val th.val.2.1 from rfl,
        (hdesX th).symm]
      rfl
    · rw [show Fin.val (3 : Fin 4) = 3 from rfl,
        Nat.mul_comm ((dedupTriples.eval x).idxOf (pval th)) 4]
      refine q3.trans ?_
      rw [hDk]
      refine congrArg some ?_
      change _ = mfpYSize (mfpRVal x) Fin.val (fun ye ↦ (py ye).val) th.val
      unfold mfpYSize
      simp only [show (pval th).2.2 = Fin.val th.val.2.2 from rfl,
        (hdesY th).symm]
      rfl
  have hgetp : ∀ i : Fin ((numsCode.eval x).map unaryVal).length,
      ((numsCode.eval x).map unaryVal)[Fin.val i]
        = mfpSize (mfpRVal x) Fin.val Fin.val Fin.val (fun w ↦ (pw w).val)
            (fun xe ↦ (px xe).val) (fun ye ↦ (py ye).val)
            (decodeMatching3D x).triples (E'.symm i) := by
    intro i
    have h := hpoint (E'.symm i)
    rw [Equiv.apply_symm_apply] at h
    rw [List.getElem?_eq_getElem (Fin.isLt i)] at h
    exact Option.some_inj.mp h
  have hfun : (fun i : Fin ((numsCode.eval x).map unaryVal).length ↦
        mfpSize (mfpRVal x) Fin.val Fin.val Fin.val (fun w ↦ (pw w).val)
          (fun xe ↦ (px xe).val) (fun ye ↦ (py ye).val)
          (decodeMatching3D x).triples (E'.symm i))
      = fun i ↦ ((numsCode.eval x).map unaryVal)[Fin.val i] :=
    funext fun i ↦ (hgetp i).symm
  -- transport: 4-PARTITION of the emitted instance is the tagged question
  have htrans : Hardness.FOUR_PARTITION
        ⟨(numsCode.eval x).map unaryVal, mfpB (mfpRVal x)⟩ ↔
      ∃ parts : Finset (Finset (↥(decodeMatching3D x).triples × Fin 4)),
        IsSizedPartition (mfpSize (mfpRVal x) Fin.val Fin.val Fin.val
            (fun w ↦ (pw w).val) (fun xe ↦ (px xe).val)
            (fun ye ↦ (py ye).val) (decodeMatching3D x).triples) 4
          (mfpB (mfpRVal x)) parts := by
    refine Iff.trans ?_ (exists_isSizedPartition_iff_map E' _ 4 _).symm
    rw [hfun]
    unfold Hardness.FOUR_PARTITION
    exact Iff.rfl
  have hdec : decodeNumberTargetUnary (numsCode.eval x, targetCode.eval x)
      = ⟨(numsCode.eval x).map unaryVal, mfpB (mfpRVal x)⟩ := by
    rw [← targetCode_val x]
    rfl
  rw [hdec]
  constructor
  · -- the reduction's iff, through the transport
    rw [htrans]
    constructor
    · rintro ⟨M, hMT, hMW, hMX, hMY⟩
      exact exists_isSizedPartition_of_matching hiW hiX hiY hpW hpX hpY hMT
        hMW hMX hMY
    · rintro ⟨parts, hparts⟩
      exact exists_matching_of_isSizedPartition h33 hiW hiX hiY hinjW hinjX
        hinjY hpW hpX hpY hparts
  · -- the window
    unfold FourPartitionWindow
    dsimp only
    constructor
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
      have h' : ((numsCode.eval x).map unaryVal)[i]
          = mfpSize (mfpRVal x) Fin.val Fin.val Fin.val (fun w ↦ (pw w).val)
              (fun xe ↦ (px xe).val) (fun ye ↦ (py ye).val)
              (decodeMatching3D x).triples (E'.symm ⟨i, hi⟩) := hgetp ⟨i, hi⟩
      rw [h']
      exact mfp_window h33 hq33 hiWq hiXq hiYq _
    · have hcW : Fintype.card (decodeMatching3D x).W = x.1.length :=
        Fintype.card_fin _
      have hcX : Fintype.card (decodeMatching3D x).X = x.2.1.length :=
        Fintype.card_fin _
      have hcY : Fintype.card (decodeMatching3D x).Y = x.2.2.1.length :=
        Fintype.card_fin _
      have hL : ((numsCode.eval x).map unaryVal).sum
          = ∑ i : Fin ((numsCode.eval x).map unaryVal).length,
              ((numsCode.eval x).map unaryVal)[Fin.val i] := by
        conv_lhs => rw [← List.ofFn_getElem
          (xs := (numsCode.eval x).map unaryVal)]
        exact List.sum_ofFn
      have hsum3 : ∑ i : Fin ((numsCode.eval x).map unaryVal).length,
            ((numsCode.eval x).map unaryVal)[Fin.val i]
          = ∑ p : ↥(decodeMatching3D x).triples × Fin 4,
              ((numsCode.eval x).map unaryVal)[Fin.val (E' p)] :=
        (Equiv.sum_comp E'
          fun i ↦ ((numsCode.eval x).map unaryVal)[Fin.val i]).symm
      have hsum2 : ∑ p : ↥(decodeMatching3D x).triples × Fin 4,
            ((numsCode.eval x).map unaryVal)[Fin.val (E' p)]
          = ∑ p : ↥(decodeMatching3D x).triples × Fin 4,
              mfpSize (mfpRVal x) Fin.val Fin.val Fin.val
                (fun w ↦ (pw w).val) (fun xe ↦ (px xe).val)
                (fun ye ↦ (py ye).val) (decodeMatching3D x).triples p :=
        Finset.sum_congr rfl fun p _ ↦ by
          have h := hgetp (E' p)
          rw [Equiv.symm_apply_apply] at h
          exact h
      have hsum1 : ∑ p : ↥(decodeMatching3D x).triples × Fin 4,
            mfpSize (mfpRVal x) Fin.val Fin.val Fin.val (fun w ↦ (pw w).val)
              (fun xe ↦ (px xe).val) (fun ye ↦ (py ye).val)
              (decodeMatching3D x).triples p
          = Fintype.card ↥(decodeMatching3D x).triples * mfpB (mfpRVal x) :=
        mfp_total_sum hiW hiX hiY hpW hpX hpY (by rw [hcX, hcW]; exact hXW)
          (by rw [hcY, hcW]; exact hYW)
      rw [hL, hsum3, hsum2, hsum1, hcardT, hlen]
      ring

/-- The degenerate branch's output, decoded: the parity no-instance of the
mathematical layer. -/
theorem decode_noInstance :
    decodeNumberTargetUnary noInstance = ⟨[6, 6, 6, 6, 6, 8, 8, 8], 27⟩ := rfl

end MfpCode

/-! ## The certificate -/

/-- The program's two obligations at once: on the decoded output, 4-PARTITION
answers 3-DIMENSIONAL MATCHING, and the output always sits inside the
Garey–Johnson window. Both branches deliver both — the parity no-instance is
chosen so that it, too, is windowed. -/
theorem matching3DToFourPartitionCode_spec (x : Matching3DTy.denote) :
    (Concrete.MATCHING_3D x ↔
        Concrete.FOUR_PARTITION_UNARY (matching3DToFourPartitionCode.eval x)) ∧
      FourPartitionWindow
        (decodeNumberTargetUnary (matching3DToFourPartitionCode.eval x)) := by
  by_cases hg : MfpCode.goodInstance.eval x = true
  · have hgood := (MfpCode.goodInstance_eval_true_iff x).mp hg
    have hcW : Fintype.card (decodeMatching3D x).W = x.1.length :=
      Fintype.card_fin _
    have hcX : Fintype.card (decodeMatching3D x).X = x.2.1.length :=
      Fintype.card_fin _
    have hcY : Fintype.card (decodeMatching3D x).Y = x.2.2.1.length :=
      Fintype.card_fin _
    have hXW : x.2.1.length = x.1.length := by rw [← hcX, ← hcW]; exact hgood.1
    have hYW : x.2.2.1.length = x.1.length := by
      rw [← hcY, ← hcW]; exact hgood.2.1
    have heval : matching3DToFourPartitionCode.eval x
        = (MfpCode.numsCode.eval x, MfpCode.targetCode.eval x) :=
      branch_eval_true _ _ hg
    rw [heval]
    exact MfpCode.good_branch x hXW hYW hgood.2.2.1 hgood.2.2.2.1 hgood.2.2.2.2
  · have hgf : MfpCode.goodInstance.eval x = false := by simpa using hg
    have heval : matching3DToFourPartitionCode.eval x = MfpCode.noInstance :=
      branch_eval_false _ _ hgf
    rw [heval, MfpCode.decode_noInstance]
    refine ⟨iff_of_false (fun hm ↦ hg ((MfpCode.goodInstance_eval_true_iff x).mpr
      (matching3DGood_of_matching hm))) ?_, by decide, by decide⟩
    change ¬ Hardness.FOUR_PARTITION (decodeNumberTargetUnary MfpCode.noInstance)
    rw [MfpCode.decode_noInstance]
    exact not_fourPartition_parityNo

/-- **The bridged reduction**: 3-DIMENSIONAL MATCHING reduces to 4-PARTITION
on unary instances, and the reduction lands inside the Garey–Johnson window —
the sharp form, matching `matching3DToFourPartition` of the mathematical
layer. Polynomial bounds come from the generic theorem; because the target is
the *unary* avatar, they are bounds in the emitted numbers' values, which is
what strong NP-hardness asks for. -/
def matching3DToFourPartitionCertified :
    CertifiedReduction Concrete.MATCHING_3D
      Concrete.FOUR_PARTITION_UNARY_WINDOW where
  code := matching3DToFourPartitionCode
  correct x :=
    ⟨fun hm ↦ ⟨(matching3DToFourPartitionCode_spec x).2,
        (matching3DToFourPartitionCode_spec x).1.mp hm⟩,
      fun hq ↦ (matching3DToFourPartitionCode_spec x).1.mpr hq.2⟩

/-- The same certificate, read against the unrestricted target. -/
def matching3DToFourPartitionUnaryCertified :
    CertifiedReduction Concrete.MATCHING_3D Concrete.FOUR_PARTITION_UNARY where
  code := matching3DToFourPartitionCode
  correct x := (matching3DToFourPartitionCode_spec x).1

/-- Sanity check: the certified reduction projects to a plain reduction. -/
example : Concrete.MATCHING_3D ⟶ᵣ Concrete.FOUR_PARTITION_UNARY_WINDOW :=
  matching3DToFourPartitionCertified.toReduction

end Cert
end Hardness
