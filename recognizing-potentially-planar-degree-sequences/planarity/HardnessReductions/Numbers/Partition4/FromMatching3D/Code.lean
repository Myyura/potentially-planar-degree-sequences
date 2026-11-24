import HardnessReductions.Numbers.Encoding
import HardnessReductions.Sets.Matching3D.Encoding

/-!
# 3-dimensional matching → 4-PARTITION: the program

The instance map of `Partition4/FromMatching3D.lean` as a `Code` program,
targeting the *unary* concrete 4-PARTITION (`NumberTargetUnaryTy`): the
emitted numbers have magnitude polynomial in the instance, and charging them
by value is exactly what the unary encoding does — this is the strong
NP-hardness reading. All unary values are built through the sugar of
`Numbers/Unary/Code.lean`, so the adequacy proof
(`FromMatching3D/Adequacy.lean`) works entirely in `ℕ` through the
`unaryVal` simp set.

The program mirrors the mathematical construction piece by piece:

* *sanitize*: triples with an out-of-range index name nothing in the decoded
  instance and are dropped (`goodTriples`); duplicates collapse as the
  decoded `Finset` collapses them (`dedupTriples`);
* *branch*: equal element counts and full coverage, recomputed concretely
  (`goodInstance`); offenders map to the parity no-instance;
* *emit*: per surviving triple the four sizes, as unary numerals — the
  index-times-power terms cross from binary indices to unary lengths through
  `unaryOfBounded`, the sanctioned crossing, bounded by the element lists;
* the *designation* of actual copies is "the first surviving triple through
  the element", which the adequacy proof feeds to the parametric
  correctness lemmas as their `pW pX pY`.
-/

namespace Hardness
namespace Cert

namespace MfpCode

/-! ## Accessors -/

/-- The `W`-element list of a concrete 3DM instance. -/
def wsOf : Code Matching3DTy (.list .nat) := .fst

/-- The `X`-element list. -/
def xsOf : Code Matching3DTy (.list .nat) := .comp .snd .fst

/-- The `Y`-element list. -/
def ysOf : Code Matching3DTy (.list .nat) := .comp (.comp .snd .snd) .fst

/-- The triple list. -/
def tsOf : Code Matching3DTy (.list TripleTy) := .comp (.comp .snd .snd) .snd

/-! ## Sanitizing -/

/-- Equality of concrete triples, coordinatewise. -/
def tripleEq : Code (.pair TripleTy TripleTy) .bool :=
  Code.and (.comp (.pair (.comp .fst .fst) (.comp .snd .fst)) .natEq)
    (Code.and
      (.comp (.pair (.comp .fst (.comp .snd .fst))
        (.comp .snd (.comp .snd .fst))) .natEq)
      (.comp (.pair (.comp .fst (.comp .snd .snd))
        (.comp .snd (.comp .snd .snd))) .natEq))

theorem tripleEq_eval (s t : TripleTy.denote) :
    tripleEq.eval (s, t) = decide (s = t) := by
  have h : tripleEq.eval (s, t)
      = (decide (s.1 = t.1) && (decide (s.2.1 = t.2.1) &&
          decide (s.2.2 = t.2.2))) := rfl
  rw [h, ← Bool.decide_and, ← Bool.decide_and, decide_eq_decide]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact Prod.ext h1 (Prod.ext h2 h3)
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩

/-- In-range test for a triple, against the three element lists riding in the
environment. -/
def goodTest : Code (.pair Matching3DTy TripleTy) .bool :=
  Code.and (Code.lt (.comp .snd .fst) (.comp (.comp .fst wsOf) .listLen))
    (Code.and
      (Code.lt (.comp .snd (.comp .snd .fst))
        (.comp (.comp .fst xsOf) .listLen))
      (Code.lt (.comp .snd (.comp .snd .snd))
        (.comp (.comp .fst ysOf) .listLen)))

theorem goodTest_eval (x : Matching3DTy.denote) (t : TripleTy.denote) :
    goodTest.eval (x, t)
      = (decide (t.1 < x.1.length) && (decide (t.2.1 < x.2.1.length) &&
          decide (t.2.2 < x.2.2.1.length))) := by
  have h : goodTest.eval (x, t)
      = (Code.natLt.eval (t.1, x.1.length) &&
          (Code.natLt.eval (t.2.1, x.2.1.length) &&
            Code.natLt.eval (t.2.2, x.2.2.1.length))) := rfl
  rw [h, natLt_eval, natLt_eval, natLt_eval]

/-- The surviving (in-range) triples. -/
def goodTriples : Code Matching3DTy (.list TripleTy) :=
  .comp (.pair .id tsOf) (Code.filterEnv goodTest)

theorem goodTriples_eval (x : Matching3DTy.denote) :
    goodTriples.eval x = x.2.2.2.filter fun t ↦
      decide (t.1 < x.1.length) && (decide (t.2.1 < x.2.1.length) &&
        decide (t.2.2 < x.2.2.1.length)) := by
  have h : goodTriples.eval x
      = (Code.filterEnv goodTest).eval (x, x.2.2.2) := rfl
  rw [h, filterEnv_eval]
  exact List.filter_congr fun t _ ↦ goodTest_eval x t

theorem mem_goodTriples_eval (x : Matching3DTy.denote) (t : TripleTy.denote) :
    t ∈ goodTriples.eval x ↔ t ∈ x.2.2.2 ∧ t.1 < x.1.length ∧
      t.2.1 < x.2.1.length ∧ t.2.2 < x.2.2.1.length := by
  rw [goodTriples_eval, List.mem_filter]
  simp

/-- The surviving triples, deduplicated — one entry per element of the
decoded triple set. -/
def dedupTriples : Code Matching3DTy (.list TripleTy) :=
  .comp goodTriples (Code.dedupBy tripleEq)

theorem dedupTriples_eval (x : Matching3DTy.denote) :
    dedupTriples.eval x = (goodTriples.eval x).dedup := by
  have h : dedupTriples.eval x
      = (Code.dedupBy tripleEq).eval (goodTriples.eval x) := rfl
  rw [h, dedupBy_eval tripleEq_eval]

theorem mem_dedupTriples_eval (x : Matching3DTy.denote) (t : TripleTy.denote) :
    t ∈ dedupTriples.eval x ↔ t ∈ x.2.2.2 ∧ t.1 < x.1.length ∧
      t.2.1 < x.2.1.length ∧ t.2.2 < x.2.2.1.length := by
  rw [dedupTriples_eval, List.mem_dedup, mem_goodTriples_eval]

theorem nodup_dedupTriples_eval (x : Matching3DTy.denote) :
    (dedupTriples.eval x).Nodup := by
  rw [dedupTriples_eval]
  exact List.nodup_dedup _

/-! ## The branch condition -/

/-- First-coordinate hit test: the enumerated triple's `W`-index equals the
element index in the environment. -/
def fstEq : Code (.pair .nat TripleTy) .bool :=
  .comp (.pair .fst (.comp .snd .fst)) .natEq

theorem fstEq_eval (i : ℕ) (t : TripleTy.denote) :
    fstEq.eval (i, t) = decide (i = t.1) := rfl

/-- Second-coordinate hit test. -/
def sndEq : Code (.pair .nat TripleTy) .bool :=
  .comp (.pair .fst (.comp .snd (.comp .snd .fst))) .natEq

theorem sndEq_eval (j : ℕ) (t : TripleTy.denote) :
    sndEq.eval (j, t) = decide (j = t.2.1) := rfl

/-- Third-coordinate hit test. -/
def trdEq : Code (.pair .nat TripleTy) .bool :=
  .comp (.pair .fst (.comp .snd (.comp .snd .snd))) .natEq

theorem trdEq_eval (k : ℕ) (t : TripleTy.denote) :
    trdEq.eval (k, t) = decide (k = t.2.2) := rfl

/-- The triples of a list hitting a given element index along a coordinate
test. -/
def matchesAt (coordEq : Code (.pair .nat TripleTy) .bool) :
    Code (.pair (.list TripleTy) .nat) (.list TripleTy) :=
  .comp (.pair .snd .fst) (Code.filterEnv coordEq)

theorem matchesAt_eval (coordEq : Code (.pair .nat TripleTy) .bool)
    (D : List TripleTy.denote) (i : ℕ) :
    (matchesAt coordEq).eval (D, i) = D.filter fun t ↦ coordEq.eval (i, t) := by
  have h : (matchesAt coordEq).eval (D, i)
      = (Code.filterEnv coordEq).eval (i, D) := rfl
  rw [h, filterEnv_eval]

/-- Uncovered test: no triple of the list hits the element index. -/
def uncovTest (coordEq : Code (.pair .nat TripleTy) .bool) :
    Code (.pair (.list TripleTy) .nat) .bool :=
  .comp (.pair (.comp (matchesAt coordEq) .listLen) (.const .nat 0)) .natEq

theorem uncovTest_eval_true (coordEq : Code (.pair .nat TripleTy) .bool)
    (D : List TripleTy.denote) (i : ℕ) :
    (uncovTest coordEq).eval (D, i) = true ↔
      ∀ t ∈ D, ¬ (coordEq.eval (i, t) = true) := by
  have h : (uncovTest coordEq).eval (D, i)
      = decide (((matchesAt coordEq).eval (D, i)).length = 0) := rfl
  rw [h, decide_eq_true_iff, matchesAt_eval, List.length_eq_zero_iff,
    List.filter_eq_nil_iff]

/-- The uncovered `W`-element indices. -/
def uncoveredW : Code Matching3DTy (.list .nat) :=
  .comp (.pair goodTriples (.comp wsOf Code.indices))
    (Code.filterEnv (uncovTest fstEq))

/-- The uncovered `X`-element indices. -/
def uncoveredX : Code Matching3DTy (.list .nat) :=
  .comp (.pair goodTriples (.comp xsOf Code.indices))
    (Code.filterEnv (uncovTest sndEq))

/-- The uncovered `Y`-element indices. -/
def uncoveredY : Code Matching3DTy (.list .nat) :=
  .comp (.pair goodTriples (.comp ysOf Code.indices))
    (Code.filterEnv (uncovTest trdEq))

/-- The branch condition: equal element counts, and no uncovered element in
any coordinate. -/
def goodInstance : Code Matching3DTy .bool :=
  Code.and
    (.comp (.pair (.comp wsOf .listLen) (.comp xsOf .listLen)) .natEq)
    (Code.and
      (.comp (.pair (.comp wsOf .listLen) (.comp ysOf .listLen)) .natEq)
      (Code.and (Code.isNil uncoveredW)
        (Code.and (Code.isNil uncoveredX) (Code.isNil uncoveredY))))

/-! ## The sizes -/

/-- The radix, as a unary numeral: `33 · (|ws| + 1)`. -/
def radix : Code Matching3DTy .unary :=
  umul (unaryConst 33) (uadd (.comp wsOf unaryOfList) (unaryConst 1))

theorem radix_val (x : Matching3DTy.denote) :
    unaryVal (radix.eval x) = 33 * (x.1.length + 1) := by
  unfold radix
  rw [umul_eval, uadd_eval, unaryConst_eval, unaryConst_eval]
  have hws : unaryVal ((Code.comp wsOf unaryOfList).eval x) = x.1.length := by
    have h2 : (Code.comp wsOf unaryOfList).eval x = unaryOfList.eval x.1 := rfl
    rw [h2, unaryOfList_eval]
  rw [hws]

/-- The four radix powers, in the environment of the per-triple map: with
input `(x, t)`, the radix of `x` multiplied out. -/
def rpow1 : Code (.pair Matching3DTy TripleTy) .unary := .comp .fst radix

/-- `r²`. -/
def rpow2 : Code (.pair Matching3DTy TripleTy) .unary := umul rpow1 rpow1

/-- `r³`. -/
def rpow3 : Code (.pair Matching3DTy TripleTy) .unary := umul rpow2 rpow1

/-- `r⁴`. -/
def rpow4 : Code (.pair Matching3DTy TripleTy) .unary := umul rpow2 rpow2

/-- The triple's `W`-index, as a unary numeral bounded by the `W`-list. -/
def uIdxW : Code (.pair Matching3DTy TripleTy) .unary :=
  .comp (.pair (.comp .snd .fst) (.comp .fst wsOf)) unaryOfBounded

/-- The triple's `X`-index, unary. -/
def uIdxX : Code (.pair Matching3DTy TripleTy) .unary :=
  .comp (.pair (.comp .snd (.comp .snd .fst)) (.comp .fst xsOf)) unaryOfBounded

/-- The triple's `Y`-index, unary. -/
def uIdxY : Code (.pair Matching3DTy TripleTy) .unary :=
  .comp (.pair (.comp .snd (.comp .snd .snd)) (.comp .fst ysOf)) unaryOfBounded

/-- The first surviving triple hitting the current triple's element along a
coordinate — the *designated* (actual) occurrence of that element. -/
def firstAt (coordEq : Code (.pair .nat TripleTy) .bool)
    (idx : Code (.pair Matching3DTy TripleTy) .nat) :
    Code (.pair Matching3DTy TripleTy) (.list TripleTy) :=
  .comp (.pair (.comp (.pair (.comp .fst dedupTriples) idx)
    (matchesAt coordEq)) (.const .nat 0)) Code.listNth

/-- Is the current triple the designated occurrence of its element? -/
def isActAt (coordEq : Code (.pair .nat TripleTy) .bool)
    (idx : Code (.pair Matching3DTy TripleTy) .nat) :
    Code (.pair Matching3DTy TripleTy) .bool :=
  .comp (.pair (.comp (.comp (.pair .snd (firstAt coordEq idx))
    (Code.filterEnv tripleEq)) .listLen) (.const .nat 1)) .natEq

/-- The leading term of a copy's size: the actual/dummy coefficient times
`r⁴`. -/
def leadTerm (coordEq : Code (.pair .nat TripleTy) .bool)
    (idx : Code (.pair Matching3DTy TripleTy) .nat) (act dum : ℕ) :
    Code (.pair Matching3DTy TripleTy) .unary :=
  .branch (isActAt coordEq idx) (umul (unaryConst act) rpow4)
    (umul (unaryConst dum) rpow4)

/-- The `W`-copy's size: `c_w·r⁴ + i·r + 1`. -/
def wSizeCode : Code (.pair Matching3DTy TripleTy) .unary :=
  uadd (leadTerm fstEq (.comp .snd .fst) 10 11)
    (uadd (umul uIdxW rpow1) (unaryConst 1))

/-- The `X`-copy's size: `c_x·r⁴ + j·r² + 2`. -/
def xSizeCode : Code (.pair Matching3DTy TripleTy) .unary :=
  uadd (leadTerm sndEq (.comp .snd (.comp .snd .fst)) 10 11)
    (uadd (umul uIdxX rpow2) (unaryConst 2))

/-- The `Y`-copy's size: `c_y·r⁴ + k·r³ + 4`. -/
def ySizeCode : Code (.pair Matching3DTy TripleTy) .unary :=
  uadd (leadTerm trdEq (.comp .snd (.comp .snd .snd)) 10 8)
    (uadd (umul uIdxY rpow3) (unaryConst 4))

/-- The triple element's size: `(10·r⁴ − (k·r³ + j·r² + i·r)) + 8`. -/
def uSizeCode : Code (.pair Matching3DTy TripleTy) .unary :=
  uadd (usub (umul (unaryConst 10) rpow4)
      (uadd (umul uIdxY rpow3) (uadd (umul uIdxX rpow2) (umul uIdxW rpow1))))
    (unaryConst 8)

/-- The four sizes of one triple, in kind order. -/
def blockOf : Code (.pair Matching3DTy TripleTy) (.list .unary) :=
  Code.cons uSizeCode (Code.cons wSizeCode
    (Code.cons xSizeCode (.comp ySizeCode .listSingle)))

/-- All the numbers: four per surviving triple, flattened. -/
def numsCode : Code Matching3DTy (.list .unary) :=
  .comp (.comp (.pair .id dedupTriples) (.listMapEnv blockOf)) .listJoin

/-- The bound: `40·r⁴ + 15`, unary. -/
def targetCode : Code Matching3DTy .unary :=
  uadd (umul (unaryConst 40) (umul (umul radix radix) (umul radix radix)))
    (unaryConst 15)

/-- The parity no-instance, unary-encoded. -/
def noInstance : NumberTargetUnaryTy.denote :=
  ([List.replicate 6 true, List.replicate 6 true, List.replicate 6 true,
    List.replicate 6 true, List.replicate 6 true, List.replicate 8 true,
    List.replicate 8 true, List.replicate 8 true], List.replicate 27 true)

end MfpCode

/-- The program: 3-DIMENSIONAL MATCHING → 4-PARTITION, unary target. -/
def matching3DToFourPartitionCode : Code Matching3DTy NumberTargetUnaryTy :=
  .branch MfpCode.goodInstance (.pair MfpCode.numsCode MfpCode.targetCode)
    (.const NumberTargetUnaryTy MfpCode.noInstance)

end Cert
end Hardness
