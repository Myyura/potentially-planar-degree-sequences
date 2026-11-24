import HardnessReductions.Cert.Language
import HardnessReductions.Numbers.Unary

/-!
# Unary arithmetic, as programs

The program-level surface for unary-encoded numbers (`Numbers/Unary.lean`):
the type `Ty.unary`, derived combinators for building unary values, and one
eval lemma per combinator. Every combinator is a plain `def` over existing
constructors, so cost and size bounds come from the blanket theorem for free;
the eval lemma is the only per-combinator obligation.

## The eval-lemma discipline

Every lemma is phrased through `unaryVal`, never through list structure —
`unaryVal (unaryMul.eval (a, b)) = unaryVal a * unaryVal b` — and the
collection is a simp set. An adequacy proof simps program values down to `ℕ`
expressions and finishes with `omega`/`ring`; the list layer exists only
inside the eval lemmas' one-line proofs.

**Strict rule**: annexes build unary values *only* through this surface, so
the simp set stays complete by construction. A missing operation forces a
sugar addition here (with its `unaryVal` lemma), not an inline drop to raw
list combinators. An override is a recorded decision
(`materials/unary-design-2026-07-21.md`), not an inline workaround.

`unaryConst` is for small fixed gadget literals only — `Code.const` charges
the value's size, so an instance-dependent value must never route through it.
There is deliberately no `natToUnary` in any form: its impossibility is the
theorem `no_binary_to_unary` (`Numbers/Representation.lean`).
-/

namespace Hardness
namespace Cert

/-- Unary numbers at the type level: a unary `n` is a list of length `n`.
Deliberately an `abbrev` of an existing `Ty`, not a new constructor — a new
universe case would cost a case in every engine induction and buy only what
naming discipline already provides. -/
abbrev Ty.unary : Ty := .list .bool

/-- *Count* a list: the unary number whose value is the input's length. The
expected workhorse — gadget numbers arise as counts of input objects. -/
def unaryOfList {τ : Ty} : Code (.list τ) .unary := .listMap (.const .bool true)

/-- Unary addition is append. -/
def unaryAdd : Code (.pair .unary .unary) .unary := .listAppend

/-- Unary multiplication: one copy of the first factor per element of the
second, flattened. -/
def unaryMul : Code (.pair .unary .unary) .unary :=
  .comp (.listMapEnv .fst) .listJoin

/-- The unary `listSum` is literally flatten — the sanity check that the
encoding is right. -/
def unarySum : Code (.list .unary) .unary := .listJoin

/-- A fixed unary literal. For small gadget constants only: `Code.const`
charges the value's size, so this must never carry an instance-dependent
value. -/
def unaryConst {σ : Ty} (n : ℕ) : Code σ .unary :=
  .const .unary (List.replicate n true)

/-- The certified unary → binary direction: read off the length. The reverse
direction is not a program (`no_binary_to_unary`,
`Numbers/Representation.lean`). -/
def unaryToNat : Code .unary .nat := .listLen

/-- Unary subtraction: keep the elements of the minuend sitting at or beyond
the subtrahend's value. The comparison reads the subtrahend's *binary* value,
which is harmless — only the minuend's length drives the output, so the cost
stays honest. Truncated at zero, as `Nat` subtraction is. -/
def unarySub : Code (.pair .unary .unary) .unary :=
  .comp (.pair (.comp .snd .listLen) (.comp .fst .listEnum))
    (.comp (Code.filterEnv (.comp Code.prefixTest .boolNot))
      (.listMap (.const .bool true)))

/-- Unary of a *bounded* binary value: the value `n`, materialized as the
positions of the bounding list strictly before `n`. This is the sanctioned
crossing from binary to unary: the language's "no `range` primitive" rule
forbids materializing a length from a binary value alone, and here the cost
is carried by the bounding list instead — `min n l.length` elements come out,
so `n` never drives iteration. -/
def unaryOfBounded {τ : Ty} : Code (.pair .nat (.list τ)) .unary :=
  .comp (.pair .fst (.comp .snd .listEnum))
    (.comp (Code.filterEnv Code.prefixTest) (.listMap (.const .bool true)))

/-! ## Applied forms

The pointwise variants annex programs compose with, mirroring `Code.add` /
`Code.mul` for the binary combinators. -/

/-- Applied unary addition. -/
def uadd {σ : Ty} (a b : Code σ .unary) : Code σ .unary :=
  .comp (.pair a b) unaryAdd

/-- Applied unary multiplication. -/
def umul {σ : Ty} (a b : Code σ .unary) : Code σ .unary :=
  .comp (.pair a b) unaryMul

/-- Applied unary subtraction. -/
def usub {σ : Ty} (a b : Code σ .unary) : Code σ .unary :=
  .comp (.pair a b) unarySub

/-! ## The eval simp set -/

@[simp] theorem unaryOfList_eval {τ : Ty} (l : List τ.denote) :
    unaryVal (unaryOfList.eval l) = l.length := by
  simp [unaryOfList, unaryVal, Code.eval]

@[simp] theorem unaryAdd_eval (a b : List Bool) :
    unaryVal (unaryAdd.eval (a, b)) = unaryVal a + unaryVal b :=
  List.length_append

@[simp] theorem unaryMul_eval (a b : List Bool) :
    unaryVal (unaryMul.eval (a, b)) = unaryVal a * unaryVal b := by
  simp [unaryMul, unaryVal, Code.eval, Nat.mul_comm]

@[simp] theorem unarySum_eval (L : List (List Bool)) :
    unaryVal (unarySum.eval L) = (L.map unaryVal).sum := by
  simp only [unarySum, unaryVal, Code.eval, List.length_flatten]
  rfl

@[simp] theorem unaryConst_eval {σ : Ty} (n : ℕ) (x : σ.denote) :
    unaryVal ((unaryConst n : Code σ .unary).eval x) = n := by
  simp [unaryConst, unaryVal, Code.eval]

@[simp] theorem unaryToNat_eval (u : List Bool) :
    unaryToNat.eval u = unaryVal u := rfl

@[simp] theorem unarySub_eval (a b : List Bool) :
    unaryVal (unarySub.eval (a, b)) = unaryVal a - unaryVal b := by
  have h : unarySub.eval (a, b)
      = ((Code.filterEnv (.comp (Code.prefixTest (τ := .bool))
          Code.boolNot)).eval (b.length, a.zipIdx)).map fun _ ↦ true := rfl
  rw [h, filterEnv_eval]
  have hpred : ∀ q : Bool × ℕ,
      (Code.comp (Code.prefixTest (τ := .bool)) Code.boolNot).eval
        (b.length, q) = !decide (q.2 < b.length) := by
    intro q
    have : (Code.comp (Code.prefixTest (τ := .bool)) Code.boolNot).eval
        (b.length, q) = !(Code.prefixTest (τ := .bool)).eval (b.length, q) :=
      rfl
    rw [this, prefixTest_eval]
  unfold unaryVal
  rw [List.length_map]
  have hcongr : (a.zipIdx.filter fun q ↦
      (Code.comp (Code.prefixTest (τ := .bool)) Code.boolNot).eval
        (b.length, q)).length
      = (a.zipIdx.filter fun q ↦ !decide (q.2 < b.length)).length := by
    rw [List.filter_congr fun q _ ↦ hpred q]
  rw [hcongr]
  have hlt := length_filter_zipIdx_lt a b.length
  have hzlen : a.zipIdx.length = a.length := List.length_zipIdx
  have hkey : (a.zipIdx.filter fun q ↦ !decide (q.2 < b.length)).length
      + (a.zipIdx.filter fun q ↦ decide (q.2 < b.length)).length
      = a.zipIdx.length := by
    have hc := List.length_eq_countP_add_countP
      (fun q : Bool × ℕ ↦ decide (q.2 < b.length)) (l := a.zipIdx)
    simp only [List.countP_eq_length_filter, decide_not, decide_eq_true_eq] at hc
    omega
  omega

@[simp] theorem unaryOfBounded_eval {τ : Ty} (n : ℕ) (l : List τ.denote) :
    unaryVal ((unaryOfBounded (τ := τ)).eval (n, l)) = min n l.length := by
  have h : (unaryOfBounded (τ := τ)).eval (n, l)
      = ((Code.filterEnv (Code.prefixTest (τ := τ))).eval
          (n, l.zipIdx)).map fun _ ↦ true := rfl
  rw [h, prefixTest_filterEnv_eval]
  unfold unaryVal
  rw [List.length_map, length_filter_zipIdx_lt]

@[simp] theorem uadd_eval {σ : Ty} (a b : Code σ .unary) (x : σ.denote) :
    unaryVal ((uadd a b).eval x) = unaryVal (a.eval x) + unaryVal (b.eval x) :=
  unaryAdd_eval _ _

@[simp] theorem umul_eval {σ : Ty} (a b : Code σ .unary) (x : σ.denote) :
    unaryVal ((umul a b).eval x) = unaryVal (a.eval x) * unaryVal (b.eval x) :=
  unaryMul_eval _ _

@[simp] theorem usub_eval {σ : Ty} (a b : Code σ .unary) (x : σ.denote) :
    unaryVal ((usub a b).eval x) = unaryVal (a.eval x) - unaryVal (b.eval x) :=
  unarySub_eval _ _

/-! ## Exercising the surface -/

example : unaryVal ((unaryConst 3 : Code .nat .unary).eval 17) = 3 := rfl

example :
    unaryVal (unaryMul.eval ([true, false], [true, true, true])) = 6 := rfl

example : -- junk entries are ignored: only the length speaks
    unaryVal (unaryAdd.eval ([false], [false, false])) = 3 := rfl

example : unaryToNat.eval ((unaryOfList (τ := .nat)).eval [5, 8, 13]) = 3 := rfl

end Cert
end Hardness
