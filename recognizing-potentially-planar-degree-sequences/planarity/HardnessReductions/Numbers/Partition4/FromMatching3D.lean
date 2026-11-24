import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import HardnessReductions.Numbers.Partition4
import HardnessReductions.Sets.Matching3D

/-!
# 4-PARTITION is hard: reduction from 3-DIMENSIONAL MATCHING

Garey–Johnson §4.2, Theorem 4.3. Every triple `t` of the 3DM instance
becomes four numbers: a *triple* element `u_t` and one *copy* element per
coordinate — the occurrence of `t`'s member of `W`, `X`, `Y` in `t`. Copies
come in two flavours: for each element `z` one designated occurrence is the
*actual* copy of `z`, all others are *dummies*. The sizes are base-`r`
numerals arranged so that a part sums to the bound `B = 40·r⁴ + 15` exactly
when it consists of a triple element together with copies of that triple's
three members, all actual or all dummy; a partition therefore selects, per
triple, either its actual members (the matching) or dummies (the garbage),
and the all-actual parts are a perfect matching.

Fresh names are tagged tuples: the element type is `↥T × Fin 4` — kind `0`
the triple element, kinds `1`, `2`, `3` the `W`-, `X`-, `Y`-copies — and the
*designation* of actual copies is a parameter (`pW pX pY`: a choice, per
element, of a triple containing it), so that the abstract instance map and
the certified program can each supply their own canonical choice.

Deviations from the book, forced by promise-free totality:

* Garey–Johnson assume `|W| = |X| = |Y| = q` and (implicitly, for the size
  bookkeeping) that every element occurs in some triple. Both are genuine:
  without them the constructed sizes need not total `m·B`, and an instance
  whose element is covered by no triple can be 4-partitionable while the
  matching does not exist. The reduction therefore *branches*: instances
  failing the (polynomial) test map to a fixed no-instance inside the
  window — `⟨[6,6,6,6,6,8,8,8], 27⟩`, a no-instance by parity: all sizes
  even, the bound odd.
* Indices are `0`-based and the radix is `r = 33·(q+1)` rather than the
  book's `32·q`: the classification argument compares residue sums of at
  most `32` against `B`'s residue `15`, and `r ≥ 33` makes every such
  comparison exact with no wrap-around case.

The hardness statement lands inside the restriction `FourPartitionWindow`
(`Reduction.codRestrict`): all constructed sizes lie strictly between `B/5`
and `B/3` and total `m·B`.
-/

namespace Hardness

variable {W X Y : Type} [DecidableEq W] [DecidableEq X] [DecidableEq Y]

section Sizes

variable (r : ℕ) (iW : W → ℕ) (iX : X → ℕ) (iY : Y → ℕ)
variable (pW : W → W × X × Y) (pX : X → W × X × Y) (pY : Y → W × X × Y)

/-- The size of the triple element `u_t`: leading digit `10`, and the three
member indices *subtracted* at their places, so that adding any three
matching copies restores a constant. -/
def mfpUSize (t : W × X × Y) : ℕ :=
  10 * r ^ 4 + 8 - (iY t.2.2 * r ^ 3 + iX t.2.1 * r ^ 2 + iW t.1 * r)

/-- The size of the `W`-copy carried by triple `t`: the copy is *actual* iff
`t` is the designated triple of its element. -/
def mfpWSize (t : W × X × Y) : ℕ :=
  (if pW t.1 = t then 10 else 11) * r ^ 4 + iW t.1 * r + 1

/-- The size of the `X`-copy carried by triple `t`. -/
def mfpXSize (t : W × X × Y) : ℕ :=
  (if pX t.2.1 = t then 10 else 11) * r ^ 4 + iX t.2.1 * r ^ 2 + 2

/-- The size of the `Y`-copy carried by triple `t`. Note the dummy leading
digit is `8`, below the actual's `10` — the counterweight that makes
`10 + 10 + 10 = 11 + 11 + 8` the only two ways to reach `30`. -/
def mfpYSize (t : W × X × Y) : ℕ :=
  (if pY t.2.2 = t then 10 else 8) * r ^ 4 + iY t.2.2 * r ^ 3 + 4

/-- The bound: four leading `10`s and the residue `15 = 8 + 1 + 2 + 4`. -/
def mfpB : ℕ := 40 * r ^ 4 + 15

variable (T : Finset (W × X × Y))

/-- The sizes, as a family over the tagged element type `↥T × Fin 4`:
kind `0` is the triple element, kinds `1`, `2`, `3` its three copies. -/
def mfpSize (p : ↥T × Fin 4) : ℕ :=
  ![mfpUSize r iW iX iY p.1.val, mfpWSize r iW pW p.1.val,
    mfpXSize r iX pX p.1.val, mfpYSize r iY pY p.1.val] p.2

@[simp] theorem mfpSize_zero (t : ↥T) :
    mfpSize r iW iX iY pW pX pY T (t, 0) = mfpUSize r iW iX iY t.val := rfl

@[simp] theorem mfpSize_one (t : ↥T) :
    mfpSize r iW iX iY pW pX pY T (t, 1) = mfpWSize r iW pW t.val := rfl

@[simp] theorem mfpSize_two (t : ↥T) :
    mfpSize r iW iX iY pW pX pY T (t, 2) = mfpXSize r iX pX t.val := rfl

@[simp] theorem mfpSize_three (t : ↥T) :
    mfpSize r iW iX iY pW pX pY T (t, 3) = mfpYSize r iY pY t.val := rfl

end Sizes

section Residues

variable {r : ℕ} {iW : W → ℕ} {iX : X → ℕ} {iY : Y → ℕ}
variable {pW : W → W × X × Y} {pX : X → W × X × Y} {pY : Y → W × X × Y}

omit [DecidableEq W] [DecidableEq X] [DecidableEq Y] in
/-- The subtracted term of a triple element's size stays below three leading
units, provided every index is below the radix. -/
theorem mfp_sub_le (hiW : ∀ w, iW w < r) (hiX : ∀ x, iX x < r)
    (hiY : ∀ y, iY y < r) (t : W × X × Y) :
    iY t.2.2 * r ^ 3 + iX t.2.1 * r ^ 2 + iW t.1 * r ≤ 3 * r ^ 4 := by
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) (hiW t.1)
  have h3 : iY t.2.2 * r ^ 3 ≤ r * r ^ 3 := Nat.mul_le_mul_right _ (hiY t.2.2).le
  have h2 : iX t.2.1 * r ^ 2 ≤ r * r ^ 2 := Nat.mul_le_mul_right _ (hiX t.2.1).le
  have h1 : iW t.1 * r ≤ r * r := Nat.mul_le_mul_right _ (hiW t.1).le
  have e3 : r * r ^ 3 = r ^ 4 := by ring
  have e2 : r * r ^ 2 = r ^ 3 := by ring
  have e1 : r * r = r ^ 2 := by ring
  have p34 : r ^ 3 ≤ r ^ 4 := Nat.pow_le_pow_right hr (by omega)
  have p24 : r ^ 2 ≤ r ^ 4 := Nat.pow_le_pow_right hr (by omega)
  linarith

omit [DecidableEq W] [DecidableEq X] [DecidableEq Y] in
/-- Kind-`0` residue: a triple element's size is `8` modulo `r`. -/
theorem mfpUSize_mod (h8 : 8 < r) (hiW : ∀ w, iW w < r) (hiX : ∀ x, iX x < r)
    (hiY : ∀ y, iY y < r) (t : W × X × Y) :
    mfpUSize r iW iX iY t % r = 8 := by
  have hsub := mfp_sub_le hiW hiX hiY t
  obtain ⟨k, hk⟩ : ∃ k, mfpUSize r iW iX iY t = k * r + 8 := by
    refine ⟨10 * r ^ 3 - (iY t.2.2 * r ^ 2 + iX t.2.1 * r + iW t.1), ?_⟩
    unfold mfpUSize
    rw [Nat.sub_mul]
    have e1 : 10 * r ^ 3 * r = 10 * r ^ 4 := by ring
    have e2 : (iY t.2.2 * r ^ 2 + iX t.2.1 * r + iW t.1) * r
        = iY t.2.2 * r ^ 3 + iX t.2.1 * r ^ 2 + iW t.1 * r := by ring
    rw [e1, e2]
    omega
  rw [hk, Nat.mul_add_mod', Nat.mod_eq_of_lt h8]

/-- Kind-`1` residue: a `W`-copy's size is `1` modulo `r`. -/
theorem mfpWSize_mod (h1 : 1 < r) (t : W × X × Y) :
    mfpWSize r iW pW t % r = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, mfpWSize r iW pW t = k * r + 1 :=
    ⟨(if pW t.1 = t then 10 else 11) * r ^ 3 + iW t.1, by unfold mfpWSize; ring⟩
  rw [hk, Nat.mul_add_mod', Nat.mod_eq_of_lt h1]

/-- Kind-`2` residue: an `X`-copy's size is `2` modulo `r`. -/
theorem mfpXSize_mod (h2 : 2 < r) (t : W × X × Y) :
    mfpXSize r iX pX t % r = 2 := by
  obtain ⟨k, hk⟩ : ∃ k, mfpXSize r iX pX t = k * r + 2 :=
    ⟨(if pX t.2.1 = t then 10 else 11) * r ^ 3 + iX t.2.1 * r,
      by unfold mfpXSize; ring⟩
  rw [hk, Nat.mul_add_mod', Nat.mod_eq_of_lt h2]

/-- Kind-`3` residue: a `Y`-copy's size is `4` modulo `r`. -/
theorem mfpYSize_mod (h4 : 4 < r) (t : W × X × Y) :
    mfpYSize r iY pY t % r = 4 := by
  obtain ⟨k, hk⟩ : ∃ k, mfpYSize r iY pY t = k * r + 4 :=
    ⟨(if pY t.2.2 = t then 10 else 8) * r ^ 3 + iY t.2.2 * r ^ 2,
      by unfold mfpYSize; ring⟩
  rw [hk, Nat.mul_add_mod', Nat.mod_eq_of_lt h4]

/-- The bound's residue is `15` modulo `r`. -/
theorem mfpB_mod (h15 : 15 < r) : mfpB r % r = 15 := by
  obtain ⟨k, hk⟩ : ∃ k, mfpB r = k * r + 15 := ⟨40 * r ^ 3, by unfold mfpB; ring⟩
  rw [hk, Nat.mul_add_mod', Nat.mod_eq_of_lt h15]

/-- The size of any element, modulo `r`, is its kind's tag: `8`, `1`, `2`,
`4` for kinds `0`, `1`, `2`, `3`. -/
theorem mfpSize_mod {T : Finset (W × X × Y)} (h33 : 33 ≤ r)
    (hiW : ∀ w, iW w < r) (hiX : ∀ x, iX x < r) (hiY : ∀ y, iY y < r)
    (p : ↥T × Fin 4) :
    mfpSize r iW iX iY pW pX pY T p % r = ![8, 1, 2, 4] p.2 := by
  obtain ⟨t, c⟩ := p
  have hc : ∀ c : Fin 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by decide
  rcases hc c with rfl | rfl | rfl | rfl
  · exact mfpUSize_mod (by omega) hiW hiX hiY t.val
  · exact mfpWSize_mod (by omega) t.val
  · exact mfpXSize_mod (by omega) t.val
  · exact mfpYSize_mod (by omega) t.val

end Residues

section Shape

variable {r : ℕ} {iW : W → ℕ} {iX : X → ℕ} {iY : Y → ℕ}
variable {pW : W → W × X × Y} {pX : X → W × X × Y} {pY : Y → W × X × Y}
variable {T : Finset (W × X × Y)}

/-- Any four elements summing to the bound consist of exactly one element of
each kind: the residues `8, 1, 2, 4` must sum to `B`'s residue `15` modulo
`r`, and with residue sums capped at `32 < r` the only multiset that works
is one of each. -/
theorem mfp_shape (h33 : 33 ≤ r) (hiW : ∀ w, iW w < r) (hiX : ∀ x, iX x < r)
    (hiY : ∀ y, iY y < r) {P : Finset (↥T × Fin 4)} (hcard : P.card = 4)
    (hsum : ∑ p ∈ P, mfpSize r iW iX iY pW pX pY T p = mfpB r) :
    ∃ t₀ t₁ t₂ t₃ : ↥T, P = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} := by
  classical
  -- the residue sum is exactly 15
  have hmod : (∑ p ∈ P, ![8, 1, 2, 4] p.2) % r = 15 := by
    have h1 : (∑ p ∈ P, mfpSize r iW iX iY pW pX pY T p) % r
        = (∑ p ∈ P, ![(8 : ℕ), 1, 2, 4] p.2) % r := by
      rw [Finset.sum_nat_mod]
      congr 1
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      exact mfpSize_mod h33 hiW hiX hiY p
    rw [← h1, hsum, mfpB_mod (by omega)]
  have hle : ∑ p ∈ P, ![(8 : ℕ), 1, 2, 4] p.2 ≤ 32 := by
    have := Finset.sum_le_card_nsmul P (fun p ↦ ![(8 : ℕ), 1, 2, 4] p.2) 8
      (fun p _ ↦ by
        have hc : ∀ c : Fin 4, ![(8 : ℕ), 1, 2, 4] c ≤ 8 := by decide
        exact hc p.2)
    rw [hcard] at this
    simpa using this
  have hressum : ∑ p ∈ P, ![(8 : ℕ), 1, 2, 4] p.2 = 15 := by
    have hlt : ∑ p ∈ P, ![(8 : ℕ), 1, 2, 4] p.2 < r :=
      Nat.lt_of_le_of_lt hle (by omega)
    rw [← Nat.mod_eq_of_lt hlt]
    exact hmod
  -- fiber counts: one element of each kind
  have hfibconst : ∀ c : Fin 4,
      ∑ p ∈ P.filter (fun p ↦ p.2 = c), ![(8 : ℕ), 1, 2, 4] p.2
        = (P.filter (fun p ↦ p.2 = c)).card * ![(8 : ℕ), 1, 2, 4] c := by
    intro c
    have hconst : ∀ p ∈ P.filter (fun p ↦ p.2 = c),
        ![(8 : ℕ), 1, 2, 4] p.2 = ![(8 : ℕ), 1, 2, 4] c := fun p hp ↦ by
      rw [(Finset.mem_filter.mp hp).2]
    calc ∑ p ∈ P.filter (fun p ↦ p.2 = c), ![(8 : ℕ), 1, 2, 4] p.2
        = ∑ _p ∈ P.filter (fun p ↦ p.2 = c), ![(8 : ℕ), 1, 2, 4] c :=
          Finset.sum_congr rfl hconst
      _ = (P.filter (fun p ↦ p.2 = c)).card * ![(8 : ℕ), 1, 2, 4] c := by
          rw [Finset.sum_const, smul_eq_mul]
  have hcards : ∑ c : Fin 4, (P.filter fun p ↦ p.2 = c).card = 4 :=
    (Finset.card_eq_sum_card_fiberwise fun p _ ↦ Finset.mem_univ p.2).symm.trans
      hcard
  have hval : ∑ c : Fin 4, (P.filter fun p ↦ p.2 = c).card * ![(8 : ℕ), 1, 2, 4] c
      = 15 := by
    have h1 : ∑ c : Fin 4, (P.filter fun p ↦ p.2 = c).card * ![(8 : ℕ), 1, 2, 4] c
        = ∑ c : Fin 4, ∑ p ∈ P.filter (fun p ↦ p.2 = c), ![(8 : ℕ), 1, 2, 4] p.2 :=
      Finset.sum_congr rfl fun c _ ↦ (hfibconst c).symm
    rw [h1, Finset.sum_fiberwise, hressum]
  -- solve the counts
  have v0 : ![(8 : ℕ), 1, 2, 4] 0 = 8 := rfl
  have v1 : ![(8 : ℕ), 1, 2, 4] 1 = 1 := rfl
  have v2 : ![(8 : ℕ), 1, 2, 4] 2 = 2 := rfl
  have v3 : ![(8 : ℕ), 1, 2, 4] 3 = 4 := rfl
  rw [Fin.sum_univ_four] at hcards hval
  rw [v0, v1, v2, v3] at hval
  have h0 : (P.filter fun p ↦ p.2 = (0 : Fin 4)).card = 1 := by omega
  have h1 : (P.filter fun p ↦ p.2 = (1 : Fin 4)).card = 1 := by omega
  have h2 : (P.filter fun p ↦ p.2 = (2 : Fin 4)).card = 1 := by omega
  have h3 : (P.filter fun p ↦ p.2 = (3 : Fin 4)).card = 1 := by omega
  -- name the four elements
  obtain ⟨p0, hp0⟩ := Finset.card_eq_one.mp h0
  obtain ⟨p1, hp1⟩ := Finset.card_eq_one.mp h1
  obtain ⟨p2, hp2⟩ := Finset.card_eq_one.mp h2
  obtain ⟨p3, hp3⟩ := Finset.card_eq_one.mp h3
  have hm0 : p0 ∈ P ∧ p0.2 = 0 := Finset.mem_filter.mp (hp0 ▸ Finset.mem_singleton_self p0)
  have hm1 : p1 ∈ P ∧ p1.2 = 1 := Finset.mem_filter.mp (hp1 ▸ Finset.mem_singleton_self p1)
  have hm2 : p2 ∈ P ∧ p2.2 = 2 := Finset.mem_filter.mp (hp2 ▸ Finset.mem_singleton_self p2)
  have hm3 : p3 ∈ P ∧ p3.2 = 3 := Finset.mem_filter.mp (hp3 ▸ Finset.mem_singleton_self p3)
  refine ⟨p0.1, p1.1, p2.1, p3.1, ?_⟩
  have e0 : (p0.1, (0 : Fin 4)) = p0 := by rw [← hm0.2]
  have e1 : (p1.1, (1 : Fin 4)) = p1 := by rw [← hm1.2]
  have e2 : (p2.1, (2 : Fin 4)) = p2 := by rw [← hm2.2]
  have e3 : (p3.1, (3 : Fin 4)) = p3 := by rw [← hm3.2]
  rw [e0, e1, e2, e3]
  apply Finset.Subset.antisymm
  · intro p hp
    have hfin : ∀ c : Fin 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by decide
    rcases hfin p.2 with h | h | h | h
    · have hm : p ∈ P.filter (fun q ↦ q.2 = 0) := Finset.mem_filter.mpr ⟨hp, h⟩
      rw [hp0, Finset.mem_singleton] at hm
      rw [hm]; simp
    · have hm : p ∈ P.filter (fun q ↦ q.2 = 1) := Finset.mem_filter.mpr ⟨hp, h⟩
      rw [hp1, Finset.mem_singleton] at hm
      rw [hm]; simp
    · have hm : p ∈ P.filter (fun q ↦ q.2 = 2) := Finset.mem_filter.mpr ⟨hp, h⟩
      rw [hp2, Finset.mem_singleton] at hm
      rw [hm]; simp
    · have hm : p ∈ P.filter (fun q ↦ q.2 = 3) := Finset.mem_filter.mpr ⟨hp, h⟩
      rw [hp3, Finset.mem_singleton] at hm
      rw [hm]; simp
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    exacts [hm0.1, hm1.1, hm2.1, hm3.1]

/-- Summing a size family over an explicit one-of-each-kind part. -/
theorem sum_four_pairs {T : Finset (W × X × Y)} (f : ↥T × Fin 4 → ℕ)
    (t₀ t₁ t₂ t₃ : ↥T) :
    ∑ p ∈ ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)), f p
      = f (t₀, 0) + f (t₁, 1) + f (t₂, 2) + f (t₃, 3) := by
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_singleton]
  ring

/-- An explicit one-of-each-kind part has four elements. -/
theorem card_four_pairs {T : Finset (W × X × Y)} (t₀ t₁ t₂ t₃ : ↥T) :
    ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

/-- The full structure of a part summing to the bound: one element of each
kind, the three copies matching the triple element's coordinates, and the
three copies all actual or all dummy. Garey–Johnson's mod-`r⁴`-and-below
argument, run through `digits_base_eq_of_eq`. -/
theorem mfp_part_structure (h33 : 33 ≤ r) (hiW : ∀ w, iW w < r)
    (hiX : ∀ x, iX x < r) (hiY : ∀ y, iY y < r)
    (hiWinj : Function.Injective iW) (hiXinj : Function.Injective iX)
    (hiYinj : Function.Injective iY) {P : Finset (↥T × Fin 4)}
    (hcard : P.card = 4)
    (hsum : ∑ p ∈ P, mfpSize r iW iX iY pW pX pY T p = mfpB r) :
    ∃ t₀ t₁ t₂ t₃ : ↥T, P = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} ∧
      t₁.val.1 = t₀.val.1 ∧ t₂.val.2.1 = t₀.val.2.1 ∧ t₃.val.2.2 = t₀.val.2.2 ∧
      ((pW t₁.val.1 = t₁.val ∧ pX t₂.val.2.1 = t₂.val ∧ pY t₃.val.2.2 = t₃.val) ∨
        (pW t₁.val.1 ≠ t₁.val ∧ pX t₂.val.2.1 ≠ t₂.val ∧
          pY t₃.val.2.2 ≠ t₃.val)) := by
  obtain ⟨t₀, t₁, t₂, t₃, rfl⟩ := mfp_shape h33 hiW hiX hiY hcard hsum
  rw [sum_four_pairs] at hsum
  simp only [mfpSize_zero, mfpSize_one, mfpSize_two, mfpSize_three] at hsum
  unfold mfpUSize mfpWSize mfpXSize mfpYSize mfpB at hsum
  set cw := if pW t₁.val.1 = t₁.val then (10 : ℕ) else 11 with hcw
  set cx := if pX t₂.val.2.1 = t₂.val then (10 : ℕ) else 11 with hcx
  set cy := if pY t₃.val.2.2 = t₃.val then (10 : ℕ) else 8 with hcy
  have hsub := mfp_sub_le hiW hiX hiY t₀.val
  have hexp : (cw + cx + cy + 10) * r ^ 4
      = cw * r ^ 4 + cx * r ^ 4 + cy * r ^ 4 + 10 * r ^ 4 := by ring
  have hcomb : (cw + cx + cy + 10) * r ^ 4 + iY t₃.val.2.2 * r ^ 3
      + iX t₂.val.2.1 * r ^ 2 + iW t₁.val.1 * r + 15
      = 40 * r ^ 4 + iY t₀.val.2.2 * r ^ 3 + iX t₀.val.2.1 * r ^ 2
        + iW t₀.val.1 * r + 15 := by
    omega
  obtain ⟨hA, hY, hX, hW⟩ := digits_base_eq_of_eq (hiY _) (hiX _) (hiW _)
    (hiY _) (hiX _) (hiW _) (by omega) hcomb
  refine ⟨t₀, t₁, t₂, t₃, rfl, hiWinj hW, hiXinj hX, hiYinj hY, ?_⟩
  by_cases hw : pW t₁.val.1 = t₁.val <;> by_cases hx : pX t₂.val.2.1 = t₂.val <;>
    by_cases hy : pY t₃.val.2.2 = t₃.val
  · exact Or.inl ⟨hw, hx, hy⟩
  · exfalso; rw [if_pos hw] at hcw; rw [if_pos hx] at hcx; rw [if_neg hy] at hcy
    omega
  · exfalso; rw [if_pos hw] at hcw; rw [if_neg hx] at hcx; rw [if_pos hy] at hcy
    omega
  · exfalso; rw [if_pos hw] at hcw; rw [if_neg hx] at hcx; rw [if_neg hy] at hcy
    omega
  · exfalso; rw [if_neg hw] at hcw; rw [if_pos hx] at hcx; rw [if_pos hy] at hcy
    omega
  · exfalso; rw [if_neg hw] at hcw; rw [if_pos hx] at hcx; rw [if_neg hy] at hcy
    omega
  · exfalso; rw [if_neg hw] at hcw; rw [if_neg hx] at hcx; rw [if_pos hy] at hcy
    omega
  · exact Or.inr ⟨hw, hx, hy⟩

end Shape

section Assign

/-! ## The copy assignment

The forward direction must hand each triple a copy of each of its three
members, bijectively, with the matching's triples receiving the actual
copies. Within the triples through a fixed element this is a *swap*: exchange
the matching's triple with the designated one, fix everything else. -/

variable {Z : Type} {T : Finset (W × X × Y)}

/-- Swap-based copy assignment along a coordinate projection `π`: the triple
`t` receives the copy carried by `swap (m (π t)) (a (π t)) t`, where `m`
names the matching's triple through an element and `a` the designated one. -/
def mfpAssign [DecidableEq Z] (π : W × X × Y → Z) (m a : Z → ↥T) (tu : ↥T) :
    ↥T :=
  Equiv.swap (m (π tu.val)) (a (π tu.val)) tu

variable [DecidableEq Z] {π : W × X × Y → Z} {m a : Z → ↥T}

/-- The assignment stays within the triples through the same element. -/
theorem mfpAssign_proj (hm : ∀ z, π (m z).val = z) (ha : ∀ z, π (a z).val = z)
    (tu : ↥T) : π (mfpAssign π m a tu).val = π tu.val := by
  unfold mfpAssign
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [ha, h1, hm]
  · rw [hm, h2, ha]
  · rfl

/-- The assignment is an involution — which is what makes it a bijection
between triples and copies. -/
theorem mfpAssign_invol (hm : ∀ z, π (m z).val = z) (ha : ∀ z, π (a z).val = z)
    (tu : ↥T) : mfpAssign π m a (mfpAssign π m a tu) = tu := by
  have h := mfpAssign_proj hm ha tu
  change Equiv.swap (m (π (mfpAssign π m a tu).val)) (a (π (mfpAssign π m a tu).val))
      (mfpAssign π m a tu) = tu
  rw [h]
  exact Equiv.swap_apply_self _ _ tu

/-- The assignment hands a triple the *designated* (actual) copy exactly when
the triple is the matching's. -/
theorem mfpAssign_eq_designated_iff (tu : ↥T) :
    mfpAssign π m a tu = a (π tu.val) ↔ tu = m (π tu.val) := by
  unfold mfpAssign
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

end Assign

section Forward

variable {r : ℕ} {iW : W → ℕ} {iX : X → ℕ} {iY : Y → ℕ}
variable {pW : W → W × X × Y} {pX : X → W × X × Y} {pY : Y → W × X × Y}
variable {T : Finset (W × X × Y)}

/-- Forward direction of Garey–Johnson Theorem 4.3: a matching yields a
sized partition — one part per triple, the matching's triples grouped with
their actual copies, the rest with dummies. -/
theorem exists_isSizedPartition_of_matching
    (hiW : ∀ w, iW w < r) (hiX : ∀ x, iX x < r) (hiY : ∀ y, iY y < r)
    (hpW : ∀ w, pW w ∈ T ∧ (pW w).1 = w)
    (hpX : ∀ x, pX x ∈ T ∧ (pX x).2.1 = x)
    (hpY : ∀ y, pY y ∈ T ∧ (pY y).2.2 = y)
    {M : Finset (W × X × Y)} (hMT : M ⊆ T)
    (hcW : IsExactCover M (fun t ↦ t.1))
    (hcX : IsExactCover M (fun t ↦ t.2.1))
    (hcY : IsExactCover M (fun t ↦ t.2.2)) :
    ∃ parts, IsSizedPartition (mfpSize r iW iX iY pW pX pY T) 4 (mfpB r)
      parts := by
  classical
  -- the matching's triple through each element, as a subtype point
  have hmW : ∀ w : W, ∃ mw : ↥T, mw.val ∈ M ∧ mw.val.1 = w ∧
      ∀ t' ∈ M, t'.1 = w → t' = mw.val := by
    intro w
    obtain ⟨t, ⟨htM, htw⟩, huniq⟩ := hcW w
    exact ⟨⟨t, hMT htM⟩, htM, htw, fun t' ht' hw' ↦ huniq t' ⟨ht', hw'⟩⟩
  have hmX : ∀ x : X, ∃ mx : ↥T, mx.val ∈ M ∧ mx.val.2.1 = x ∧
      ∀ t' ∈ M, t'.2.1 = x → t' = mx.val := by
    intro x
    obtain ⟨t, ⟨htM, htx⟩, huniq⟩ := hcX x
    exact ⟨⟨t, hMT htM⟩, htM, htx, fun t' ht' hx' ↦ huniq t' ⟨ht', hx'⟩⟩
  have hmY : ∀ y : Y, ∃ my : ↥T, my.val ∈ M ∧ my.val.2.2 = y ∧
      ∀ t' ∈ M, t'.2.2 = y → t' = my.val := by
    intro y
    obtain ⟨t, ⟨htM, hty⟩, huniq⟩ := hcY y
    exact ⟨⟨t, hMT htM⟩, htM, hty, fun t' ht' hy' ↦ huniq t' ⟨ht', hy'⟩⟩
  choose mW hmW1 hmW2 hmW3 using hmW
  choose mX hmX1 hmX2 hmX3 using hmX
  choose mY hmY1 hmY2 hmY3 using hmY
  -- a triple is in the matching iff it is the matching's triple through
  -- its own element
  have hMiffW : ∀ tu : ↥T, tu.val ∈ M ↔ tu = mW tu.val.1 := by
    intro tu
    constructor
    · intro h
      exact Subtype.ext (hmW3 tu.val.1 tu.val h rfl)
    · intro h
      rw [h]
      exact hmW1 tu.val.1
  have hMiffX : ∀ tu : ↥T, tu.val ∈ M ↔ tu = mX tu.val.2.1 := by
    intro tu
    constructor
    · intro h
      exact Subtype.ext (hmX3 tu.val.2.1 tu.val h rfl)
    · intro h
      rw [h]
      exact hmX1 tu.val.2.1
  have hMiffY : ∀ tu : ↥T, tu.val ∈ M ↔ tu = mY tu.val.2.2 := by
    intro tu
    constructor
    · intro h
      exact Subtype.ext (hmY3 tu.val.2.2 tu.val h rfl)
    · intro h
      rw [h]
      exact hmY1 tu.val.2.2
  -- the copy assignments, with their three defining properties
  obtain ⟨σW, hW1, hWinv, hactW⟩ : ∃ σ : ↥T → ↥T,
      (∀ tu, (σ tu).val.1 = tu.val.1) ∧ (∀ tu, σ (σ tu) = tu) ∧
        ∀ tu, pW ((σ tu).val.1) = (σ tu).val ↔ tu.val ∈ M := by
    have haproj : ∀ w, ((⟨pW w, (hpW w).1⟩ : ↥T)).val.1 = w := fun w ↦ (hpW w).2
    have h1 : ∀ tu, ((mfpAssign (fun t ↦ t.1) mW
        (fun w ↦ ⟨pW w, (hpW w).1⟩) tu).val.1) = tu.val.1 :=
      fun tu ↦ mfpAssign_proj (π := fun t ↦ t.1) hmW2 haproj tu
    refine ⟨_, h1, fun tu ↦ mfpAssign_invol hmW2 haproj tu, ?_⟩
    intro tu
    rw [h1 tu, hMiffW tu]
    constructor
    · intro h
      exact (mfpAssign_eq_designated_iff tu).mp (Subtype.ext h.symm)
    · intro h
      rw [(mfpAssign_eq_designated_iff tu).mpr h]
  obtain ⟨σX, hX1, hXinv, hactX⟩ : ∃ σ : ↥T → ↥T,
      (∀ tu, (σ tu).val.2.1 = tu.val.2.1) ∧ (∀ tu, σ (σ tu) = tu) ∧
        ∀ tu, pX ((σ tu).val.2.1) = (σ tu).val ↔ tu.val ∈ M := by
    have haproj : ∀ x, ((⟨pX x, (hpX x).1⟩ : ↥T)).val.2.1 = x := fun x ↦ (hpX x).2
    have h1 : ∀ tu, ((mfpAssign (fun t ↦ t.2.1) mX
        (fun x ↦ ⟨pX x, (hpX x).1⟩) tu).val.2.1) = tu.val.2.1 :=
      fun tu ↦ mfpAssign_proj (π := fun t ↦ t.2.1) hmX2 haproj tu
    refine ⟨_, h1, fun tu ↦ mfpAssign_invol hmX2 haproj tu, ?_⟩
    intro tu
    rw [h1 tu, hMiffX tu]
    constructor
    · intro h
      exact (mfpAssign_eq_designated_iff tu).mp (Subtype.ext h.symm)
    · intro h
      rw [(mfpAssign_eq_designated_iff tu).mpr h]
  obtain ⟨σY, hY1, hYinv, hactY⟩ : ∃ σ : ↥T → ↥T,
      (∀ tu, (σ tu).val.2.2 = tu.val.2.2) ∧ (∀ tu, σ (σ tu) = tu) ∧
        ∀ tu, pY ((σ tu).val.2.2) = (σ tu).val ↔ tu.val ∈ M := by
    have haproj : ∀ y, ((⟨pY y, (hpY y).1⟩ : ↥T)).val.2.2 = y := fun y ↦ (hpY y).2
    have h1 : ∀ tu, ((mfpAssign (fun t ↦ t.2.2) mY
        (fun y ↦ ⟨pY y, (hpY y).1⟩) tu).val.2.2) = tu.val.2.2 :=
      fun tu ↦ mfpAssign_proj (π := fun t ↦ t.2.2) hmY2 haproj tu
    refine ⟨_, h1, fun tu ↦ mfpAssign_invol hmY2 haproj tu, ?_⟩
    intro tu
    rw [h1 tu, hMiffY tu]
    constructor
    · intro h
      exact (mfpAssign_eq_designated_iff tu).mp (Subtype.ext h.symm)
    · intro h
      rw [(mfpAssign_eq_designated_iff tu).mpr h]
  -- the parts: one per triple
  set block : ↥T → Finset (↥T × Fin 4) :=
    fun tu ↦ {(tu, 0), (σW tu, 1), (σX tu, 2), (σY tu, 3)} with hblock
  refine ⟨T.attach.image block, ?_, ?_⟩
  · -- every element lies in exactly one part
    rintro ⟨tu, c⟩
    have hfin : ∀ c : Fin 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by decide
    have hkind : ∀ su u : ↥T, ∀ c : Fin 4, (u, c) ∈ block su ↔
        (u = su ∧ c = 0) ∨ (u = σW su ∧ c = 1) ∨ (u = σX su ∧ c = 2) ∨
          (u = σY su ∧ c = 3) := by
      intro su u c
      simp [hblock, Prod.ext_iff]
    rcases hfin c with rfl | rfl | rfl | rfl
    · refine ⟨block tu, ⟨Finset.mem_image_of_mem block (Finset.mem_attach T tu),
        ?_⟩, ?_⟩
      · rw [hkind]
        exact Or.inl ⟨rfl, rfl⟩
      · rintro q ⟨hq, hmem⟩
        obtain ⟨su, -, rfl⟩ := Finset.mem_image.mp hq
        rw [hkind] at hmem
        rcases hmem with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · rw [h]
        all_goals exact absurd h (by decide)
    · refine ⟨block (σW tu), ⟨Finset.mem_image_of_mem block
        (Finset.mem_attach T (σW tu)), ?_⟩, ?_⟩
      · rw [hkind]
        exact Or.inr (Or.inl ⟨(hWinv tu).symm, rfl⟩)
      · rintro q ⟨hq, hmem⟩
        obtain ⟨su, -, rfl⟩ := Finset.mem_image.mp hq
        rw [hkind] at hmem
        rcases hmem with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact absurd h (by decide)
        · rw [show su = σW tu from by rw [h, hWinv]]
        all_goals exact absurd h (by decide)
    · refine ⟨block (σX tu), ⟨Finset.mem_image_of_mem block
        (Finset.mem_attach T (σX tu)), ?_⟩, ?_⟩
      · rw [hkind]
        exact Or.inr (Or.inr (Or.inl ⟨(hXinv tu).symm, rfl⟩))
      · rintro q ⟨hq, hmem⟩
        obtain ⟨su, -, rfl⟩ := Finset.mem_image.mp hq
        rw [hkind] at hmem
        rcases hmem with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · rw [show su = σX tu from by rw [h, hXinv]]
        · exact absurd h (by decide)
    · refine ⟨block (σY tu), ⟨Finset.mem_image_of_mem block
        (Finset.mem_attach T (σY tu)), ?_⟩, ?_⟩
      · rw [hkind]
        exact Or.inr (Or.inr (Or.inr ⟨(hYinv tu).symm, rfl⟩))
      · rintro q ⟨hq, hmem⟩
        obtain ⟨su, -, rfl⟩ := Finset.mem_image.mp hq
        rw [hkind] at hmem
        rcases hmem with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · rw [show su = σY tu from by rw [h, hYinv]]
  · -- every part has four elements summing to the bound
    intro p hp
    obtain ⟨su, -, rfl⟩ := Finset.mem_image.mp hp
    simp only [hblock]
    refine ⟨card_four_pairs su (σW su) (σX su) (σY su), ?_⟩
    rw [sum_four_pairs]
    simp only [mfpSize_zero, mfpSize_one, mfpSize_two, mfpSize_three]
    have hsub := mfp_sub_le hiW hiX hiY su.val
    by_cases hM : su.val ∈ M
    · unfold mfpWSize mfpXSize mfpYSize
      rw [if_pos ((hactW su).mpr hM), if_pos ((hactX su).mpr hM),
        if_pos ((hactY su).mpr hM), hW1 su, hX1 su, hY1 su]
      unfold mfpUSize mfpB
      omega
    · unfold mfpWSize mfpXSize mfpYSize
      rw [if_neg (fun h ↦ hM ((hactW su).mp h)),
        if_neg (fun h ↦ hM ((hactX su).mp h)),
        if_neg (fun h ↦ hM ((hactY su).mp h)), hW1 su, hX1 su, hY1 su]
      unfold mfpUSize mfpB
      omega

end Forward

section Backward

variable {r : ℕ} {iW : W → ℕ} {iX : X → ℕ} {iY : Y → ℕ}
variable {pW : W → W × X × Y} {pX : X → W × X × Y} {pY : Y → W × X × Y}
variable {T : Finset (W × X × Y)}

/-- Backward direction of Garey–Johnson Theorem 4.3: a sized partition
yields a matching — the triples whose parts are all-actual. Each part is
structured by `mfp_part_structure`; the all-actual parts consume each
element's unique actual copy, so they cover every element exactly once. -/
theorem exists_matching_of_isSizedPartition (h33 : 33 ≤ r)
    (hiW : ∀ w, iW w < r) (hiX : ∀ x, iX x < r) (hiY : ∀ y, iY y < r)
    (hiWinj : Function.Injective iW) (hiXinj : Function.Injective iX)
    (hiYinj : Function.Injective iY)
    (hpW : ∀ w, pW w ∈ T ∧ (pW w).1 = w)
    (hpX : ∀ x, pX x ∈ T ∧ (pX x).2.1 = x)
    (hpY : ∀ y, pY y ∈ T ∧ (pY y).2.2 = y)
    {parts : Finset (Finset (↥T × Fin 4))}
    (hpart : IsSizedPartition (mfpSize r iW iX iY pW pX pY T) 4 (mfpB r)
      parts) :
    ∃ M ⊆ T, IsExactCover M (fun t ↦ t.1) ∧ IsExactCover M (fun t ↦ t.2.1) ∧
      IsExactCover M (fun t ↦ t.2.2) := by
  classical
  have hstruct : ∀ p ∈ parts, ∃ t₀ t₁ t₂ t₃ : ↥T,
      p = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} ∧
      t₁.val.1 = t₀.val.1 ∧ t₂.val.2.1 = t₀.val.2.1 ∧
      t₃.val.2.2 = t₀.val.2.2 ∧
      ((pW t₁.val.1 = t₁.val ∧ pX t₂.val.2.1 = t₂.val ∧
          pY t₃.val.2.2 = t₃.val) ∨
        (pW t₁.val.1 ≠ t₁.val ∧ pX t₂.val.2.1 ≠ t₂.val ∧
          pY t₃.val.2.2 ≠ t₃.val)) :=
    fun p hp ↦ mfp_part_structure h33 hiW hiX hiY hiWinj hiXinj hiYinj
      (hpart.2 p hp).1 (hpart.2 p hp).2
  -- membership in an explicit part pins the element of each kind
  have hk0 : ∀ t₀ t₁ t₂ t₃ u : ↥T, (u, (0 : Fin 4)) ∈
      ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)) →
        u = t₀ := by
    intro t₀ t₁ t₂ t₃ u h
    simpa [Prod.ext_iff] using h
  have hk1 : ∀ t₀ t₁ t₂ t₃ u : ↥T, (u, (1 : Fin 4)) ∈
      ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)) →
        u = t₁ := by
    intro t₀ t₁ t₂ t₃ u h
    simpa [Prod.ext_iff] using h
  have hk2 : ∀ t₀ t₁ t₂ t₃ u : ↥T, (u, (2 : Fin 4)) ∈
      ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)) →
        u = t₂ := by
    intro t₀ t₁ t₂ t₃ u h
    simpa [Prod.ext_iff] using h
  have hk3 : ∀ t₀ t₁ t₂ t₃ u : ↥T, (u, (3 : Fin 4)) ∈
      ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)) →
        u = t₃ := by
    intro t₀ t₁ t₂ t₃ u h
    simpa [Prod.ext_iff] using h
  -- the matching: triples whose part carries an actual `W`-copy
  refine ⟨(T.attach.filter fun tu ↦ ∀ p ∈ parts, (tu, (0 : Fin 4)) ∈ p →
      ∃ t₁ : ↥T, (t₁, (1 : Fin 4)) ∈ p ∧ pW t₁.val.1 = t₁.val).image
        Subtype.val, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨tu, -, rfl⟩ := Finset.mem_image.mp ht
    exact tu.2
  · -- W-cover
    intro w
    obtain ⟨pstar, ⟨hpstar, hmem⟩, -⟩ :=
      hpart.1 ((⟨pW w, (hpW w).1⟩ : ↥T), (1 : Fin 4))
    obtain ⟨t₀, t₁, t₂, t₃, hpeq, hc1, hc2, hc3, halign⟩ := hstruct pstar hpstar
    subst hpeq
    have ht₁ : t₁ = ⟨pW w, (hpW w).1⟩ := (hk1 _ _ _ _ _ hmem).symm
    have hact1 : pW t₁.val.1 = t₁.val := by
      rw [ht₁]
      change pW ((pW w).1) = pW w
      rw [(hpW w).2]
    have hall : pW t₁.val.1 = t₁.val ∧ pX t₂.val.2.1 = t₂.val ∧
        pY t₃.val.2.2 = t₃.val := by
      rcases halign with h | h
      · exact h
      · exact absurd hact1 h.1
    have ht₀w : t₀.val.1 = w := by
      rw [← hc1, ht₁]
      exact (hpW w).2
    refine ⟨t₀.val, ⟨?_, ht₀w⟩, ?_⟩
    · refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _, ?_⟩)
      intro q hq hq0
      have hqp : q = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} :=
        hpart.eq_of_mem hq hpstar hq0 (by simp)
      subst hqp
      exact ⟨t₁, by simp, hall.1⟩
    · rintro t' ⟨ht'M, ht'w⟩
      obtain ⟨tu, htu, rfl⟩ := Finset.mem_image.mp ht'M
      have hAct := (Finset.mem_filter.mp htu).2
      obtain ⟨q, ⟨hq, hq0⟩, -⟩ := hpart.1 (tu, (0 : Fin 4))
      obtain ⟨s₀, s₁, s₂, s₃, hqeq, hd1, hd2, hd3, halign'⟩ := hstruct q hq
      subst hqeq
      have hts₀ : tu = s₀ := hk0 _ _ _ _ _ hq0
      obtain ⟨u₁, hu₁mem, hu₁act⟩ := hAct _ hq hq0
      have hu₁ : u₁ = s₁ := hk1 _ _ _ _ _ hu₁mem
      subst hu₁
      have hs₁w : u₁.val.1 = w := by
        rw [hd1, ← hts₀]
        exact ht'w
      have hs₁val : u₁.val = pW w := by
        rw [← hs₁w]
        exact hu₁act.symm
      have hin : ((⟨pW w, (hpW w).1⟩ : ↥T), (1 : Fin 4)) ∈
          ({(s₀, 0), (u₁, 1), (s₂, 2), (s₃, 3)} : Finset (↥T × Fin 4)) := by
        have he : (⟨pW w, (hpW w).1⟩ : ↥T) = u₁ := Subtype.ext hs₁val.symm
        rw [he]
        simp
      have hqp : ({(s₀, 0), (u₁, 1), (s₂, 2), (s₃, 3)} :
          Finset (↥T × Fin 4)) = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} :=
        hpart.eq_of_mem hq hpstar hin hmem
      have hs₀mem : (s₀, (0 : Fin 4)) ∈
          ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)) := by
        rw [← hqp]
        simp
      have hs₀t₀ : s₀ = t₀ := hk0 _ _ _ _ _ hs₀mem
      rw [hts₀, hs₀t₀]
  · -- X-cover
    intro x
    obtain ⟨pstar, ⟨hpstar, hmem⟩, -⟩ :=
      hpart.1 ((⟨pX x, (hpX x).1⟩ : ↥T), (2 : Fin 4))
    obtain ⟨t₀, t₁, t₂, t₃, hpeq, hc1, hc2, hc3, halign⟩ := hstruct pstar hpstar
    subst hpeq
    have ht₂ : t₂ = ⟨pX x, (hpX x).1⟩ := (hk2 _ _ _ _ _ hmem).symm
    have hact2 : pX t₂.val.2.1 = t₂.val := by
      rw [ht₂]
      change pX ((pX x).2.1) = pX x
      rw [(hpX x).2]
    have hall : pW t₁.val.1 = t₁.val ∧ pX t₂.val.2.1 = t₂.val ∧
        pY t₃.val.2.2 = t₃.val := by
      rcases halign with h | h
      · exact h
      · exact absurd hact2 h.2.1
    have ht₀x : t₀.val.2.1 = x := by
      rw [← hc2, ht₂]
      exact (hpX x).2
    refine ⟨t₀.val, ⟨?_, ht₀x⟩, ?_⟩
    · refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _, ?_⟩)
      intro q hq hq0
      have hqp : q = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} :=
        hpart.eq_of_mem hq hpstar hq0 (by simp)
      subst hqp
      exact ⟨t₁, by simp, hall.1⟩
    · rintro t' ⟨ht'M, ht'x⟩
      obtain ⟨tu, htu, rfl⟩ := Finset.mem_image.mp ht'M
      have hAct := (Finset.mem_filter.mp htu).2
      obtain ⟨q, ⟨hq, hq0⟩, -⟩ := hpart.1 (tu, (0 : Fin 4))
      obtain ⟨s₀, s₁, s₂, s₃, hqeq, hd1, hd2, hd3, halign'⟩ := hstruct q hq
      subst hqeq
      have hts₀ : tu = s₀ := hk0 _ _ _ _ _ hq0
      obtain ⟨u₁, hu₁mem, hu₁act⟩ := hAct _ hq hq0
      have hu₁ : u₁ = s₁ := hk1 _ _ _ _ _ hu₁mem
      subst hu₁
      -- the W-actual witness rules out the all-dummy branch
      have hall' : pW u₁.val.1 = u₁.val ∧ pX s₂.val.2.1 = s₂.val ∧
          pY s₃.val.2.2 = s₃.val := by
        rcases halign' with h | h
        · exact h
        · exact absurd hu₁act h.1
      have hs₂x : s₂.val.2.1 = x := by
        rw [hd2, ← hts₀]
        exact ht'x
      have hs₂val : s₂.val = pX x := by
        rw [← hs₂x]
        exact hall'.2.1.symm
      have hin : ((⟨pX x, (hpX x).1⟩ : ↥T), (2 : Fin 4)) ∈
          ({(s₀, 0), (u₁, 1), (s₂, 2), (s₃, 3)} : Finset (↥T × Fin 4)) := by
        have he : (⟨pX x, (hpX x).1⟩ : ↥T) = s₂ := Subtype.ext hs₂val.symm
        rw [he]
        simp
      have hqp : ({(s₀, 0), (u₁, 1), (s₂, 2), (s₃, 3)} :
          Finset (↥T × Fin 4)) = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} :=
        hpart.eq_of_mem hq hpstar hin hmem
      have hs₀mem : (s₀, (0 : Fin 4)) ∈
          ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)) := by
        rw [← hqp]
        simp
      have hs₀t₀ : s₀ = t₀ := hk0 _ _ _ _ _ hs₀mem
      rw [hts₀, hs₀t₀]
  · -- Y-cover
    intro y
    obtain ⟨pstar, ⟨hpstar, hmem⟩, -⟩ :=
      hpart.1 ((⟨pY y, (hpY y).1⟩ : ↥T), (3 : Fin 4))
    obtain ⟨t₀, t₁, t₂, t₃, hpeq, hc1, hc2, hc3, halign⟩ := hstruct pstar hpstar
    subst hpeq
    have ht₃ : t₃ = ⟨pY y, (hpY y).1⟩ := (hk3 _ _ _ _ _ hmem).symm
    have hact3 : pY t₃.val.2.2 = t₃.val := by
      rw [ht₃]
      change pY ((pY y).2.2) = pY y
      rw [(hpY y).2]
    have hall : pW t₁.val.1 = t₁.val ∧ pX t₂.val.2.1 = t₂.val ∧
        pY t₃.val.2.2 = t₃.val := by
      rcases halign with h | h
      · exact h
      · exact absurd hact3 h.2.2
    have ht₀y : t₀.val.2.2 = y := by
      rw [← hc3, ht₃]
      exact (hpY y).2
    refine ⟨t₀.val, ⟨?_, ht₀y⟩, ?_⟩
    · refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨Finset.mem_attach _ _, ?_⟩)
      intro q hq hq0
      have hqp : q = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} :=
        hpart.eq_of_mem hq hpstar hq0 (by simp)
      subst hqp
      exact ⟨t₁, by simp, hall.1⟩
    · rintro t' ⟨ht'M, ht'y⟩
      obtain ⟨tu, htu, rfl⟩ := Finset.mem_image.mp ht'M
      have hAct := (Finset.mem_filter.mp htu).2
      obtain ⟨q, ⟨hq, hq0⟩, -⟩ := hpart.1 (tu, (0 : Fin 4))
      obtain ⟨s₀, s₁, s₂, s₃, hqeq, hd1, hd2, hd3, halign'⟩ := hstruct q hq
      subst hqeq
      have hts₀ : tu = s₀ := hk0 _ _ _ _ _ hq0
      obtain ⟨u₁, hu₁mem, hu₁act⟩ := hAct _ hq hq0
      have hu₁ : u₁ = s₁ := hk1 _ _ _ _ _ hu₁mem
      subst hu₁
      have hall' : pW u₁.val.1 = u₁.val ∧ pX s₂.val.2.1 = s₂.val ∧
          pY s₃.val.2.2 = s₃.val := by
        rcases halign' with h | h
        · exact h
        · exact absurd hu₁act h.1
      have hs₃y : s₃.val.2.2 = y := by
        rw [hd3, ← hts₀]
        exact ht'y
      have hs₃val : s₃.val = pY y := by
        rw [← hs₃y]
        exact hall'.2.2.symm
      have hin : ((⟨pY y, (hpY y).1⟩ : ↥T), (3 : Fin 4)) ∈
          ({(s₀, 0), (u₁, 1), (s₂, 2), (s₃, 3)} : Finset (↥T × Fin 4)) := by
        have he : (⟨pY y, (hpY y).1⟩ : ↥T) = s₃ := Subtype.ext hs₃val.symm
        rw [he]
        simp
      have hqp : ({(s₀, 0), (u₁, 1), (s₂, 2), (s₃, 3)} :
          Finset (↥T × Fin 4)) = {(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} :=
        hpart.eq_of_mem hq hpstar hin hmem
      have hs₀mem : (s₀, (0 : Fin 4)) ∈
          ({(t₀, 0), (t₁, 1), (t₂, 2), (t₃, 3)} : Finset (↥T × Fin 4)) := by
        rw [← hqp]
        simp
      have hs₀t₀ : s₀ = t₀ := hk0 _ _ _ _ _ hs₀mem
      rw [hts₀, hs₀t₀]

end Backward

section Window

variable {r q : ℕ} {iW : W → ℕ} {iX : X → ℕ} {iY : Y → ℕ}
variable {pW : W → W × X × Y} {pX : X → W × X × Y} {pY : Y → W × X × Y}
variable {T : Finset (W × X × Y)}

omit [DecidableEq W] [DecidableEq X] [DecidableEq Y] in
/-- Under the radix margin `33·q ≤ r`, eleven times the subtracted term of a
triple element still fits under one leading unit — the slack the window
bounds need. -/
theorem mfp_sub_le' (hq : 33 * q ≤ r) (hiW : ∀ w, iW w < q)
    (hiX : ∀ x, iX x < q) (hiY : ∀ y, iY y < q) (t : W × X × Y) :
    11 * (iY t.2.2 * r ^ 3 + iX t.2.1 * r ^ 2 + iW t.1 * r) ≤ r ^ 4 := by
  have hq1 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) (hiW t.1)
  have hr : 0 < r := by omega
  have h3 : iY t.2.2 * r ^ 3 ≤ q * r ^ 3 :=
    Nat.mul_le_mul_right _ (hiY t.2.2).le
  have h2 : iX t.2.1 * r ^ 2 ≤ q * r ^ 3 :=
    Nat.mul_le_mul (hiX t.2.1).le (Nat.pow_le_pow_right hr (by omega))
  have h1 : iW t.1 * r ≤ q * r ^ 3 :=
    Nat.mul_le_mul (hiW t.1).le (Nat.le_self_pow (by omega) r)
  have hmargin : 33 * q * r ^ 3 ≤ r ^ 4 := by
    have := Nat.mul_le_mul_right (r ^ 3) hq
    have he : r * r ^ 3 = r ^ 4 := by ring
    omega
  have he : 33 * q * r ^ 3 = 33 * (q * r ^ 3) := by ring
  omega

/-- Every constructed size lies strictly inside the Garey–Johnson window:
`B < 5·s` and `3·s < B`. -/
theorem mfp_window (h33 : 33 ≤ r) (hq33 : 33 * q ≤ r)
    (hiW : ∀ w, iW w < q) (hiX : ∀ x, iX x < q) (hiY : ∀ y, iY y < q)
    (p : ↥T × Fin 4) :
    mfpB r < 5 * mfpSize r iW iX iY pW pX pY T p ∧
      3 * mfpSize r iW iX iY pW pX pY T p < mfpB r := by
  have hr : 0 < r := by omega
  have hqr : q ≤ r := by omega
  have p2 : r ^ 2 ≤ r ^ 4 := Nat.pow_le_pow_right hr (by omega)
  have p3 : r ^ 3 ≤ r ^ 4 := Nat.pow_le_pow_right hr (by omega)
  have p1 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ hr
  have p0 : r ≤ r ^ 4 := Nat.le_self_pow (by omega) r
  obtain ⟨tu, c⟩ := p
  have hiWr : ∀ w, iW w < r := fun w ↦ Nat.lt_of_lt_of_le (hiW w) hqr
  have hiXr : ∀ x, iX x < r := fun x ↦ Nat.lt_of_lt_of_le (hiX x) hqr
  have hiYr : ∀ y, iY y < r := fun y ↦ Nat.lt_of_lt_of_le (hiY y) hqr
  have hfin : ∀ c : Fin 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by decide
  rcases hfin c with rfl | rfl | rfl | rfl
  · rw [mfpSize_zero]
    have hsub := mfp_sub_le' hq33 hiW hiX hiY tu.val
    unfold mfpUSize mfpB
    omega
  · rw [mfpSize_one]
    have hb : iW tu.val.1 * r ≤ r ^ 2 := by
      have := Nat.mul_le_mul_right r (hiWr tu.val.1).le
      have he : r * r = r ^ 2 := by ring
      omega
    unfold mfpWSize mfpB
    by_cases hact : pW tu.val.1 = tu.val
    · rw [if_pos hact]; omega
    · rw [if_neg hact]; omega
  · rw [mfpSize_two]
    have hb : iX tu.val.2.1 * r ^ 2 ≤ r ^ 3 := by
      have := Nat.mul_le_mul_right (r ^ 2) (hiXr tu.val.2.1).le
      have he : r * r ^ 2 = r ^ 3 := by ring
      omega
    unfold mfpXSize mfpB
    by_cases hact : pX tu.val.2.1 = tu.val
    · rw [if_pos hact]; omega
    · rw [if_neg hact]; omega
  · rw [mfpSize_three]
    have hb : iY tu.val.2.2 * r ^ 3 ≤ r ^ 4 := by
      have := Nat.mul_le_mul_right (r ^ 3) (hiYr tu.val.2.2).le
      have he : r * r ^ 3 = r ^ 4 := by ring
      omega
    unfold mfpYSize mfpB
    by_cases hact : pY tu.val.2.2 = tu.val
    · rw [if_pos hact]; omega
    · rw [if_neg hact]; omega

/-- The designated (actual) copies are in bijection with the elements: one
actual `W`-copy per element of `W`. -/
theorem mfp_card_actualW [Fintype W]
    (hpW : ∀ w, pW w ∈ T ∧ (pW w).1 = w) :
    (Finset.univ.filter fun tu : ↥T ↦ pW tu.val.1 = tu.val).card
      = Fintype.card W := by
  refine Finset.card_bij (fun tu _ ↦ tu.val.1) (fun tu _ ↦ Finset.mem_univ _)
    ?_ ?_
  · intro a ha b hb heq
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    apply Subtype.ext
    rw [← ha', ← hb', heq]
  · intro w _
    refine ⟨⟨pW w, (hpW w).1⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change pW ((pW w).1) = pW w
      rw [(hpW w).2]
    · exact (hpW w).2

/-- One actual `X`-copy per element of `X`. -/
theorem mfp_card_actualX [Fintype X]
    (hpX : ∀ x, pX x ∈ T ∧ (pX x).2.1 = x) :
    (Finset.univ.filter fun tu : ↥T ↦ pX tu.val.2.1 = tu.val).card
      = Fintype.card X := by
  refine Finset.card_bij (fun tu _ ↦ tu.val.2.1) (fun tu _ ↦ Finset.mem_univ _)
    ?_ ?_
  · intro a ha b hb heq
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    apply Subtype.ext
    rw [← ha', ← hb', heq]
  · intro x _
    refine ⟨⟨pX x, (hpX x).1⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change pX ((pX x).2.1) = pX x
      rw [(hpX x).2]
    · exact (hpX x).2

/-- One actual `Y`-copy per element of `Y`. -/
theorem mfp_card_actualY [Fintype Y]
    (hpY : ∀ y, pY y ∈ T ∧ (pY y).2.2 = y) :
    (Finset.univ.filter fun tu : ↥T ↦ pY tu.val.2.2 = tu.val).card
      = Fintype.card Y := by
  refine Finset.card_bij (fun tu _ ↦ tu.val.2.2) (fun tu _ ↦ Finset.mem_univ _)
    ?_ ?_
  · intro a ha b hb heq
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    apply Subtype.ext
    rw [← ha', ← hb', heq]
  · intro y _
    refine ⟨⟨pY y, (hpY y).1⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change pY ((pY y).2.2) = pY y
      rw [(hpY y).2]
    · exact (hpY y).2

/-- The total of all constructed sizes is `m·B`, where `m = |T|` is the
number of parts a partition must have — provided the three element sets have
equal cardinality. Per element of `W`, the actual copy saves one leading
unit against the dummy's `11`; per element of `Y` it *adds* two against the
dummy's `8`; with `|W| = |X| = |Y|` the corrections cancel. -/
theorem mfp_total_sum [Fintype W] [Fintype X] [Fintype Y]
    (hiWr : ∀ w, iW w < r) (hiXr : ∀ x, iX x < r) (hiYr : ∀ y, iY y < r)
    (hpW : ∀ w, pW w ∈ T ∧ (pW w).1 = w)
    (hpX : ∀ x, pX x ∈ T ∧ (pX x).2.1 = x)
    (hpY : ∀ y, pY y ∈ T ∧ (pY y).2.2 = y)
    (hXW : Fintype.card X = Fintype.card W)
    (hYW : Fintype.card Y = Fintype.card W) :
    ∑ p : ↥T × Fin 4, mfpSize r iW iX iY pW pX pY T p
      = Fintype.card ↥T * mfpB r := by
  classical
  rw [Fintype.sum_prod_type]
  have hinner : ∀ tu : ↥T, ∑ c : Fin 4, mfpSize r iW iX iY pW pX pY T (tu, c)
      = (10 + ((if pW tu.val.1 = tu.val then (10 : ℕ) else 11)
          + ((if pX tu.val.2.1 = tu.val then (10 : ℕ) else 11)
            + (if pY tu.val.2.2 = tu.val then (10 : ℕ) else 8)))) * r ^ 4
        + 15 := by
    intro tu
    rw [Fin.sum_univ_four, mfpSize_zero, mfpSize_one, mfpSize_two,
      mfpSize_three]
    have hsub := mfp_sub_le hiWr hiXr hiYr tu.val
    unfold mfpUSize mfpWSize mfpXSize mfpYSize
    have hexp : (10 + ((if pW tu.val.1 = tu.val then (10 : ℕ) else 11)
        + ((if pX tu.val.2.1 = tu.val then (10 : ℕ) else 11)
          + (if pY tu.val.2.2 = tu.val then (10 : ℕ) else 8)))) * r ^ 4
        = 10 * r ^ 4 + (if pW tu.val.1 = tu.val then (10 : ℕ) else 11) * r ^ 4
          + (if pX tu.val.2.1 = tu.val then (10 : ℕ) else 11) * r ^ 4
          + (if pY tu.val.2.2 = tu.val then (10 : ℕ) else 8) * r ^ 4 := by
      ring
    omega
  simp only [hinner]
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul]
  -- the leading coefficients total 40 per triple, in aggregate
  have hcw : ∑ tu : ↥T, ((if pW tu.val.1 = tu.val then (10 : ℕ) else 11)
      + (if pW tu.val.1 = tu.val then (1 : ℕ) else 0)) = 11 * Fintype.card ↥T := by
    have h11 : ∀ tu : ↥T, ((if pW tu.val.1 = tu.val then (10 : ℕ) else 11)
        + (if pW tu.val.1 = tu.val then (1 : ℕ) else 0)) = 11 := by
      intro tu
      split_ifs <;> rfl
    simp only [h11]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
  have hcx : ∑ tu : ↥T, ((if pX tu.val.2.1 = tu.val then (10 : ℕ) else 11)
      + (if pX tu.val.2.1 = tu.val then (1 : ℕ) else 0)) = 11 * Fintype.card ↥T := by
    have h11 : ∀ tu : ↥T, ((if pX tu.val.2.1 = tu.val then (10 : ℕ) else 11)
        + (if pX tu.val.2.1 = tu.val then (1 : ℕ) else 0)) = 11 := by
      intro tu
      split_ifs <;> rfl
    simp only [h11]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
  have hcy : ∀ tu : ↥T, (if pY tu.val.2.2 = tu.val then (10 : ℕ) else 8)
      = 8 + 2 * (if pY tu.val.2.2 = tu.val then (1 : ℕ) else 0) := by
    intro tu
    split_ifs <;> rfl
  have hindW : ∑ tu : ↥T, (if pW tu.val.1 = tu.val then (1 : ℕ) else 0)
      = Fintype.card W := by
    rw [Finset.sum_boole, mfp_card_actualW hpW]
    simp
  have hindX : ∑ tu : ↥T, (if pX tu.val.2.1 = tu.val then (1 : ℕ) else 0)
      = Fintype.card W := by
    rw [Finset.sum_boole, mfp_card_actualX hpX]
    simp [hXW]
  have hindY : ∑ tu : ↥T, (if pY tu.val.2.2 = tu.val then (1 : ℕ) else 0)
      = Fintype.card W := by
    rw [Finset.sum_boole, mfp_card_actualY hpY]
    simp [hYW]
  have hcoef : ∑ tu : ↥T, (10 + ((if pW tu.val.1 = tu.val then (10 : ℕ) else 11)
      + ((if pX tu.val.2.1 = tu.val then (10 : ℕ) else 11)
        + (if pY tu.val.2.2 = tu.val then (10 : ℕ) else 8))))
      = 40 * Fintype.card ↥T := by
    simp only [hcy, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_add_distrib] at hcw hcx
    rw [hindW] at hcw
    rw [hindX] at hcx
    rw [hindY]
    omega
  rw [hcoef, Finset.card_univ, smul_eq_mul]
  unfold mfpB
  ring

end Window

section Glue

/-- The branch condition of the reduction: the three element sets have equal
cardinality, and every element occurs in some triple. Both are forced by a
matching (`matching3DGood_of_matching`), and both are what the size
bookkeeping needs — without them the constructed sizes need not total `m·B`,
and an uncovered element breaks the correspondence. Decidable, so the
reduction may branch on it. -/
def Matching3DGood (I : Matching3DInstance) : Prop :=
  Fintype.card I.X = Fintype.card I.W ∧ Fintype.card I.Y = Fintype.card I.W ∧
    (∀ w : I.W, ∃ t ∈ I.triples, t.1 = w) ∧
    (∀ x : I.X, ∃ t ∈ I.triples, t.2.1 = x) ∧
    (∀ y : I.Y, ∃ t ∈ I.triples, t.2.2 = y)

instance (I : Matching3DInstance) : Decidable (Matching3DGood I) := by
  unfold Matching3DGood
  infer_instance

/-- A matching forces the branch condition: the exact covers put `M` in
bijection with each of the three element sets, and every element is covered
through a triple of `M ⊆ T`. -/
theorem matching3DGood_of_matching {I : Matching3DInstance}
    (h : MATCHING_3D I) : Matching3DGood I := by
  obtain ⟨M, hMT, hcW, hcX, hcY⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hcX.card_eq]
    exact hcW.card_eq
  · rw [← hcY.card_eq]
    exact hcW.card_eq
  · intro w
    obtain ⟨t, htM, hw⟩ := hcW.exists_mem w
    exact ⟨t, hMT htM, hw⟩
  · intro x
    obtain ⟨t, htM, hx⟩ := hcX.exists_mem x
    exact ⟨t, hMT htM, hx⟩
  · intro y
    obtain ⟨t, htM, hy⟩ := hcY.exists_mem y
    exact ⟨t, hMT htM, hy⟩

/-- The fixed no-instance for the degenerate branch: all sizes even, bound
odd, so no part can hit the bound — yet every size is inside the window and
the total is `m·B`, so the branch lands in the restriction too. -/
theorem not_fourPartition_parityNo :
    ¬ FOUR_PARTITION ⟨[6, 6, 6, 6, 6, 8, 8, 8], 27⟩ := by
  intro h
  unfold FOUR_PARTITION at h
  obtain ⟨parts, hcov, hprops⟩ := h
  obtain ⟨p, ⟨hp, -⟩, -⟩ := hcov ⟨0, by decide⟩
  obtain ⟨-, hsum⟩ := hprops p hp
  have heven : (∑ i ∈ p, ([6, 6, 6, 6, 6, 8, 8, 8] : List ℕ)[i.1]) % 2
      = 0 := by
    have hz : ∀ a ∈ ([6, 6, 6, 6, 6, 8, 8, 8] : List ℕ), a % 2 = 0 := by
      decide
    calc (∑ i ∈ p, ([6, 6, 6, 6, 6, 8, 8, 8] : List ℕ)[i.1]) % 2
        = (∑ i ∈ p, ([6, 6, 6, 6, 6, 8, 8, 8] : List ℕ)[i.1] % 2) % 2 :=
          Finset.sum_nat_mod p 2 _
      _ = (∑ _i ∈ p, 0) % 2 := congrArg (· % 2)
          (Finset.sum_congr rfl fun i _ ↦ hz _ (List.getElem_mem _))
      _ = 0 := by simp
  rw [hsum] at heven
  exact absurd heven (by decide)

/-- The radix: `33·(q+1)` for `q` the common cardinality — at least `33`, and
with the margin `33·q ≤ r` the window bounds need. -/
def mfpRadix (I : Matching3DInstance) : ℕ := 33 * (Fintype.card I.W + 1)

/-- The gadget's number list: four sizes per triple, flattened along an
enumeration of the tagged element type. -/
noncomputable def mfpNums (I : Matching3DInstance) (h : Matching3DGood I) :
    List ℕ :=
  List.ofFn fun j : Fin (Fintype.card (↥I.triples × Fin 4)) ↦
    mfpSize (mfpRadix I) (fun w ↦ (Fintype.equivFin I.W w).val)
      (fun x ↦ (Fintype.equivFin I.X x).val)
      (fun y ↦ (Fintype.equivFin I.Y y).val)
      (fun w ↦ (h.2.2.1 w).choose) (fun x ↦ (h.2.2.2.1 x).choose)
      (fun y ↦ (h.2.2.2.2 y).choose) I.triples
      ((Fintype.equivFin (↥I.triples × Fin 4)).symm j)

/-- The instance map: the gadget when the branch condition holds, the parity
no-instance otherwise. -/
noncomputable def matching3DFourPartitionInstance (I : Matching3DInstance) :
    NumberTargetInstance :=
  if h : Matching3DGood I then ⟨mfpNums I h, mfpB (mfpRadix I)⟩
  else ⟨[6, 6, 6, 6, 6, 8, 8, 8], 27⟩

/-- Transport: 4-PARTITION of the emitted instance is the sized-partition
question over the tagged element type. -/
theorem fourPartition_mfpNums_iff (I : Matching3DInstance)
    (h : Matching3DGood I) :
    FOUR_PARTITION ⟨mfpNums I h, mfpB (mfpRadix I)⟩ ↔
      ∃ parts, IsSizedPartition
        (mfpSize (mfpRadix I) (fun w ↦ (Fintype.equivFin I.W w).val)
          (fun x ↦ (Fintype.equivFin I.X x).val)
          (fun y ↦ (Fintype.equivFin I.Y y).val)
          (fun w ↦ (h.2.2.1 w).choose) (fun x ↦ (h.2.2.2.1 x).choose)
          (fun y ↦ (h.2.2.2.2 y).choose) I.triples) 4 (mfpB (mfpRadix I))
        parts := by
  unfold FOUR_PARTITION mfpNums
  dsimp only
  rw [exists_isSizedPartition_ofFn_iff]
  exact (exists_isSizedPartition_iff_map
    (Fintype.equivFin (↥I.triples × Fin 4)) _ 4 _).symm

/-- Correctness of the instance map. -/
theorem matching3D_iff_fourPartitionInstance (I : Matching3DInstance) :
    MATCHING_3D I ↔ FOUR_PARTITION (matching3DFourPartitionInstance I) := by
  unfold matching3DFourPartitionInstance
  by_cases h : Matching3DGood I
  · rw [dif_pos h, fourPartition_mfpNums_iff I h]
    have h33 : (33 : ℕ) ≤ mfpRadix I := by
      unfold mfpRadix
      omega
    have hiW : ∀ w : I.W, (Fintype.equivFin I.W w).val < mfpRadix I := by
      intro w
      have := (Fintype.equivFin I.W w).isLt
      unfold mfpRadix
      omega
    have hiX : ∀ x : I.X, (Fintype.equivFin I.X x).val < mfpRadix I := by
      intro x
      have h1 : ((Fintype.equivFin I.X x) : ℕ) < Fintype.card I.W :=
        Nat.lt_of_lt_of_le (Fintype.equivFin I.X x).isLt h.1.le
      unfold mfpRadix
      omega
    have hiY : ∀ y : I.Y, (Fintype.equivFin I.Y y).val < mfpRadix I := by
      intro y
      have h1 : ((Fintype.equivFin I.Y y) : ℕ) < Fintype.card I.W :=
        Nat.lt_of_lt_of_le (Fintype.equivFin I.Y y).isLt h.2.1.le
      unfold mfpRadix
      omega
    have hinjW : Function.Injective fun w ↦ (Fintype.equivFin I.W w).val :=
      fun a b hab ↦ (Fintype.equivFin I.W).injective (Fin.val_injective hab)
    have hinjX : Function.Injective fun x ↦ (Fintype.equivFin I.X x).val :=
      fun a b hab ↦ (Fintype.equivFin I.X).injective (Fin.val_injective hab)
    have hinjY : Function.Injective fun y ↦ (Fintype.equivFin I.Y y).val :=
      fun a b hab ↦ (Fintype.equivFin I.Y).injective (Fin.val_injective hab)
    have hpW : ∀ w, (h.2.2.1 w).choose ∈ I.triples ∧
        ((h.2.2.1 w).choose).1 = w := fun w ↦ (h.2.2.1 w).choose_spec
    have hpX : ∀ x, (h.2.2.2.1 x).choose ∈ I.triples ∧
        ((h.2.2.2.1 x).choose).2.1 = x := fun x ↦ (h.2.2.2.1 x).choose_spec
    have hpY : ∀ y, (h.2.2.2.2 y).choose ∈ I.triples ∧
        ((h.2.2.2.2 y).choose).2.2 = y := fun y ↦ (h.2.2.2.2 y).choose_spec
    constructor
    · rintro ⟨M, hMT, hcW, hcX, hcY⟩
      exact exists_isSizedPartition_of_matching hiW hiX hiY hpW hpX hpY hMT
        hcW hcX hcY
    · rintro ⟨parts, hparts⟩
      exact exists_matching_of_isSizedPartition h33 hiW hiX hiY hinjW hinjX
        hinjY hpW hpX hpY hparts
  · rw [dif_neg h]
    constructor
    · intro hm
      exact absurd (matching3DGood_of_matching hm) h
    · intro hp
      exact absurd hp not_fourPartition_parityNo

/-- The instance map lands inside the Garey–Johnson window on every input. -/
theorem fourPartitionWindow_matching3DFourPartitionInstance
    (I : Matching3DInstance) :
    FourPartitionWindow (matching3DFourPartitionInstance I) := by
  unfold matching3DFourPartitionInstance
  by_cases h : Matching3DGood I
  · rw [dif_pos h]
    have h33 : (33 : ℕ) ≤ mfpRadix I := by
      unfold mfpRadix
      omega
    have hq33 : 33 * Fintype.card I.W ≤ mfpRadix I := by
      unfold mfpRadix
      omega
    have hiWq : ∀ w : I.W, (Fintype.equivFin I.W w).val < Fintype.card I.W :=
      fun w ↦ (Fintype.equivFin I.W w).isLt
    have hiXq : ∀ x : I.X, (Fintype.equivFin I.X x).val < Fintype.card I.W :=
      fun x ↦ Nat.lt_of_lt_of_le (Fintype.equivFin I.X x).isLt h.1.le
    have hiYq : ∀ y : I.Y, (Fintype.equivFin I.Y y).val < Fintype.card I.W :=
      fun y ↦ Nat.lt_of_lt_of_le (Fintype.equivFin I.Y y).isLt h.2.1.le
    have hpW : ∀ w, (h.2.2.1 w).choose ∈ I.triples ∧
        ((h.2.2.1 w).choose).1 = w := fun w ↦ (h.2.2.1 w).choose_spec
    have hpX : ∀ x, (h.2.2.2.1 x).choose ∈ I.triples ∧
        ((h.2.2.2.1 x).choose).2.1 = x := fun x ↦ (h.2.2.2.1 x).choose_spec
    have hpY : ∀ y, (h.2.2.2.2 y).choose ∈ I.triples ∧
        ((h.2.2.2.2 y).choose).2.2 = y := fun y ↦ (h.2.2.2.2 y).choose_spec
    unfold FourPartitionWindow
    dsimp only
    constructor
    · intro a ha
      unfold mfpNums at ha
      rw [List.mem_ofFn] at ha
      obtain ⟨j, rfl⟩ := ha
      exact mfp_window h33 hq33 hiWq hiXq hiYq _
    · unfold mfpNums
      rw [List.sum_ofFn, List.length_ofFn]
      have hiWr : ∀ w : I.W, (Fintype.equivFin I.W w).val < mfpRadix I :=
        fun w ↦ Nat.lt_of_lt_of_le (hiWq w) (by unfold mfpRadix; omega)
      have hiXr : ∀ x : I.X, (Fintype.equivFin I.X x).val < mfpRadix I :=
        fun x ↦ Nat.lt_of_lt_of_le (hiXq x) (by unfold mfpRadix; omega)
      have hiYr : ∀ y : I.Y, (Fintype.equivFin I.Y y).val < mfpRadix I :=
        fun y ↦ Nat.lt_of_lt_of_le (hiYq y) (by unfold mfpRadix; omega)
      have htot := Equiv.sum_comp
        (Fintype.equivFin (↥I.triples × Fin 4)).symm
        (mfpSize (mfpRadix I) (fun w ↦ (Fintype.equivFin I.W w).val)
          (fun x ↦ (Fintype.equivFin I.X x).val)
          (fun y ↦ (Fintype.equivFin I.Y y).val)
          (fun w ↦ (h.2.2.1 w).choose) (fun x ↦ (h.2.2.2.1 x).choose)
          (fun y ↦ (h.2.2.2.2 y).choose) I.triples)
      rw [htot, mfp_total_sum hiWr hiXr hiYr hpW hpX hpY h.1 h.2.1,
        Fintype.card_prod, Fintype.card_fin]
      ring
  · rw [dif_neg h]
    exact ⟨by decide, by decide⟩

/-- The reduction 3-DIMENSIONAL MATCHING → 4-PARTITION, landing inside the
Garey–Johnson window: 4-PARTITION is hard even when every size lies strictly
between `B/5` and `B/3` and the sizes total `m·B`. -/
noncomputable def matching3DToFourPartition :
    MATCHING_3D ⟶ᵣ FOUR_PARTITION.restrict FourPartitionWindow :=
  Reduction.codRestrict
    ⟨matching3DFourPartitionInstance, matching3D_iff_fourPartitionInstance⟩
    FourPartitionWindow fourPartitionWindow_matching3DFourPartitionInstance

/-- The same map, read against the unrestricted target. -/
noncomputable def matching3DToFourPartitionPlain :
    MATCHING_3D ⟶ᵣ FOUR_PARTITION :=
  ⟨matching3DFourPartitionInstance, matching3D_iff_fourPartitionInstance⟩

end Glue

end Hardness
