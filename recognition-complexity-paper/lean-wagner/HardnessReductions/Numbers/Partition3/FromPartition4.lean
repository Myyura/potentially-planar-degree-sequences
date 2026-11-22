import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import HardnessReductions.Numbers.Partition3
import HardnessReductions.Numbers.Partition4
import HardnessReductions.Numbers.Partition4.FromMatching3D

/-!
# 4-PARTITION → 3-PARTITION

Garey–Johnson's Theorem 4.4, the second half of the strong-hardness chain:
4-PARTITION *inside the window* — every size strictly between `B/5` and `B/3`,
sizes totalling `m·B` — reduces to 3-PARTITION, again inside a window.

## The construction

Over an index type `α` carrying the numbers `s`, the constructed instance has
three kinds of element:

* a **regular** element per index `a`, of size `20B + 4·s a + 1`;
* two **pairing** elements per ordered pair `p` of distinct indices, of sizes
  `24B + 2 − 4·v` and `20B + 4·v + 2` where `v = s p.1 + s p.2` — a *matched
  pair*, since the two sizes total `44B + 4`;
* `F` **filler** elements of size `20B`,

with bound `B' = 64B + 4`. The residues `1`, `2`, `0` of the three kinds
against `B' ≡ 0 (mod 4)` force every part to hold either two regular elements
and one pairing element, or two pairing elements and one filler.

## The backward direction, counted rather than exchanged

Garey–Johnson recover the 4-partition by repeatedly *exchanging* equal-sized
pairing elements until every filler part holds a matched pair. Here the same
conclusion comes from a count. Give each pairing element the value

`β(u) = v`,  `β(ū) = B − v`,

so that a matched pair has `β`-sum `B`. Then: a part with two pairing elements
has `β`-sum `B` (all three ways two pairing sizes can total `44B + 4` say so),
and a part with two regular elements `a`, `b` carries a pairing element with
`β = s a + s b`. Since the whole pool splits into matched pairs, the pairing
elements *not* used by regular parts still have `β`-multiplicities symmetric
under `v ↦ B − v`, so `exists_pairs_of_card_symm` (`Numbers/Defs.lean`) pairs
the regular parts up; each such pair of parts has four regular elements of
total size `B`, and those are the 4-partition's parts.
-/

namespace Hardness

section Construction

variable {α : Type} {F : ℕ}

/-- An ordered pair of distinct indices: the pool the pairing elements are
indexed by. Ordered, because the construction never needs `p` and its reverse
to be the same object — it needs only that each pool entry carries *two*
elements of complementary size. -/
abbrev TpPair (α : Type) : Type := {p : α × α // p.1 ≠ p.2}

/-- The tagged elements of the constructed 3-PARTITION instance: one
*regular* element per index, two *pairing* elements per pool entry, and `F`
*filler* elements. A tagged tuple of input objects throughout, in the
library's naming discipline — no counters. -/
abbrev TpElt (α : Type) (F : ℕ) : Type := α ⊕ (TpPair α × Bool) ⊕ Fin F

/-- The combined size of a pool entry's two numbers. -/
def pairVal (s : α → ℕ) (p : TpPair α) : ℕ := s p.val.1 + s p.val.2

/-- The sizes of the constructed elements. The two pairing elements of a pool
entry are *matched*: their sizes total `44B + 4`, which is `B'` minus a
filler. -/
def tpSize (s : α → ℕ) (B : ℕ) : TpElt α F → ℕ
  | .inl a => 20 * B + 4 * s a + 1
  | .inr (.inl (p, false)) => 24 * B + 2 - 4 * pairVal s p
  | .inr (.inl (p, true)) => 20 * B + 4 * pairVal s p + 2
  | .inr (.inr _) => 20 * B

/-- The constructed bound. -/
def tpBound (B : ℕ) : ℕ := 64 * B + 4

/-- The complementary value of a pairing element: `v` for the first of a
matched pair, `B − v` for the second, so that a matched pair has value sum
`B`. Regular and filler elements are given `0`; the value is only ever read
on pairing elements. -/
def tpBeta (s : α → ℕ) (B : ℕ) : TpElt α F → ℕ
  | .inr (.inl (p, false)) => pairVal s p
  | .inr (.inl (p, true)) => B - pairVal s p
  | _ => 0

@[simp] theorem tpSize_reg (s : α → ℕ) (B : ℕ) (a : α) :
    tpSize (F := F) s B (.inl a) = 20 * B + 4 * s a + 1 := rfl

@[simp] theorem tpSize_pair_false (s : α → ℕ) (B : ℕ) (p : TpPair α) :
    tpSize (F := F) s B (.inr (.inl (p, false)))
      = 24 * B + 2 - 4 * pairVal s p := rfl

@[simp] theorem tpSize_pair_true (s : α → ℕ) (B : ℕ) (p : TpPair α) :
    tpSize (F := F) s B (.inr (.inl (p, true)))
      = 20 * B + 4 * pairVal s p + 2 := rfl

@[simp] theorem tpSize_filler (s : α → ℕ) (B : ℕ) (k : Fin F) :
    tpSize s B (.inr (.inr k)) = 20 * B := rfl

@[simp] theorem tpBeta_pair_false (s : α → ℕ) (B : ℕ) (p : TpPair α) :
    tpBeta (F := F) s B (.inr (.inl (p, false))) = pairVal s p := rfl

@[simp] theorem tpBeta_pair_true (s : α → ℕ) (B : ℕ) (p : TpPair α) :
    tpBeta (F := F) s B (.inr (.inl (p, true))) = B - pairVal s p := rfl

/-- Every pool value is well inside the bound — the fact that keeps all the
truncated subtractions above honest. -/
theorem pairVal_lt (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B) (p : TpPair α) :
    3 * pairVal s p < 2 * B := by
  have h1 := hs p.val.1
  have h2 := hs p.val.2
  unfold pairVal
  omega

/-- The sizes of a matched pair total `B' − 20B`: a matched pair plus a
filler is a part. -/
theorem tpSize_matched (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    (p : TpPair α) :
    tpSize (F := F) s B (.inr (.inl (p, false)))
        + tpSize (F := F) s B (.inr (.inl (p, true)))
      = 44 * B + 4 := by
  have h := pairVal_lt s hs p
  simp only [tpSize_pair_false, tpSize_pair_true]
  omega

/-! ## Residues, and what a part can look like -/

/-- A regular element's size is `1` mod `4`. -/
theorem tpSize_reg_mod (s : α → ℕ) (B : ℕ) (a : α) :
    tpSize (F := F) s B (.inl a) % 4 = 1 := by
  simp only [tpSize_reg]; omega

/-- A pairing element's size is `2` mod `4` — for either member of a matched
pair, which is what makes the classification blind to the two types. -/
theorem tpSize_pair_mod (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    (q : TpPair α × Bool) :
    tpSize (F := F) s B (.inr (.inl q)) % 4 = 2 := by
  obtain ⟨p, b⟩ := q
  have h := pairVal_lt s hs p
  cases b <;> simp only [tpSize_pair_false, tpSize_pair_true] <;> omega

/-- A filler's size is `0` mod `4`. -/
theorem tpSize_filler_mod (s : α → ℕ) (B : ℕ) (k : Fin F) :
    tpSize s B (.inr (.inr k)) % 4 = 0 := by
  simp only [tpSize_filler]; omega

/-- Reading a part's `β`-arithmetic off its size arithmetic: two pairing
elements whose sizes total `44B + 4` — a part's worth, minus a filler — have
complementary values, however the two are typed. -/
theorem tpBeta_add_tpBeta (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    (q q' : TpPair α × Bool)
    (h : tpSize (F := F) s B (.inr (.inl q)) + tpSize (F := F) s B (.inr (.inl q'))
      = 44 * B + 4) :
    tpBeta (F := F) s B (.inr (.inl q)) + tpBeta (F := F) s B (.inr (.inl q'))
      = B := by
  obtain ⟨p, b⟩ := q
  obtain ⟨p', b'⟩ := q'
  have hp := pairVal_lt s hs p
  have hp' := pairVal_lt s hs p'
  cases b <;> cases b' <;>
    simp only [tpSize_pair_false, tpSize_pair_true, tpBeta_pair_false,
      tpBeta_pair_true] at h ⊢ <;> omega

/-- And the same for the pairing element of a part with two regular elements:
its size pins its value to the two numbers' total. -/
theorem tpBeta_eq_of_tpSize (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    (q : TpPair α × Bool) {d : ℕ} (hd : 3 * d < 2 * B)
    (h : tpSize (F := F) s B (.inr (.inl q)) = 24 * B + 2 - 4 * d) :
    tpBeta (F := F) s B (.inr (.inl q)) = d := by
  obtain ⟨p, b⟩ := q
  have hp := pairVal_lt s hs p
  cases b <;>
    simp only [tpSize_pair_false, tpSize_pair_true, tpBeta_pair_false,
      tpBeta_pair_true] at h ⊢ <;> omega

end Construction

section Parts

variable {α : Type} [DecidableEq α] {F : ℕ}

/-- A three-element finset, read from one of its elements: the other two, and
the resulting listing. -/
theorem exists_two_of_card_three {T : Type*} [DecidableEq T] {P : Finset T}
    {x : T} (hcard : P.card = 3) (hx : x ∈ P) :
    ∃ y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ P = {x, y, z} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨b, c, hab, hac, hbc, rfl⟩
  · exact ⟨a, c, fun h ↦ hab h.symm, hbc, hac, by ext t; simp; tauto⟩
  · exact ⟨a, b, fun h ↦ hac h.symm, fun h ↦ hbc h.symm, hab,
      by ext t; simp; tauto⟩

/-- The sum over a three-element listing. -/
theorem sum_triple {T : Type*} [DecidableEq T] {x y z : T} (f : T → ℕ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∑ t ∈ ({x, y, z} : Finset T), f t = f x + f y + f z := by
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, ← add_assoc]

/-- **What a part holding a pairing element is**: either two regular
elements — and then the pairing element's value is those two numbers'
total — or a second pairing element of complementary value together with a
filler. Everything else is excluded by the residues, except three fillers,
excluded by their total `60B ≠ B'`. -/
theorem tp_part_of_mem_pair (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    {P : Finset (TpElt α F)} (hcard : P.card = 3)
    (hsum : ∑ x ∈ P, tpSize s B x = tpBound B) {q : TpPair α × Bool}
    (hq : Sum.inr (Sum.inl q) ∈ P) :
    (∃ a b : α, a ≠ b ∧ P = {Sum.inl a, Sum.inl b, Sum.inr (Sum.inl q)} ∧
        tpBeta (F := F) s B (Sum.inr (Sum.inl q)) = s a + s b) ∨
      (∃ (q' : TpPair α × Bool) (k : Fin F),
        P = {Sum.inr (Sum.inl q), Sum.inr (Sum.inl q'), Sum.inr (Sum.inr k)} ∧
          tpBeta (F := F) s B (Sum.inr (Sum.inl q))
            + tpBeta (F := F) s B (Sum.inr (Sum.inl q')) = B) := by
  obtain ⟨y, z, hxy, hxz, hyz, rfl⟩ := exists_two_of_card_three hcard hq
  rw [sum_triple _ hxy hxz hyz, tpBound] at hsum
  have hmq := tpSize_pair_mod (F := F) s hs q
  rcases y with b | q' | k <;> rcases z with c | q'' | k'
  · -- two regular elements: the pairing element's value is their total
    have hbc : b ≠ c := fun h ↦ hyz (by rw [h])
    refine Or.inl ⟨b, c, hbc, by ext t; simp; tauto, ?_⟩
    refine tpBeta_eq_of_tpSize s hs q (by have := hs b; have := hs c; omega) ?_
    simp only [tpSize_reg] at hsum
    omega
  · exact absurd hsum (by
      have := tpSize_reg_mod (F := F) s B b
      have := tpSize_pair_mod (F := F) s hs q''
      omega)
  · exact absurd hsum (by
      have := tpSize_reg_mod (F := F) s B b
      have := tpSize_filler_mod (F := F) s B k'
      omega)
  · exact absurd hsum (by
      have := tpSize_pair_mod (F := F) s hs q'
      have := tpSize_reg_mod (F := F) s B c
      omega)
  · exact absurd hsum (by
      have := tpSize_pair_mod (F := F) s hs q'
      have := tpSize_pair_mod (F := F) s hs q''
      omega)
  · -- a matched-in-value pairing element and a filler
    refine Or.inr ⟨q', k', rfl, tpBeta_add_tpBeta s hs q q' ?_⟩
    simp only [tpSize_filler] at hsum
    omega
  · exact absurd hsum (by
      have := tpSize_filler_mod (F := F) s B k
      have := tpSize_reg_mod (F := F) s B c
      omega)
  · refine Or.inr ⟨q'', k, by ext t; simp; tauto, tpBeta_add_tpBeta s hs q q'' ?_⟩
    simp only [tpSize_filler] at hsum
    omega
  · exact absurd hsum (by
      have := tpSize_filler_mod (F := F) s B k
      have := tpSize_filler_mod (F := F) s B k'
      omega)

/-- **What a part holding a regular element is**: a second regular element and
a pairing element whose value is the two numbers' total. -/
theorem tp_part_of_mem_reg (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    {P : Finset (TpElt α F)} (hcard : P.card = 3)
    (hsum : ∑ x ∈ P, tpSize s B x = tpBound B) {a : α}
    (ha : (Sum.inl a : TpElt α F) ∈ P) :
    ∃ (b : α) (q : TpPair α × Bool), a ≠ b ∧
      P = {Sum.inl a, Sum.inl b, Sum.inr (Sum.inl q)} ∧
        tpBeta (F := F) s B (Sum.inr (Sum.inl q)) = s a + s b := by
  obtain ⟨y, z, hxy, hxz, hyz, rfl⟩ := exists_two_of_card_three hcard ha
  rw [sum_triple _ hxy hxz hyz, tpBound] at hsum
  have hma := tpSize_reg_mod (F := F) s B a
  rcases y with b | q' | k <;> rcases z with c | q'' | k'
  · exact absurd hsum (by
      have := tpSize_reg_mod (F := F) s B b
      have := tpSize_reg_mod (F := F) s B c
      omega)
  · -- a second regular element in the third slot
    refine ⟨b, q'', fun h ↦ hxy (by rw [h]), rfl, ?_⟩
    refine tpBeta_eq_of_tpSize s hs q'' (by have := hs a; have := hs b; omega) ?_
    simp only [tpSize_reg] at hsum
    omega
  · exact absurd hsum (by
      have := tpSize_reg_mod (F := F) s B b
      have := tpSize_filler_mod (F := F) s B k'
      omega)
  · refine ⟨c, q', fun h ↦ hxz (by rw [h]), by ext t; simp; tauto, ?_⟩
    refine tpBeta_eq_of_tpSize s hs q' (by have := hs a; have := hs c; omega) ?_
    simp only [tpSize_reg] at hsum
    omega
  · exact absurd hsum (by
      have := tpSize_pair_mod (F := F) s hs q'
      have := tpSize_pair_mod (F := F) s hs q''
      omega)
  · exact absurd hsum (by
      have := tpSize_pair_mod (F := F) s hs q'
      have := tpSize_filler_mod (F := F) s B k'
      omega)
  · exact absurd hsum (by
      have := tpSize_filler_mod (F := F) s B k
      have := tpSize_reg_mod (F := F) s B c
      omega)
  · exact absurd hsum (by
      have := tpSize_filler_mod (F := F) s B k
      have := tpSize_pair_mod (F := F) s hs q''
      omega)
  · exact absurd hsum (by
      have := tpSize_filler_mod (F := F) s B k
      have := tpSize_filler_mod (F := F) s B k'
      omega)

end Parts

/-! ## The three shapes of constructed part -/

section Shapes

variable {α : Type} [DecidableEq α] {F : ℕ}

/-- The part carrying the *chosen* half of a 4-set: its two chosen indices,
and the first element of their pool entry's matched pair. -/
def tpPartLo (p : TpPair α) : Finset (TpElt α F) :=
  {Sum.inl p.val.1, Sum.inl p.val.2, Sum.inr (Sum.inl (p, false))}

/-- The part carrying the other half of the 4-set `X`: its two remaining
indices, and the second element of the pool entry's matched pair. -/
def tpPartHi (X : Finset α) (p : TpPair α) : Finset (TpElt α F) :=
  insert (Sum.inr (Sum.inl (p, true))) ((X \ {p.val.1, p.val.2}).image Sum.inl)

/-- The part carrying an *unused* pool entry: its matched pair, and a
filler. -/
def tpPartFill (p : TpPair α) (k : Fin F) : Finset (TpElt α F) :=
  {Sum.inr (Sum.inl (p, false)), Sum.inr (Sum.inl (p, true)),
    Sum.inr (Sum.inr k)}

@[simp] theorem mem_tpPartLo_inl {p : TpPair α} {a : α} :
    (Sum.inl a : TpElt α F) ∈ tpPartLo p ↔ a = p.val.1 ∨ a = p.val.2 := by
  simp [tpPartLo]

@[simp] theorem mem_tpPartLo_pair {p : TpPair α} {q : TpPair α × Bool} :
    (Sum.inr (Sum.inl q) : TpElt α F) ∈ tpPartLo p ↔ q = (p, false) := by
  simp [tpPartLo]

@[simp] theorem mem_tpPartLo_fill {p : TpPair α} {k : Fin F} :
    (Sum.inr (Sum.inr k) : TpElt α F) ∈ tpPartLo p ↔ False := by
  simp [tpPartLo]

@[simp] theorem mem_tpPartHi_inl {X : Finset α} {p : TpPair α} {a : α} :
    (Sum.inl a : TpElt α F) ∈ tpPartHi X p ↔
      a ∈ X ∧ a ≠ p.val.1 ∧ a ≠ p.val.2 := by
  simp [tpPartHi, and_assoc]

@[simp] theorem mem_tpPartHi_pair {X : Finset α} {p : TpPair α}
    {q : TpPair α × Bool} :
    (Sum.inr (Sum.inl q) : TpElt α F) ∈ tpPartHi X p ↔ q = (p, true) := by
  simp [tpPartHi]

@[simp] theorem mem_tpPartHi_fill {X : Finset α} {p : TpPair α} {k : Fin F} :
    (Sum.inr (Sum.inr k) : TpElt α F) ∈ tpPartHi X p ↔ False := by
  simp [tpPartHi]

@[simp] theorem mem_tpPartFill_inl {p : TpPair α} {k : Fin F} {a : α} :
    (Sum.inl a : TpElt α F) ∈ tpPartFill p k ↔ False := by
  simp [tpPartFill]

@[simp] theorem mem_tpPartFill_pair {p : TpPair α} {k : Fin F}
    {q : TpPair α × Bool} :
    (Sum.inr (Sum.inl q) : TpElt α F) ∈ tpPartFill p k ↔
      q = (p, false) ∨ q = (p, true) := by
  simp [tpPartFill]

@[simp] theorem mem_tpPartFill_fill {p : TpPair α} {k k' : Fin F} :
    (Sum.inr (Sum.inr k') : TpElt α F) ∈ tpPartFill p k ↔ k' = k := by
  simp [tpPartFill]

theorem tpPartLo_card (p : TpPair α) : (tpPartLo (F := F) p).card = 3 := by
  have h1 : (Sum.inl p.val.1 : TpElt α F) ≠ Sum.inl p.val.2 := by
    simpa using p.property
  rw [tpPartLo, Finset.card_insert_of_notMem (by simp [h1]),
    Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

theorem tpPartFill_card (p : TpPair α) (k : Fin F) :
    (tpPartFill p k).card = 3 := by
  rw [tpPartFill, Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

theorem tpPartHi_card {X : Finset α} {p : TpPair α} (hcard : X.card = 4)
    (h1 : p.val.1 ∈ X) (h2 : p.val.2 ∈ X) :
    (tpPartHi (F := F) X p).card = 3 := by
  have hpair : ({p.val.1, p.val.2} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using p.property),
      Finset.card_singleton]
  have hsub : ({p.val.1, p.val.2} : Finset α) ⊆ X := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · exact h1
    · rw [Finset.mem_singleton.mp ha']; exact h2
  have hdiff : (X \ {p.val.1, p.val.2}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard, hpair]
  rw [tpPartHi, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ Sum.inl_injective, hdiff]

theorem tpPartLo_sum (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    (p : TpPair α) :
    ∑ x ∈ tpPartLo (F := F) p, tpSize s B x = tpBound B := by
  have hne : (Sum.inl p.val.1 : TpElt α F) ≠ Sum.inl p.val.2 := by
    simpa using p.property
  have h := pairVal_lt s hs p
  rw [tpPartLo, sum_triple _ hne (by simp) (by simp)]
  simp only [tpSize_reg, tpSize_pair_false, tpBound]
  unfold pairVal
  have := hs p.val.1
  have := hs p.val.2
  omega

theorem tpPartFill_sum (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    (p : TpPair α) (k : Fin F) :
    ∑ x ∈ tpPartFill p k, tpSize s B x = tpBound B := by
  have h := pairVal_lt s hs p
  rw [tpPartFill, sum_triple _ (by simp) (by simp) (by simp)]
  simp only [tpSize_pair_false, tpSize_pair_true, tpSize_filler, tpBound]
  omega

theorem tpPartHi_sum (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    {X : Finset α} {p : TpPair α} (hcard : X.card = 4) (h1 : p.val.1 ∈ X)
    (h2 : p.val.2 ∈ X) (hXsum : ∑ a ∈ X, s a = B) :
    ∑ x ∈ tpPartHi (F := F) X p, tpSize s B x = tpBound B := by
  have hpair : ({p.val.1, p.val.2} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using p.property),
      Finset.card_singleton]
  have hsub : ({p.val.1, p.val.2} : Finset α) ⊆ X := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · exact h1
    · rw [Finset.mem_singleton.mp ha']; exact h2
  have hdiff : (X \ {p.val.1, p.val.2}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard, hpair]
  have hpsum : ∑ a ∈ ({p.val.1, p.val.2} : Finset α), s a = pairVal s p := by
    rw [Finset.sum_insert (by simpa using p.property), Finset.sum_singleton]
    rfl
  have hdsum : ∑ a ∈ X \ {p.val.1, p.val.2}, s a + pairVal s p = B := by
    have h := Finset.sum_sdiff (f := s) hsub
    rw [hXsum, hpsum] at h
    exact h
  have hv := pairVal_lt s hs p
  rw [tpPartHi, Finset.sum_insert (by simp),
    Finset.sum_image (fun a _ b _ h ↦ Sum.inl_injective h)]
  have hexp : ∑ a ∈ X \ {p.val.1, p.val.2}, tpSize (F := F) s B (Sum.inl a)
      = (X \ {p.val.1, p.val.2}).card * (20 * B + 1)
        + 4 * ∑ a ∈ X \ {p.val.1, p.val.2}, s a :=
    calc ∑ a ∈ X \ {p.val.1, p.val.2}, tpSize (F := F) s B (Sum.inl a)
        = ∑ a ∈ X \ {p.val.1, p.val.2}, ((20 * B + 1) + 4 * s a) :=
          Finset.sum_congr rfl fun a _ ↦ by
            simp only [tpSize_reg]
            omega
      _ = (X \ {p.val.1, p.val.2}).card * (20 * B + 1)
            + 4 * ∑ a ∈ X \ {p.val.1, p.val.2}, s a := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            Finset.mul_sum]
  rw [hexp, hdiff]
  simp only [tpSize_pair_true, tpBound]
  omega

/-- The constructed partition, as a family: each 4-set contributes its two
halves, and each unused pool entry its matched pair plus a filler. -/
def tpFamily {parts : Finset (Finset α)} (pick : {X // X ∈ parts} → TpPair α)
    {U : Finset (TpPair α)} (e : ↥U → Fin F) :
    ({X : Finset α // X ∈ parts} × Bool) ⊕ ↥U → Finset (TpElt α F)
  | .inl (X, false) => tpPartLo (pick X)
  | .inl (X, true) => tpPartHi X.val (pick X)
  | .inr u => tpPartFill u.val (e u)

@[simp] theorem tpFamily_lo {parts : Finset (Finset α)}
    (pick : {X // X ∈ parts} → TpPair α) {U : Finset (TpPair α)}
    (e : ↥U → Fin F) (X : {X : Finset α // X ∈ parts}) :
    tpFamily pick e (.inl (X, false)) = tpPartLo (pick X) := rfl

@[simp] theorem tpFamily_hi {parts : Finset (Finset α)}
    (pick : {X // X ∈ parts} → TpPair α) {U : Finset (TpPair α)}
    (e : ↥U → Fin F) (X : {X : Finset α // X ∈ parts}) :
    tpFamily pick e (.inl (X, true)) = tpPartHi X.val (pick X) := rfl

@[simp] theorem tpFamily_fill {parts : Finset (Finset α)}
    (pick : {X // X ∈ parts} → TpPair α) {U : Finset (TpPair α)}
    (e : ↥U → Fin F) (u : ↥U) :
    tpFamily (F := F) pick e (.inr u) = tpPartFill u.val (e u) := rfl

end Shapes

/-! ## A 4-partition becomes a 3-partition -/

section Forward

variable {α : Type} [Fintype α] [DecidableEq α] {F : ℕ}

/-- **The forward direction** of Garey–Johnson's Theorem 4.4: split each
4-set in two, and give the two halves the two elements of one matched pair —
their sizes are complementary exactly because the 4-set totals `B`. Every
pool entry left over is a part of its own, together with a filler. -/
theorem exists_tpPartition_of_isSizedPartition (s : α → ℕ) {B : ℕ}
    (hs : ∀ a, 3 * s a < B) {parts : Finset (Finset α)}
    (h : IsSizedPartition s 4 B parts)
    (hF : F + parts.card = Fintype.card (TpPair α)) :
    ∃ π : Finset (Finset (TpElt α F)),
      IsSizedPartition (tpSize s B) 3 (tpBound B) π := by
  classical
  -- a pool entry inside each 4-set
  have hpick : ∀ X : {X : Finset α // X ∈ parts},
      ∃ p : TpPair α, p.val.1 ∈ X.val ∧ p.val.2 ∈ X.val := by
    rintro ⟨X, hX⟩
    obtain ⟨hc, -⟩ := h.2 X hX
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
    exact ⟨⟨(a, b), hab⟩, ha, hb⟩
  choose pick hpick1 hpick2 using hpick
  have hpickinj : Function.Injective pick := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ hxy
    have hx1 := hpick1 ⟨X, hX⟩
    have hy1 := hpick1 ⟨Y, hY⟩
    rw [hxy] at hx1
    exact Subtype.ext (h.eq_of_mem hX hY hx1 hy1)
  -- the unused pool entries, in bijection with the fillers
  have hUsedCard : (Finset.univ.image pick).card = parts.card := by
    rw [Finset.card_image_of_injective _ hpickinj, Finset.card_univ,
      Fintype.card_coe]
  have hUnusedCard : (Finset.univ \ Finset.univ.image pick).card = F := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      hUsedCard]
    omega
  have hcardU : Fintype.card ↥(Finset.univ \ Finset.univ.image pick) = F := by
    rw [Fintype.card_coe, hUnusedCard]
  obtain ⟨e⟩ : Nonempty (↥(Finset.univ \ Finset.univ.image pick) ≃ Fin F) :=
    ⟨Fintype.equivFinOfCardEq hcardU⟩
  refine ⟨Finset.univ.image (tpFamily (F := F) pick (fun u ↦ e u)),
    isSizedPartition_image _ _ 3 (tpBound B) ?_ ?_ ?_⟩
  · -- every constructed element lies in exactly one part
    intro x
    rcases x with a | ⟨p, b⟩ | k
    · -- a regular element: its 4-set, and which half of it
      obtain ⟨X, ⟨hX, haX⟩, huniqX⟩ := h.1 a
      have hother : ∀ (Y : {X : Finset α // X ∈ parts}) (c : Bool),
          (Sum.inl a : TpElt α F)
              ∈ tpFamily pick (fun u ↦ e u) (Sum.inl (Y, c)) →
            Y = ⟨X, hX⟩ := by
        rintro ⟨Y, hY⟩ c hmem
        refine Subtype.ext (huniqX Y ⟨hY, ?_⟩)
        cases c
        · simp only [tpFamily_lo, mem_tpPartLo_inl] at hmem
          rcases hmem with rfl | rfl
          · exact hpick1 ⟨Y, hY⟩
          · exact hpick2 ⟨Y, hY⟩
        · simp only [tpFamily_hi, mem_tpPartHi_inl] at hmem
          exact hmem.1
      by_cases hlo : a = (pick ⟨X, hX⟩).val.1 ∨ a = (pick ⟨X, hX⟩).val.2
      · refine ⟨Sum.inl (⟨X, hX⟩, false), by simpa using hlo, ?_⟩
        rintro (⟨Y, c⟩ | u) hmem
        · obtain rfl := hother Y c hmem
          cases c
          · rfl
          · simp only [tpFamily_hi, mem_tpPartHi_inl] at hmem
            exact absurd hlo (by tauto)
        · simp only [tpFamily_fill, mem_tpPartFill_inl] at hmem
      · refine ⟨Sum.inl (⟨X, hX⟩, true), ?_, ?_⟩
        · simp only [tpFamily_hi, mem_tpPartHi_inl]
          exact ⟨haX, fun hc ↦ hlo (Or.inl hc), fun hc ↦ hlo (Or.inr hc)⟩
        · rintro (⟨Y, c⟩ | u) hmem
          · obtain rfl := hother Y c hmem
            cases c
            · simp only [tpFamily_lo, mem_tpPartLo_inl] at hmem
              exact absurd hmem hlo
            · rfl
          · simp only [tpFamily_fill, mem_tpPartFill_inl] at hmem
    · -- a pairing element: used by a 4-set, or left over for a filler part
      by_cases hp : p ∈ Finset.univ.image pick
      · obtain ⟨X, -, hpX⟩ := Finset.mem_image.mp hp
        refine ⟨Sum.inl (X, b), ?_, ?_⟩
        · cases b
          · simp [hpX]
          · simp [hpX]
        · rintro (⟨Y, c⟩ | u) hmem
          · have hq : (p, b) = (pick Y, c) := by
              cases c
              · simpa using hmem
              · simpa using hmem
            obtain ⟨hpp, rfl⟩ := Prod.ext_iff.mp hq
            rw [hpickinj (hpX.trans hpp)]
          · exfalso
            have hu : (p, b) = (u.val, false) ∨ (p, b) = (u.val, true) := by
              simpa [tpFamily] using hmem
            have hup : u.val = p := by
              rcases hu with hu | hu <;> exact ((Prod.ext_iff.mp hu).1).symm
            exact (Finset.mem_sdiff.mp u.property).2 (hup ▸ hp)
      · have hpU : p ∈ Finset.univ \ Finset.univ.image pick :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp⟩
        refine ⟨Sum.inr ⟨p, hpU⟩, ?_, ?_⟩
        · cases b
          · simp
          · simp
        · rintro (⟨Y, c⟩ | u) hmem
          · exfalso
            have hq : (p, b) = (pick Y, c) := by
              cases c
              · simpa using hmem
              · simpa using hmem
            exact hp (Finset.mem_image.mpr
              ⟨Y, Finset.mem_univ _, ((Prod.ext_iff.mp hq).1).symm⟩)
          · refine congrArg Sum.inr (Subtype.ext ?_)
            have hu : (p, b) = (u.val, false) ∨ (p, b) = (u.val, true) := by
              simpa [tpFamily] using hmem
            rcases hu with hu | hu <;> exact ((Prod.ext_iff.mp hu).1).symm
    · -- a filler: its own part
      refine ⟨Sum.inr (e.symm k), ?_, ?_⟩
      · simp only [tpFamily_fill, mem_tpPartFill_fill, Equiv.apply_symm_apply]
      · rintro (⟨Y, c⟩ | u) hmem
        · exfalso
          cases c
          · simp at hmem
          · simp at hmem
        · refine congrArg Sum.inr ?_
          have hk : k = e u := by simpa [tpFamily] using hmem
          rw [hk, Equiv.symm_apply_apply]
  · -- every part has three elements
    rintro (⟨X, b⟩ | u)
    · cases b
      · exact tpPartLo_card _
      · exact tpPartHi_card (h.2 X.val X.property).1 (hpick1 X) (hpick2 X)
    · exact tpPartFill_card _ _
  · -- and totals the bound
    rintro (⟨X, b⟩ | u)
    · cases b
      · exact tpPartLo_sum s hs _
      · exact tpPartHi_sum s hs (h.2 X.val X.property).1 (hpick1 X) (hpick2 X)
          (h.2 X.val X.property).2
    · exact tpPartFill_sum s hs _ _

end Forward

/-! ## A 3-partition becomes a 4-partition -/

section Backward

variable {α : Type} [Finite α] {F : ℕ}

/-- **The backward direction**: from a 3-partition of the constructed
instance back to a 4-partition of the source. The regular parts pair up
because the pairing elements they use still have complementary-value
multiplicities — the pool splits into matched pairs, and so do the pairing
elements sitting in filler parts. -/
theorem exists_isSizedPartition_of_tpPartition (s : α → ℕ) {B : ℕ}
    (hs : ∀ a, 3 * s a < B) {π : Finset (Finset (TpElt α F))}
    (h3 : IsSizedPartition (tpSize s B) 3 (tpBound B) π) :
    ∃ parts : Finset (Finset α), IsSizedPartition s 4 B parts := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- every index sits in a part with one other index and one pairing element
  have hreg : ∀ a : α, ∃ (b : α) (q : TpPair α × Bool), a ≠ b ∧
      ({Sum.inl a, Sum.inl b, Sum.inr (Sum.inl q)} : Finset (TpElt α F)) ∈ π ∧
        tpBeta (F := F) s B (Sum.inr (Sum.inl q)) = s a + s b := by
    intro a
    obtain ⟨P, ⟨hP, haP⟩, -⟩ := h3.1 (Sum.inl a)
    obtain ⟨hcard, hsum⟩ := h3.2 P hP
    obtain ⟨b, q, hab, hPeq, hbeta⟩ := tp_part_of_mem_reg s hs hcard hsum haP
    exact ⟨b, q, hab, hPeq ▸ hP, hbeta⟩
  choose partner pe hpne hpπ hpbeta using hreg
  -- a pairing element determines its part's two indices
  have hpe_eq : ∀ a c : α, pe c = pe a → c = a ∨ c = partner a := by
    intro a c hac
    have heq := h3.eq_of_mem (a := Sum.inr (Sum.inl (pe c))) (hpπ c) (hpπ a)
      (by simp) (by rw [hac]; simp)
    have hmem : (Sum.inl c : TpElt α F)
        ∈ ({Sum.inl a, Sum.inl (partner a), Sum.inr (Sum.inl (pe a))} :
          Finset (TpElt α F)) := heq ▸ (by simp)
    simpa using hmem
  -- the partner relation is an involution, and shares the pairing element
  have hpartner : ∀ a : α, pe (partner a) = pe a ∧ partner (partner a) = a := by
    intro a
    have heq := h3.eq_of_mem (a := Sum.inl (partner a)) (hpπ (partner a))
      (hpπ a) (by simp) (by simp)
    have h1 : (Sum.inr (Sum.inl (pe (partner a))) : TpElt α F)
        ∈ ({Sum.inl a, Sum.inl (partner a), Sum.inr (Sum.inl (pe a))} :
          Finset (TpElt α F)) := heq ▸ (by simp)
    have h2 : (Sum.inl (partner (partner a)) : TpElt α F)
        ∈ ({Sum.inl a, Sum.inl (partner a), Sum.inr (Sum.inl (pe a))} :
          Finset (TpElt α F)) := heq ▸ (by simp)
    refine ⟨by simpa using h1, ?_⟩
    have h3' : partner (partner a) = a ∨ partner (partner a) = partner a := by
      simpa using h2
    rcases h3' with h | h
    · exact h
    · exact absurd h (hpne (partner a)).symm
  -- the pairing elements of filler parts, and their partners there
  have hfill : ∀ q : TpPair α × Bool, ∃ q' : TpPair α × Bool,
      (¬ ∃ a, pe a = q) → (q' ≠ q ∧
        tpBeta (F := F) s B (Sum.inr (Sum.inl q))
            + tpBeta (F := F) s B (Sum.inr (Sum.inl q')) = B ∧
          ∃ k : Fin F, ({Sum.inr (Sum.inl q), Sum.inr (Sum.inl q'),
            Sum.inr (Sum.inr k)} : Finset (TpElt α F)) ∈ π) := by
    intro q
    by_cases hq : ∃ a, pe a = q
    · exact ⟨q, fun h ↦ absurd hq h⟩
    · obtain ⟨P, ⟨hP, hqP⟩, -⟩ := h3.1 (Sum.inr (Sum.inl q))
      obtain ⟨hcard, hsum⟩ := h3.2 P hP
      rcases tp_part_of_mem_pair s hs hcard hsum hqP with
        ⟨a, b, hab, hPeq, -⟩ | ⟨q', k, hPeq, hbeta⟩
      · exfalso
        refine hq ⟨a, ?_⟩
        have heq := h3.eq_of_mem (a := Sum.inl a) (hpπ a) hP (by simp)
          (by rw [hPeq]; simp)
        have hmem : (Sum.inr (Sum.inl (pe a)) : TpElt α F) ∈ P :=
          heq ▸ (by simp)
        rw [hPeq] at hmem
        simpa using hmem
      · refine ⟨q', fun _ ↦ ⟨?_, hbeta, k, hPeq ▸ hP⟩⟩
        rintro rfl
        rw [hPeq] at hcard
        rw [Finset.insert_idem] at hcard
        rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
          at hcard
        omega
  choose J hJ using hfill
  -- the value function on pool elements, and the two involutions on it
  set g : (TpPair α × Bool) → ℕ :=
    fun q ↦ tpBeta (F := F) s B (Sum.inr (Sum.inl q)) with hgdef
  have hgapp : ∀ q, g q = tpBeta (F := F) s B (Sum.inr (Sum.inl q)) :=
    fun _ ↦ rfl
  have hgle : ∀ q, g q ≤ B := by
    rintro ⟨p, b⟩
    have := pairVal_lt s hs p
    cases b <;> simp only [hgdef, tpBeta_pair_false, tpBeta_pair_true] <;> omega
  have hflipne : ∀ q : TpPair α × Bool, (q.1, !q.2) ≠ q := by
    intro q hc
    have h2 : (!q.2) = q.2 := congrArg Prod.snd hc
    cases hq2 : q.2 <;> rw [hq2] at h2 <;> simp at h2
  have hflip : ∀ q : TpPair α × Bool, g q + g (q.1, !q.2) = B := by
    rintro ⟨p, b⟩
    have := pairVal_lt s hs p
    cases b <;>
      simp only [hgdef, tpBeta_pair_false, tpBeta_pair_true, Bool.not_false,
        Bool.not_true] <;> omega
  -- the filler-part involution is one, and stays outside the regular pool
  have hJmem : ∀ q, (¬ ∃ a, pe a = q) → ¬ ∃ a, pe a = J q := by
    rintro q hq ⟨a, ha⟩
    obtain ⟨-, -, k, hk⟩ := hJ q hq
    have heq := h3.eq_of_mem (a := Sum.inr (Sum.inl (J q))) (hpπ a) hk
      (by rw [← ha]; simp) (by simp)
    have hmem : (Sum.inl a : TpElt α F)
        ∈ ({Sum.inr (Sum.inl q), Sum.inr (Sum.inl (J q)),
          Sum.inr (Sum.inr k)} : Finset (TpElt α F)) := heq ▸ (by simp)
    simp at hmem
  have hJinv : ∀ q, (¬ ∃ a, pe a = q) → J (J q) = q := by
    intro q hq
    obtain ⟨hne, -, k, hk⟩ := hJ q hq
    obtain ⟨hne', -, k', hk'⟩ := hJ (J q) (hJmem q hq)
    have heq := h3.eq_of_mem (a := Sum.inr (Sum.inl (J q))) hk' hk (by simp)
      (by simp)
    have hmem : (Sum.inr (Sum.inl (J (J q))) : TpElt α F)
        ∈ ({Sum.inr (Sum.inl q), Sum.inr (Sum.inl (J q)),
          Sum.inr (Sum.inr k)} : Finset (TpElt α F)) := heq ▸ (by simp)
    have : J (J q) = q ∨ J (J q) = J q := by simpa using hmem
    rcases this with h | h
    · exact h
    · exact absurd h hne'
  -- the multiplicity count, and the pairing it yields
  set S : Finset (TpPair α × Bool) :=
    Finset.univ.filter (fun q ↦ ∃ a, pe a = q) with hSdef
  have hsplit : ∀ v : ℕ,
      (Finset.univ.filter fun q ↦ g q = v).card
        = (S.filter fun q ↦ g q = v).card
          + ((Finset.univ.filter fun q ↦ ¬ ∃ a, pe a = q).filter
              fun q ↦ g q = v).card := by
    intro v
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun q : TpPair α × Bool ↦ g q = v)
      (p := fun q ↦ ∃ a, pe a = q)
    have e1 : (Finset.univ.filter fun q : TpPair α × Bool ↦ g q = v).filter
        (fun q ↦ ∃ a, pe a = q) = S.filter (fun q ↦ g q = v) := by
      rw [hSdef]
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have e2 : (Finset.univ.filter fun q : TpPair α × Bool ↦ g q = v).filter
        (fun q ↦ ¬ ∃ a, pe a = q)
        = (Finset.univ.filter fun q ↦ ¬ ∃ a, pe a = q).filter
            (fun q ↦ g q = v) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [e1, e2] at h
    omega
  have hsymm : ∀ v ≤ B, (S.filter fun q ↦ g q = v).card
      = (S.filter fun q ↦ g q = B - v).card := by
    intro v hv
    have huniv : (Finset.univ.filter fun q : TpPair α × Bool ↦ g q = v).card
        = (Finset.univ.filter fun q ↦ g q = B - v).card := by
      refine card_filter_eq_of_involution _ _ _ (fun q ↦ (q.1, !q.2))
        (fun _ _ ↦ Finset.mem_univ _) (fun q _ ↦ by simp) ?_ ?_
      · intro q _ hq
        have := hflip q
        omega
      · intro q _ hq
        have := hflip q
        have := hgle q
        omega
    have hfillc : ((Finset.univ.filter fun q : TpPair α × Bool ↦
          ¬ ∃ a, pe a = q).filter fun q ↦ g q = v).card
        = ((Finset.univ.filter fun q : TpPair α × Bool ↦
          ¬ ∃ a, pe a = q).filter fun q ↦ g q = B - v).card := by
      refine card_filter_eq_of_involution _ _ _ J ?_ ?_ ?_ ?_
      · intro q hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hJmem q (Finset.mem_filter.mp hq).2⟩
      · exact fun q hq ↦ hJinv q (Finset.mem_filter.mp hq).2
      · intro q hq hgq
        obtain ⟨-, hsum, -⟩ := hJ q (Finset.mem_filter.mp hq).2
        rw [← hgapp q, ← hgapp (J q)] at hsum
        omega
      · intro q hq hgq
        obtain ⟨-, hsum, -⟩ := hJ q (Finset.mem_filter.mp hq).2
        rw [← hgapp q, ← hgapp (J q)] at hsum
        have := hgle q
        omega
    have h1 := hsplit v
    have h2 := hsplit (B - v)
    omega
  have heven : ∀ v, 2 * v = B → Even (S.filter fun q ↦ g q = v).card := by
    intro v hv
    have huniv : Even (Finset.univ.filter fun q : TpPair α × Bool ↦
        g q = v).card := by
      refine even_card_of_involution (fun q ↦ (q.1, !q.2)) _
        (fun q hq ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        (fun q _ ↦ hflipne q) (fun q _ ↦ by simp)
      have hgq := (Finset.mem_filter.mp hq).2
      have := hflip q
      omega
    have hfille : Even ((Finset.univ.filter fun q : TpPair α × Bool ↦
        ¬ ∃ a, pe a = q).filter fun q ↦ g q = v).card := by
      refine even_card_of_involution J _ (fun q hq ↦ ?_) (fun q hq ↦ ?_)
        (fun q hq ↦ hJinv q (Finset.mem_filter.mp
          (Finset.mem_filter.mp hq).1).2)
      · obtain ⟨hq1, hgq⟩ := Finset.mem_filter.mp hq
        obtain ⟨-, hsum, -⟩ := hJ q (Finset.mem_filter.mp hq1).2
        rw [← hgapp q, ← hgapp (J q)] at hsum
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hJmem q (Finset.mem_filter.mp hq1).2⟩, by omega⟩
      · exact (hJ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2).1
    have h1 := hsplit v
    rw [Nat.even_iff] at huniv hfille ⊢
    omega
  obtain ⟨pairs, hcov, hpairs⟩ := exists_pairs_of_card_symm g B S
    (fun q _ ↦ hgle q) hsymm heven
  -- the 4-sets: the indices of the two regular parts a pair joins
  set regsOf : (TpPair α × Bool) → Finset α :=
    fun q ↦ Finset.univ.filter (fun a ↦ pe a = q) with hregdef
  have hregsOf : ∀ a : α, regsOf (pe a) = {a, partner a} := by
    intro a
    ext c
    simp only [hregdef, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact hpe_eq a c
    · rintro (rfl | rfl)
      · rfl
      · exact (hpartner a).1
  have hregsOf_card : ∀ a : α, (regsOf (pe a)).card = 2 := by
    intro a
    rw [hregsOf a, Finset.card_insert_of_notMem (by simpa using hpne a),
      Finset.card_singleton]
  have hregsOf_sum : ∀ a : α, ∑ c ∈ regsOf (pe a), s c = g (pe a) := by
    intro a
    rw [hregsOf a, Finset.sum_insert (by simpa using hpne a),
      Finset.sum_singleton, hgapp]
    exact (hpbeta a).symm
  have hregsOf_disj : ∀ q q' : TpPair α × Bool, q ≠ q' →
      Disjoint (regsOf q) (regsOf q') := by
    intro q q' hne
    refine Finset.disjoint_left.mpr fun a ha ha' ↦ hne ?_
    have h1 : pe a = q := (Finset.mem_filter.mp ha).2
    have h2 : pe a = q' := (Finset.mem_filter.mp ha').2
    rw [← h1, h2]
  refine ⟨pairs.image fun P ↦ P.biUnion regsOf, ?_, ?_⟩
  · -- every index lies in exactly one 4-set
    intro a
    have haS : pe a ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, rfl⟩⟩
    obtain ⟨P, ⟨hP, hpeP⟩, huniq⟩ := hcov (pe a) haS
    refine ⟨P.biUnion regsOf, ⟨Finset.mem_image_of_mem _ hP, ?_⟩, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨pe a, hpeP, by
        rw [hregsOf a]; simp⟩
    · rintro X ⟨hX, haX⟩
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨q, hqQ, haq⟩ := Finset.mem_biUnion.mp haX
      have : pe a = q := (Finset.mem_filter.mp haq).2
      rw [huniq Q ⟨hQ, this ▸ hqQ⟩]
  · -- and every 4-set has four indices totalling `B`
    intro X hX
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨hPS, hPcard, hPsum⟩ := hpairs P hP
    have hmemS : ∀ q ∈ P, ∃ a, pe a = q := fun q hq ↦
      (Finset.mem_filter.mp (hPS hq)).2
    have hcard2 : ∀ q ∈ P, (regsOf q).card = 2 := by
      intro q hq
      obtain ⟨a, rfl⟩ := hmemS q hq
      exact hregsOf_card a
    have hsum2 : ∀ q ∈ P, ∑ c ∈ regsOf q, s c = g q := by
      intro q hq
      obtain ⟨a, rfl⟩ := hmemS q hq
      exact hregsOf_sum a
    constructor
    · rw [Finset.card_biUnion (fun x _ y _ hxy ↦ hregsOf_disj x y hxy),
        Finset.sum_congr rfl hcard2, Finset.sum_const, hPcard, smul_eq_mul]
    · rw [Finset.sum_biUnion (fun x _ y _ hxy ↦ hregsOf_disj x y hxy),
        Finset.sum_congr rfl hsum2, hPsum]

end Backward

/-! ## The window, and the total -/

section Window

variable {α : Type} {F : ℕ}

/-- Every constructed size lies strictly between `B'/4` and `B'/2`. A filler
is the one kind that carries no source number, so its bound needs to know
that `B` is positive — which it is as soon as any element exists at all. -/
theorem tp_window (s : α → ℕ) {B : ℕ} (hs : ∀ a, 3 * s a < B)
    (hB : 0 < F → 0 < B) (x : TpElt α F) :
    tpBound B < 4 * tpSize s B x ∧ 2 * tpSize s B x < tpBound B := by
  match x with
  | .inl a =>
    have := hs a
    simp only [tpSize_reg, tpBound]
    omega
  | .inr (.inl (p, false)) =>
    have h := pairVal_lt s hs p
    have := hs p.val.1
    simp only [tpSize_pair_false, tpBound]
    omega
  | .inr (.inl (p, true)) =>
    have h := pairVal_lt s hs p
    have := hs p.val.1
    simp only [tpSize_pair_true, tpBound]
    omega
  | .inr (.inr k) =>
    have := hB (Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt)
    simp only [tpSize_filler, tpBound]
    omega

variable [Fintype α] [DecidableEq α]

/-- The constructed sizes total `(m' · B')/3` where `m'` is the number of
parts — the second half of the window, and the arithmetic identity behind the
count of fillers. -/
theorem tp_total_sum (s : α → ℕ) {B n : ℕ} (hs : ∀ a, 3 * s a < B)
    (hcard : Fintype.card α = 4 * n) (hF : F + n = Fintype.card (TpPair α))
    (hsum : 4 * ∑ a, s a = Fintype.card α * B) :
    3 * ∑ x : TpElt α F, tpSize s B x
      = Fintype.card (TpElt α F) * tpBound B := by
  have hcardE : Fintype.card (TpElt α F)
      = Fintype.card α + 2 * Fintype.card (TpPair α) + F := by
    simp only [TpElt, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_fin]
    ring
  have hsumE : ∑ x : TpElt α F, tpSize s B x
      = (∑ a : α, tpSize (F := F) s B (Sum.inl a))
        + ((∑ q : TpPair α × Bool, tpSize (F := F) s B (Sum.inr (Sum.inl q)))
          + ∑ k : Fin F, tpSize (F := F) s B (Sum.inr (Sum.inr k))) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ a : α, tpSize (F := F) s B (Sum.inl a)
      = Fintype.card α * (20 * B + 1) + 4 * ∑ a, s a := by
    calc ∑ a : α, tpSize (F := F) s B (Sum.inl a)
        = ∑ a : α, ((20 * B + 1) + 4 * s a) :=
          Finset.sum_congr rfl fun a _ ↦ by simp only [tpSize_reg]; omega
      _ = Fintype.card α * (20 * B + 1) + 4 * ∑ a, s a := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            smul_eq_mul, Finset.mul_sum]
  have h2 : ∑ q : TpPair α × Bool, tpSize (F := F) s B (Sum.inr (Sum.inl q))
      = Fintype.card (TpPair α) * (44 * B + 4) := by
    rw [Fintype.sum_prod_type]
    have hb : ∀ p : TpPair α,
        ∑ b : Bool, tpSize (F := F) s B (Sum.inr (Sum.inl (p, b)))
          = 44 * B + 4 := by
      intro p
      rw [Fintype.sum_bool]
      have := tpSize_matched (F := F) s hs p
      omega
    rw [Finset.sum_congr rfl fun p _ ↦ hb p, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have h3 : ∑ _k : Fin F, tpSize (F := F) s B (Sum.inr (Sum.inr _k))
      = F * (20 * B) := by
    simp only [tpSize_filler, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hss : ∑ a, s a = n * B := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < 4 by omega) ?_
    rw [hsum, hcard]
    ring
  rw [hsumE, h1, h2, h3, hcardE, hcard, ← hF, hss, tpBound]
  ring

/-- With `4n` indices the pool has at least `n` entries: the pairs
`(4j, 4j+1)` are distinct, one per part. Together with `card_le_card_tpPair`
this is what makes the filler count `|pool| − n` a subtraction that never
truncates. -/
theorem le_card_tpPair {m n : ℕ} (hm : m = 4 * n) :
    n ≤ Fintype.card (TpPair (Fin m)) := by
  have hmap : Function.Injective
      (fun j : Fin n ↦ (⟨(⟨4 * j.val, by omega⟩, ⟨4 * j.val + 1, by omega⟩),
        by simp [Fin.ext_iff]⟩ : TpPair (Fin m))) := by
    intro a b hab
    have h := congrArg (fun p ↦ (p.val.1 : ℕ)) hab
    simp only at h
    exact Fin.ext (by omega)
  have h := Fintype.card_le_of_injective _ hmap
  rwa [Fintype.card_fin] at h

/-- A 4-partition injects into the pool of index pairs: each part offers one,
and distinct parts offer distinct ones. This is what makes the filler count
`|pool| − |parts|` honest. -/
theorem card_le_card_tpPair (s : α → ℕ) {B : ℕ} {parts : Finset (Finset α)}
    (h : IsSizedPartition s 4 B parts) :
    parts.card ≤ Fintype.card (TpPair α) := by
  classical
  have hpick : ∀ X : {X : Finset α // X ∈ parts},
      ∃ p : TpPair α, p.val.1 ∈ X.val ∧ p.val.2 ∈ X.val := by
    rintro ⟨X, hX⟩
    obtain ⟨hc, -⟩ := h.2 X hX
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
    exact ⟨⟨(a, b), hab⟩, ha, hb⟩
  choose pick hpick1 hpick2 using hpick
  have hinj : Function.Injective pick := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ hxy
    have hx1 := hpick1 ⟨X, hX⟩
    have hy1 := hpick1 ⟨Y, hY⟩
    rw [hxy] at hx1
    exact Subtype.ext (h.eq_of_mem hX hY hx1 hy1)
  have hle := Fintype.card_le_of_injective pick hinj
  rwa [Fintype.card_coe] at hle

end Window

/-! ## The reduction -/

section Glue

/-- The number of fillers a source instance needs: one for every pool entry
that no 4-set can claim. -/
def tpFillers (x : NumberTargetInstance) : ℕ :=
  Fintype.card (TpPair (Fin x.nums.length)) - x.nums.length / 4

/-- The constructed number list: the sizes of the tagged elements, listed
along a numbering of them. -/
noncomputable def tpNums (x : NumberTargetInstance) : List ℕ :=
  List.ofFn fun j : Fin (Fintype.card (TpElt (Fin x.nums.length)
      (tpFillers x))) ↦
    tpSize (fun i : Fin x.nums.length ↦ x.nums[i.1]) x.target
      ((Fintype.equivFin (TpElt (Fin x.nums.length) (tpFillers x))).symm j)

/-- The branch condition: the Garey–Johnson window on the source, and a
number count divisible by four — without which the source has no 4-partition
at all, and with which the filler count comes out right. -/
def ThreePartitionGood (x : NumberTargetInstance) : Prop :=
  FourPartitionWindow x ∧ 4 ∣ x.nums.length

instance : DecidablePred ThreePartitionGood := fun x ↦ by
  unfold ThreePartitionGood
  infer_instance

/-- The fixed no-instance for the degenerate branch: all sizes even, bound
odd — and windowed, so the branch lands inside the restriction too. -/
theorem not_threePartition_parityNo :
    ¬ THREE_PARTITION ⟨[4, 4, 4, 6, 6, 6], 15⟩ := by
  intro h
  unfold THREE_PARTITION at h
  obtain ⟨parts, hcov, hprops⟩ := h
  obtain ⟨p, ⟨hp, -⟩, -⟩ := hcov ⟨0, by decide⟩
  obtain ⟨-, hsum⟩ := hprops p hp
  have heven : (∑ i ∈ p, ([4, 4, 4, 6, 6, 6] : List ℕ)[i.1]) % 2 = 0 := by
    have hz : ∀ a ∈ ([4, 4, 4, 6, 6, 6] : List ℕ), a % 2 = 0 := by decide
    calc (∑ i ∈ p, ([4, 4, 4, 6, 6, 6] : List ℕ)[i.1]) % 2
        = (∑ i ∈ p, ([4, 4, 4, 6, 6, 6] : List ℕ)[i.1] % 2) % 2 :=
          Finset.sum_nat_mod p 2 _
      _ = (∑ _i ∈ p, 0) % 2 := congrArg (· % 2)
          (Finset.sum_congr rfl fun i _ ↦ hz _ (List.getElem_mem _))
      _ = 0 := by simp
  rw [hsum] at heven
  exact absurd heven (by decide)

/-- The instance map: the gadget when the branch condition holds, the parity
no-instance otherwise. -/
noncomputable def threePartitionInstance (x : NumberTargetInstance) :
    NumberTargetInstance :=
  if ThreePartitionGood x then ⟨tpNums x, tpBound x.target⟩
  else ⟨[4, 4, 4, 6, 6, 6], 15⟩

/-- Transport: 3-PARTITION of the emitted instance is the sized-partition
question over the tagged element type. -/
theorem threePartition_tpNums_iff (x : NumberTargetInstance) :
    THREE_PARTITION ⟨tpNums x, tpBound x.target⟩ ↔
      ∃ parts, IsSizedPartition
        (tpSize (F := tpFillers x)
          (fun i : Fin x.nums.length ↦ x.nums[i.1]) x.target) 3
        (tpBound x.target) parts := by
  unfold THREE_PARTITION tpNums
  dsimp only
  rw [exists_isSizedPartition_ofFn_iff]
  exact (exists_isSizedPartition_iff_map
    (Fintype.equivFin (TpElt (Fin x.nums.length) (tpFillers x))) _ 3 _).symm

/-- On the gadget branch, the window's size bound holds pointwise; the
positivity a filler needs comes from the pool being nonempty. -/
theorem tp_pos_of_fillers {x : NumberTargetInstance}
    (hs : ∀ i : Fin x.nums.length, 3 * x.nums[i.1] < x.target) :
    0 < tpFillers x → 0 < x.target := by
  intro hF
  have hcard : 0 < Fintype.card (TpPair (Fin x.nums.length)) := by
    unfold tpFillers at hF
    omega
  obtain ⟨p⟩ := Fintype.card_pos_iff.mp hcard
  have := hs p.val.1
  omega

/-- Correctness of the instance map. -/
theorem fourPartition_iff_threePartitionInstance (x : NumberTargetInstance) :
    (FOUR_PARTITION.restrict FourPartitionWindow) x ↔
      THREE_PARTITION (threePartitionInstance x) := by
  unfold threePartitionInstance
  by_cases hgood : ThreePartitionGood x
  · rw [if_pos hgood, threePartition_tpNums_iff]
    obtain ⟨hwin, n, hn⟩ := hgood
    have hs : ∀ i : Fin x.nums.length, 3 * x.nums[i.1] < x.target := fun i ↦
      (hwin.1 _ (List.getElem_mem i.isLt)).2
    have hcardα : Fintype.card (Fin x.nums.length) = 4 * n := by
      rw [Fintype.card_fin]; omega
    constructor
    · rintro ⟨-, parts, hparts⟩
      have hpc : parts.card = n := by
        have := hparts.card_univ
        rw [hcardα] at this
        omega
      have hle := card_le_card_tpPair (fun i : Fin x.nums.length ↦ x.nums[i.1]) hparts
      refine exists_tpPartition_of_isSizedPartition (F := tpFillers x)
        (fun i : Fin x.nums.length ↦ x.nums[i.1]) hs hparts ?_
      unfold tpFillers
      rw [hpc] at hle ⊢
      have hn4 : x.nums.length / 4 = n := by omega
      rw [hn4]
      omega
    · rintro ⟨parts, hparts⟩
      exact ⟨hwin, exists_isSizedPartition_of_tpPartition
        (fun i : Fin x.nums.length ↦ x.nums[i.1]) hs hparts⟩
  · rw [if_neg hgood]
    refine iff_of_false ?_ not_threePartition_parityNo
    rintro ⟨hwin, parts, hparts⟩
    refine hgood ⟨hwin, ?_⟩
    have := hparts.card_univ
    rw [Fintype.card_fin] at this
    exact ⟨parts.card, by omega⟩

/-- The instance map lands inside the Garey–Johnson window on every input. -/
theorem threePartitionWindow_threePartitionInstance
    (x : NumberTargetInstance) :
    ThreePartitionWindow (threePartitionInstance x) := by
  unfold threePartitionInstance
  by_cases hgood : ThreePartitionGood x
  · rw [if_pos hgood]
    obtain ⟨hwin, n, hn⟩ := hgood
    have hs : ∀ i : Fin x.nums.length, 3 * x.nums[i.1] < x.target := fun i ↦
      (hwin.1 _ (List.getElem_mem i.isLt)).2
    have hcardα : Fintype.card (Fin x.nums.length) = 4 * n := by
      rw [Fintype.card_fin]; omega
    have hsum : 4 * ∑ i : Fin x.nums.length, x.nums[i.1]
        = Fintype.card (Fin x.nums.length) * x.target := by
      rw [Fintype.card_fin, ← hwin.2]
      refine congrArg (4 * ·) ?_
      conv_rhs => rw [← List.ofFn_getElem (xs := x.nums)]
      exact (List.sum_ofFn).symm
    have hFn : tpFillers x + n = Fintype.card (TpPair (Fin x.nums.length)) := by
      unfold tpFillers
      have hn4 : x.nums.length / 4 = n := by omega
      rw [hn4]
      have hle : n ≤ Fintype.card (TpPair (Fin x.nums.length)) :=
        le_card_tpPair (by omega)
      omega
    unfold ThreePartitionWindow
    dsimp only
    constructor
    · intro a ha
      unfold tpNums at ha
      rw [List.mem_ofFn] at ha
      obtain ⟨j, rfl⟩ := ha
      exact tp_window (fun i : Fin x.nums.length ↦ x.nums[i.1]) hs (tp_pos_of_fillers hs) _
    · unfold tpNums
      rw [List.sum_ofFn, List.length_ofFn]
      have htot := tp_total_sum (F := tpFillers x) (fun i : Fin x.nums.length ↦ x.nums[i.1]) hs
        hcardα hFn hsum
      rw [← htot, Equiv.sum_comp
        (Fintype.equivFin (TpElt (Fin x.nums.length) (tpFillers x))).symm
        (tpSize (F := tpFillers x)
          (fun i : Fin x.nums.length ↦ x.nums[i.1]) x.target)]
  · rw [if_neg hgood]
    exact ⟨by decide, by decide⟩

/-- The reduction 4-PARTITION → 3-PARTITION, landing inside the Garey–Johnson
window: 3-PARTITION is hard even when every size lies strictly between `B/4`
and `B/2` and the sizes total `m·B`. The source is 4-PARTITION *inside its
own window*, which is exactly what the 3-dimensional-matching reduction
delivers. -/
noncomputable def fourPartitionToThreePartition :
    FOUR_PARTITION.restrict FourPartitionWindow ⟶ᵣ
      THREE_PARTITION.restrict ThreePartitionWindow :=
  Reduction.codRestrict
    ⟨threePartitionInstance, fourPartition_iff_threePartitionInstance⟩
    ThreePartitionWindow threePartitionWindow_threePartitionInstance

/-- The same map, read against the unrestricted target. -/
noncomputable def fourPartitionToThreePartitionPlain :
    FOUR_PARTITION.restrict FourPartitionWindow ⟶ᵣ THREE_PARTITION :=
  ⟨threePartitionInstance, fourPartition_iff_threePartitionInstance⟩

/-- 3-DIMENSIONAL MATCHING reduces to 3-PARTITION, by composition through
4-PARTITION — the Garey–Johnson chain, end to end. -/
noncomputable def matching3DToThreePartition :
    MATCHING_3D ⟶ᵣ THREE_PARTITION.restrict ThreePartitionWindow :=
  matching3DToFourPartition.comp fourPartitionToThreePartition

end Glue

end Hardness
