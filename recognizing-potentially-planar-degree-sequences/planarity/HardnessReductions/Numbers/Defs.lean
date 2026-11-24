import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# Shared instance type for number problems with a target

Several catalog entries ask different questions of the same Garey–Johnson
instance — a list of numbers together with one distinguished number — so they
share one instance type and one encoding (`Numbers/Encoding.lean`), the
`SetSystemInstance` discipline applied to the numbers domain:

* **SUBSET SUM** (`Numbers/SubsetSum.lean`) reads `target` as the value some
  subset of the numbers must hit;
* **3-PARTITION** and **4-PARTITION** (`Numbers/Partition3.lean`,
  `Numbers/Partition4.lean`) read `target` as the bound `B` every part of the
  partition must sum to.

The list is explicit, in keeping with the size-model discipline: every item
is represented, and duplicate entries are distinct items. Selections and
partitions are therefore formulated over *indices* into the list, never over
sublists or subsets of values.

PARTITION (`Numbers/Partition.lean`) deliberately does not share this type:
its Garey–Johnson instance is the bare list, with no distinguished number.
-/

namespace Hardness

/-- A list of numbers together with a distinguished target number — the
instance data shared by SUBSET SUM (target = the sum to hit) and by
3-PARTITION and 4-PARTITION (target = the bound each part must sum to).
Duplicate entries
of `nums` are distinct items. -/
structure NumberTargetInstance : Type where
  /-- The available numbers. -/
  nums : List ℕ
  /-- The distinguished number, read by each entry's question. -/
  target : ℕ

/-! ## Partitions into parts of a fixed size and sum

The predicate shared by 3-PARTITION (`c = 3`) and 4-PARTITION (`c = 4`),
stated over an arbitrary indexed family `f : α → ℕ` so that gadget
constructions can work with tagged index types and transport to list
positions afterwards. The cover condition is the `∃!` packaging of
"every index lies in exactly one part", as in `IsExactCover`
(`Sets/Matching3D.lean`). -/

/-- `parts` partitions the index type `α` into parts of size exactly `c`,
each of whose `f`-values sum to `B`. -/
def IsSizedPartition {α : Type} (f : α → ℕ) (c B : ℕ)
    (parts : Finset (Finset α)) : Prop :=
  (∀ a : α, ∃! p, p ∈ parts ∧ a ∈ p) ∧
    ∀ p ∈ parts, p.card = c ∧ ∑ a ∈ p, f a = B

namespace IsSizedPartition

variable {α β : Type} {f : α → ℕ} {c B : ℕ} {parts : Finset (Finset α)}

/-- Every index lies in some part. -/
theorem exists_mem (h : IsSizedPartition f c B parts) (a : α) :
    ∃ p ∈ parts, a ∈ p := by
  obtain ⟨p, ⟨hp, hap⟩, -⟩ := h.1 a
  exact ⟨p, hp, hap⟩

/-- No index lies in two parts. -/
theorem eq_of_mem (h : IsSizedPartition f c B parts) {p q : Finset α} {a : α}
    (hp : p ∈ parts) (hq : q ∈ parts) (hap : a ∈ p) (haq : a ∈ q) : p = q := by
  obtain ⟨o, -, huniq⟩ := h.1 a
  rw [huniq p ⟨hp, hap⟩, huniq q ⟨hq, haq⟩]

/-- A sized partition transports along an equivalence of index types. -/
theorem map [DecidableEq β] (e : α ≃ β) (h : IsSizedPartition f c B parts) :
    IsSizedPartition (fun b ↦ f (e.symm b)) c B
      (parts.image fun p ↦ p.map e.toEmbedding) := by
  constructor
  · intro b
    obtain ⟨p, ⟨hp, hbp⟩, huniq⟩ := h.1 (e.symm b)
    refine ⟨p.map e.toEmbedding, ⟨Finset.mem_image_of_mem _ hp,
      Finset.mem_map.mpr ⟨e.symm b, hbp, e.apply_symm_apply b⟩⟩, ?_⟩
    rintro q ⟨hq, hbq⟩
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨a, hap', hab⟩ := Finset.mem_map.mp hbq
    obtain rfl : a = e.symm b := by rw [← hab]; exact (e.symm_apply_apply a).symm
    rw [huniq p' ⟨hp', hap'⟩]
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hcard, hsum⟩ := h.2 p hp
    refine ⟨by rw [Finset.card_map, hcard], ?_⟩
    rw [Finset.sum_map, ← hsum]
    exact Finset.sum_congr rfl fun a _ ↦ by
      rw [Equiv.coe_toEmbedding, e.symm_apply_apply]

/-- Counting the index type by parts: a sized partition has exactly
`card α / c` parts. -/
theorem card_univ [Fintype α] (h : IsSizedPartition f c B parts) :
    Fintype.card α = parts.card * c := by
  classical
  have hdisj : ∀ p ∈ parts, ∀ q ∈ parts, p ≠ q → Disjoint p q := by
    intro p hp q hq hne
    refine Finset.disjoint_left.mpr fun a hap haq ↦ hne ?_
    exact h.eq_of_mem hp hq hap haq
  have hcover : parts.biUnion (fun p ↦ p) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun a ↦ ?_
    obtain ⟨p, hp, hap⟩ := h.exists_mem a
    exact Finset.mem_biUnion.mpr ⟨p, hp, hap⟩
  rw [← Finset.card_univ, ← hcover, Finset.card_biUnion hdisj]
  rw [Finset.sum_congr rfl fun p hp ↦ (h.2 p hp).1, Finset.sum_const,
    smul_eq_mul]

end IsSizedPartition

/-- Sized-partition solvability transports along an equivalence of index
types — the renaming-invariance lemma both partition entries' gadgets and
representation pairs consume. -/
theorem exists_isSizedPartition_iff_map {α β : Type} (e : α ≃ β)
    (f : α → ℕ) (c B : ℕ) :
    (∃ parts, IsSizedPartition f c B parts) ↔
      ∃ parts, IsSizedPartition (fun b ↦ f (e.symm b)) c B parts := by
  classical
  constructor
  · rintro ⟨parts, h⟩
    exact ⟨_, h.map e⟩
  · rintro ⟨parts, h⟩
    have := h.map e.symm
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at this
    exact ⟨_, this⟩

/-- Partitioning the positions of the list `List.ofFn g` is the same as
partitioning the indices of `g`: the passage from an indexed family of
numbers to its explicit listing preserves sized partitions. -/
theorem exists_isSizedPartition_ofFn_iff {n : ℕ} (g : Fin n → ℕ) (c B : ℕ) :
    (∃ parts : Finset (Finset (Fin (List.ofFn g).length)),
        IsSizedPartition (fun i ↦ (List.ofFn g)[i.1]) c B parts) ↔
      ∃ parts : Finset (Finset (Fin n)), IsSizedPartition g c B parts := by
  have hlen : (List.ofFn g).length = n := List.length_ofFn
  rw [exists_isSizedPartition_iff_map (finCongr hlen)]
  refine exists_congr fun parts ↦ ?_
  have : (fun i : Fin n ↦ (List.ofFn g)[((finCongr hlen).symm i).1]) = g := by
    funext i
    rw [List.getElem_ofFn]
    exact congrArg g (Fin.ext rfl)
  rw [this]

/-- Building a sized partition from an *indexed* family of parts: if every
index carries a part of the right size and sum, and every element lies in
exactly one of them, the family's image is a sized partition. The convenient
form for gadget constructions, whose parts come indexed by the source objects
they were built from — and note that the indexing need not be injective, since
`∃!` over indices already gives `∃!` over parts. -/
theorem isSizedPartition_image {α ι : Type} [Fintype ι]
    [DecidableEq (Finset α)] (f : ι → Finset α) (g : α → ℕ) (c B : ℕ)
    (hcover : ∀ a : α, ∃! i, a ∈ f i)
    (hcard : ∀ i, (f i).card = c) (hsum : ∀ i, ∑ a ∈ f i, g a = B) :
    IsSizedPartition g c B (Finset.univ.image f) := by
  constructor
  · intro a
    obtain ⟨i, hi, huniq⟩ := hcover a
    refine ⟨f i, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩, ?_⟩
    rintro P ⟨hP, haP⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hP
    rw [huniq j haP]
  · intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨hcard i, hsum i⟩

/-! ## Pairing a finset by complementary values

The combinatorial core of the 4-PARTITION → 3-PARTITION construction, isolated
because nothing in it is about numbers-in-parts: a finset whose value
multiplicities are symmetric under `v ↦ B - v` splits into pairs summing to
`B`. Garey–Johnson finish that construction with a repeated *exchange* of
equal-sized elements; the multiplicity count below is the same fact without
the iteration, and so without its termination argument. -/

/-- A finset carried into itself by a fixed-point-free involution has even
cardinality — the parity half of a multiplicity count. -/
theorem even_card_of_involution {T : Type*} (ι : T → T) :
    ∀ S : Finset T, (∀ x ∈ S, ι x ∈ S) → (∀ x ∈ S, ι x ≠ x) →
      (∀ x ∈ S, ι (ι x) = x) → Even S.card := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hmem hne hinv
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hix : ι x ∈ S := hmem x hx
      have hixne : ι x ≠ x := hne x hx
      have hixe : ι x ∈ S.erase x := Finset.mem_erase.mpr ⟨hixne, hix⟩
      have hsub : (S.erase x).erase (ι x) ⊂ S :=
        lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hx)
      have hmemS : ∀ y ∈ (S.erase x).erase (ι x), y ∈ S := fun y hy ↦
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
      have hstep : ∀ y ∈ (S.erase x).erase (ι x),
          ι y ∈ (S.erase x).erase (ι x) := by
        intro y hy
        have hyS := hmemS y hy
        have hy1 : y ≠ ι x := (Finset.mem_erase.mp hy).1
        have hy2 : y ≠ x := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hy)).1
        refine Finset.mem_erase.mpr ⟨fun hc ↦ ?_,
          Finset.mem_erase.mpr ⟨fun hc ↦ ?_, hmem y hyS⟩⟩
        · exact hy2 (by rw [← hinv y hyS, hc, hinv x hx])
        · exact hy1 (by rw [← hinv y hyS, hc])
      obtain ⟨c, hc⟩ := ih _ hsub hstep (fun y hy ↦ hne y (hmemS y hy))
        (fun y hy ↦ hinv y (hmemS y hy))
      refine ⟨c + 1, ?_⟩
      rw [Finset.card_erase_of_mem hixe, Finset.card_erase_of_mem hx] at hc
      have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
      have h2 : 2 ≤ S.card := by
        have := Finset.card_pos.mpr ⟨ι x, hixe⟩
        rw [Finset.card_erase_of_mem hx] at this
        omega
      omega

/-- Two filtered counts agree when an involution of the ambient finset swaps
the two predicates. -/
theorem card_filter_eq_of_involution {T : Type*} (S : Finset T)
    (p q : T → Prop) [DecidablePred p] [DecidablePred q] (ι : T → T)
    (hmem : ∀ x ∈ S, ι x ∈ S) (hinv : ∀ x ∈ S, ι (ι x) = x)
    (hpq : ∀ x ∈ S, p x → q (ι x)) (hqp : ∀ x ∈ S, q x → p (ι x)) :
    (S.filter p).card = (S.filter q).card := by
  refine Finset.card_nbij' ι ι ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hxp⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hmem x hxS, hpq x hxS hxp⟩
  · intro x hx
    obtain ⟨hxS, hxq⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hmem x hxS, hqp x hxS hxq⟩
  · exact fun x hx ↦ hinv x (Finset.mem_filter.mp hx).1
  · exact fun x hx ↦ hinv x (Finset.mem_filter.mp hx).1

/-- Removing two elements decreases each filtered count by the elements'
own contribution — the bookkeeping step of `exists_pairs_of_card_symm`. -/
theorem card_filter_erase_two {T : Type*} [DecidableEq T] (p : T → Prop)
    [DecidablePred p] {S : Finset T} {x y : T} (hx : x ∈ S) (hy : y ∈ S.erase x) :
    (S.filter p).card
      = (((S.erase x).erase y).filter p).card
        + (if p y then 1 else 0) + (if p x then 1 else 0) := by
  simp only [Finset.card_filter]
  rw [Finset.sum_erase_add _ _ hy, Finset.sum_erase_add _ _ hx]

/-- **Complementary pairing**: if, for every value `v ≤ B`, as many elements
of `S` carry the value `v` as carry `B - v`, and the self-complementary value
`B / 2` is carried an even number of times, then `S` splits into pairs whose
values sum to `B`.

The two hypotheses are exactly what a value multiset needs: outside the
self-complementary value the counts must match across the involution
`v ↦ B - v`, and at it they must be even. -/
theorem exists_pairs_of_card_symm {T : Type*} (g : T → ℕ)
    (B : ℕ) (S : Finset T) (hle : ∀ x ∈ S, g x ≤ B)
    (hsymm : ∀ v ≤ B, (S.filter fun x ↦ g x = v).card
      = (S.filter fun x ↦ g x = B - v).card)
    (heven : ∀ v, 2 * v = B → Even (S.filter fun x ↦ g x = v).card) :
    ∃ pairs : Finset (Finset T),
      (∀ x ∈ S, ∃! P, P ∈ pairs ∧ x ∈ P) ∧
        ∀ P ∈ pairs, P ⊆ S ∧ P.card = 2 ∧ ∑ x ∈ P, g x = B := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨∅, by simp, by simp⟩
    -- the partner of `x`, and the value bookkeeping its removal causes
    obtain ⟨y, hyx, hgy⟩ : ∃ y, y ∈ S.erase x ∧ g x + g y = B := by
      have hxv : x ∈ S.filter fun z ↦ g z = g x := Finset.mem_filter.mpr ⟨hx, rfl⟩
      by_cases hhalf : 2 * g x = B
      · obtain ⟨c, hc⟩ := heven (g x) hhalf
        have h2 : 2 ≤ (S.filter fun z ↦ g z = g x).card := by
          have := Finset.card_pos.mpr ⟨x, hxv⟩
          omega
        obtain ⟨y, hyf, hyne⟩ := Finset.exists_mem_ne h2 x
        obtain ⟨hyS, hyg⟩ := Finset.mem_filter.mp hyf
        exact ⟨y, Finset.mem_erase.mpr ⟨hyne, hyS⟩, by omega⟩
      · have hxle : g x ≤ B := hle x hx
        have hcard : 0 < (S.filter fun z ↦ g z = B - g x).card := by
          rw [← hsymm (g x) (hle x hx)]
          exact Finset.card_pos.mpr ⟨x, hxv⟩
        obtain ⟨y, hyf⟩ := Finset.card_pos.mp hcard
        obtain ⟨hyS, hyg⟩ := Finset.mem_filter.mp hyf
        have hne : y ≠ x := by
          intro h
          rw [h] at hyg
          omega
        exact ⟨y, Finset.mem_erase.mpr ⟨hne, hyS⟩, by omega⟩
    obtain ⟨hyne, hyS⟩ := Finset.mem_erase.mp hyx
    set S' := (S.erase x).erase y with hS'
    have hsub : S' ⊂ S :=
      lt_of_le_of_lt (Finset.erase_subset _ _)
        (Finset.erase_ssubset hx)
    have hxS' : x ∉ S' := fun h ↦
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
    have hyS' : y ∉ S' := fun h ↦ (Finset.mem_erase.mp h).1 rfl
    -- the hypotheses survive the removal
    have hle' : ∀ z ∈ S', g z ≤ B := fun z hz ↦
      hle z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
    have hsymm' : ∀ v ≤ B, (S'.filter fun z ↦ g z = v).card
        = (S'.filter fun z ↦ g z = B - v).card := by
      intro v hv
      have h1 := card_filter_erase_two (fun z ↦ g z = v) hx hyx
      have h2 := card_filter_erase_two (fun z ↦ g z = B - v) hx hyx
      rw [← hS'] at h1 h2
      have h3 := hsymm v hv
      have hxv : g x ≤ B := hle x hx
      split_ifs at h1 h2 <;> omega
    have heven' : ∀ v, 2 * v = B → Even (S'.filter fun z ↦ g z = v).card := by
      intro v hv
      have hc := heven v hv
      rw [Nat.even_iff] at hc ⊢
      have h1 := card_filter_erase_two (fun z ↦ g z = v) hx hyx
      rw [← hS'] at h1
      have hxv : g x ≤ B := hle x hx
      split_ifs at h1 <;> omega
    obtain ⟨pairs, hcov, hpair⟩ := ih S' hsub hle' hsymm' heven'
    refine ⟨insert {x, y} pairs, ?_, ?_⟩
    · intro z hz
      have hnotin : ∀ P ∈ pairs, x ∉ P ∧ y ∉ P := fun P hP ↦
        ⟨fun h ↦ hxS' ((hpair P hP).1 h), fun h ↦ hyS' ((hpair P hP).1 h)⟩
      by_cases hzxy : z = x ∨ z = y
      · refine ⟨{x, y}, ⟨Finset.mem_insert_self _ _, ?_⟩, ?_⟩
        · rcases hzxy with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · rintro P ⟨hP, hzP⟩
          rcases Finset.mem_insert.mp hP with rfl | hP'
          · rfl
          · exact absurd hzP (by
              rcases hzxy with rfl | rfl
              · exact (hnotin P hP').1
              · exact (hnotin P hP').2)
      · push Not at hzxy
        have hzS' : z ∈ S' :=
          Finset.mem_erase.mpr ⟨hzxy.2, Finset.mem_erase.mpr ⟨hzxy.1, hz⟩⟩
        obtain ⟨P, ⟨hP, hzP⟩, huniq⟩ := hcov z hzS'
        refine ⟨P, ⟨Finset.mem_insert_of_mem hP, hzP⟩, ?_⟩
        rintro Q ⟨hQ, hzQ⟩
        rcases Finset.mem_insert.mp hQ with rfl | hQ'
        · rcases Finset.mem_insert.mp hzQ with rfl | hz2
          · exact absurd rfl hzxy.1
          · exact absurd (Finset.mem_singleton.mp hz2) hzxy.2
        · exact huniq Q ⟨hQ', hzQ⟩
    · intro P hP
      rcases Finset.mem_insert.mp hP with rfl | hP'
      · refine ⟨?_, ?_, ?_⟩
        · intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz2
          · exact hx
          · rw [Finset.mem_singleton.mp hz2]; exact hyS
        · rw [Finset.card_insert_of_notMem (by simpa using fun h ↦ hyne h.symm),
            Finset.card_singleton]
        · rw [Finset.sum_insert (by simpa using fun h ↦ hyne h.symm),
            Finset.sum_singleton]
          exact hgy
      · exact ⟨(hpair P hP').1.trans hsub.subset, (hpair P hP').2.1,
          (hpair P hP').2.2⟩

/-! ## Digit arithmetic

The uniqueness lemmas behind the domain's digit gadgets: SUBSET SUM's base-4
construction (`SubsetSum/FromVertexCover.lean`) and 4-PARTITION's base-`r`
construction (`Partition4/FromMatching3D.lean`) both pin gadget data by
reading a sum as a positional numeral. -/

/-- Uniqueness of Euclidean division: two decompositions `a * B + r` with
remainders below `B` are equal componentwise. -/
theorem eq_of_mul_add_eq_mul_add {B a a' r r' : ℕ} (hr : r < B) (hr' : r' < B)
    (h : a * B + r = a' * B + r') : a = a' ∧ r = r' := by
  have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have hdiv : ∀ (c : ℕ) {s : ℕ}, s < B → (c * B + s) / B = c := by
    intro c s hs
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hs, Nat.add_zero]
  have ha : a = a' := by rw [← hdiv a hr, ← hdiv a' hr', h]
  subst ha
  exact ⟨rfl, Nat.add_left_cancel h⟩

/-- One digit-peeling step: a digit below `r` at place `r ^ k` plus a
remainder below `r ^ k` stays below `r ^ (k + 1)`. -/
theorem mul_pow_add_lt_pow_succ {r a b : ℕ} (k : ℕ) (ha : a < r)
    (hb : b < r ^ k) : a * r ^ k + b < r ^ (k + 1) := by
  calc a * r ^ k + b < (a + 1) * r ^ k := by
        rw [Nat.add_mul, Nat.one_mul]; omega
  _ ≤ r * r ^ k := Nat.mul_le_mul_right _ (by omega)
  _ = r ^ (k + 1) := (pow_succ' r k).symm

/-- Base-`r` uniqueness for a four-digit numeral whose three low digits sit
at places `r`, `r²`, `r³` and whose leading coefficient is unconstrained:
componentwise equality. The `+ s` on both sides absorbs a shared additive
offset (the constant residue of a gadget sum), and the leading coefficients
may exceed `r` — only the three inner digits need the bound. -/
theorem digits_base_eq_of_eq {r a a' d₃ d₂ d₁ e₃ e₂ e₁ s : ℕ}
    (hd₃ : d₃ < r) (hd₂ : d₂ < r) (hd₁ : d₁ < r)
    (he₃ : e₃ < r) (he₂ : e₂ < r) (he₁ : e₁ < r) (hs : s < r)
    (h : a * r ^ 4 + d₃ * r ^ 3 + d₂ * r ^ 2 + d₁ * r + s
        = a' * r ^ 4 + e₃ * r ^ 3 + e₂ * r ^ 2 + e₁ * r + s) :
    a = a' ∧ d₃ = e₃ ∧ d₂ = e₂ ∧ d₁ = e₁ := by
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) hd₃
  have hr1 : r ^ 1 = r := pow_one r
  -- remainders under each place are genuinely below it
  have hlow : ∀ {f₃ f₂ f₁ : ℕ}, f₃ < r → f₂ < r → f₁ < r →
      f₁ * r + s < r ^ 2 ∧ f₂ * r ^ 2 + (f₁ * r + s) < r ^ 3 ∧
        f₃ * r ^ 3 + (f₂ * r ^ 2 + (f₁ * r + s)) < r ^ 4 := by
    intro f₃ f₂ f₁ h₃ h₂ h₁
    have e1 : f₁ * r ^ 1 + s < r ^ 2 :=
      mul_pow_add_lt_pow_succ 1 h₁ (by rw [pow_one]; exact hs)
    rw [hr1] at e1
    have e2 : f₂ * r ^ 2 + (f₁ * r + s) < r ^ 3 := mul_pow_add_lt_pow_succ 2 h₂ e1
    exact ⟨e1, e2, mul_pow_add_lt_pow_succ 3 h₃ e2⟩
  obtain ⟨hd1, hd2, hd3⟩ := hlow hd₃ hd₂ hd₁
  obtain ⟨he1, he2, he3⟩ := hlow he₃ he₂ he₁
  -- peel the places from the top
  obtain ⟨ha, hrest⟩ := eq_of_mul_add_eq_mul_add (B := r ^ 4) (a := a)
    (a' := a') hd3 he3 (by linarith [h])
  obtain ⟨h₃, hrest₃⟩ := eq_of_mul_add_eq_mul_add (B := r ^ 3) (a := d₃)
    (a' := e₃) hd2 he2 (by linarith [hrest])
  obtain ⟨h₂, hrest₂⟩ := eq_of_mul_add_eq_mul_add (B := r ^ 2) (a := d₂)
    (a' := e₂) hd1 he1 (by linarith [hrest₃])
  exact ⟨ha, h₃, h₂, Nat.eq_of_mul_eq_mul_right hr (by linarith [hrest₂])⟩

end Hardness
