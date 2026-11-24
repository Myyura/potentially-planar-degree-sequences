import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange

/-!
# Counting a family block by block

The catalog's optimization problems — MAX 2SAT, and SIMPLE MAX CUT after it —
ask how *many* members of a family a witness satisfies, where every previous
predicate only exhibited or bounded a set. Their constructions all have the same
shape: the family is a concatenation of one block per source object, each block
contributes at most `m`, and the threshold is `m` times the number of blocks. So
the threshold is attained only if *every* block attains `m`, and that is the step
that turns a global count back into a local statement about each source object.

The three lemmas here are that argument, stated over `List.countP` and
`List.sum`:

* `countP_flatMap` splits the count of a concatenated family into the counts of
  its blocks;
* `sum_map_le_mul_length` is the upper bound, `blocks × m`;
* `eq_of_sum_map_ge` is the forcing step — at the threshold, no block has any
  slack to give.

The pair `sum_map_le_mul_length` / `eq_of_sum_map_ge` is deliberately stated
about the *same* two hypotheses, because a reduction needs both directions of
the same block bound: the upper bound is what makes an over-threshold instance
impossible (and so what lets a junk instance be excluded by raising the
threshold above it), and the forcing step is what extracts the witness.
-/

namespace Hardness

variable {α : Type*}

/-- `countP` distributes over `flatMap`: the count of a concatenated family is
the sum of the counts of its blocks. -/
theorem countP_flatMap (p : α → Bool) {β : Type*} (l : List β) (f : β → List α) :
    (l.flatMap f).countP p = (l.map fun a ↦ (f a).countP p).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.countP_append, List.map_cons, List.sum_cons, ih]

/-- **The upper bound**: if every block contributes at most `m`, the total is at
most `m` per block. Stated with no hypothesis on the blocks beyond the bound, so
that a construction may apply it to junk inputs as well — which is what makes a
threshold above it a sound way to reject them. -/
theorem sum_map_le_mul_length {l : List α} {g : α → ℕ} {m : ℕ}
    (h : ∀ a ∈ l, g a ≤ m) : (l.map g).sum ≤ l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have ha := h a List.mem_cons_self
    have hl := ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    omega

/-- The total when every block contributes the same amount — the companion of
`eq_of_sum_map_ge`, used on the constructing side of a reduction where each
block is built to attain `m` exactly. -/
theorem sum_map_const {l : List α} {g : α → ℕ} {m : ℕ}
    (h : ∀ a ∈ l, g a = m) : (l.map g).sum = l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul,
      h a List.mem_cons_self, ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]
    omega

/-- **The count as a sum of indicators.** A construction indexed by *positions*
counts its source with a sum over `List.finRange`, while `numSat` and its kin are
`countP`s over the list itself; this is the one rewrite between the two views. -/
theorem countP_eq_sum_map (l : List α) (p : α → Bool) :
    l.countP p = (l.map fun a ↦ if p a then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
    cases p a <;> simp [Nat.add_comm]

/-- Blockwise bounds add up. -/
theorem sum_map_le_sum_map {l : List α} {f g : α → ℕ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self)
      (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-- Reading a list-indexed family back as a family over the list. Stated for an
arbitrary `f` so that both the counting view and the summing view of a
position-indexed construction can use it. -/
theorem map_finRange_getElem (l : List α) {β : Type*} (f : α → β) :
    ((List.finRange l.length).map fun i ↦ f (l[i.1]'i.isLt)) = l.map f := by
  refine List.ext_getElem (by simp) fun k h1 h2 ↦ ?_
  rw [List.getElem_map, List.getElem_map]
  simp

/-- A sum of pointwise sums splits — the form a per-block bound of the shape
`base + contribution` is added up in. -/
theorem sum_map_add (l : List α) (f g : α → ℕ) :
    (l.map fun a ↦ f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.map_cons,
      List.sum_cons]
    omega

/-- A doubled family sums to twice the sum — how "each satisfied pair is worth
two edges" leaves the sum. -/
theorem sum_map_two_mul (l : List α) (f : α → ℕ) :
    (l.map fun a ↦ 2 * f a).sum = 2 * (l.map f).sum := by
  rw [List.map_congr_left fun a _ ↦ Nat.two_mul (f a), sum_map_add]
  omega

/-- **One member bounds the sum below** — the lower-bound mirror of the upper
bounds above, and the shape of an amplification argument: exhibiting a single
block whose contribution is large forces the whole family's total past it,
whatever the other blocks do. -/
theorem le_sum_map_of_mem {l : List α} {g : α → ℕ} {a : α} (h : a ∈ l) :
    g a ≤ (l.map g).sum := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h
      omega

/-- Complementary counts partition the length. Stated with `!p` rather than the
standard library's propositional negation, so that a *lower* bound on the
failures converts to an upper bound on the successes without a `decide`
shim. -/
theorem countP_add_countP_not (l : List α) (p : α → Bool) :
    l.countP p + l.countP (fun a ↦ !p a) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons, ← ih]
    cases p a <;> simp <;> omega

/-- **The forcing step**: a family whose blocks each contribute at most `m`, and
whose total reaches `m` per block, has *every* block contributing exactly `m`.
This is what turns "the threshold is met" into a statement about each source
object separately. -/
theorem eq_of_sum_map_ge {l : List α} {g : α → ℕ} {m : ℕ}
    (hle : ∀ a ∈ l, g a ≤ m) (hsum : l.length * m ≤ (l.map g).sum) :
    ∀ a ∈ l, g a = m := by
  induction l with
  | nil => intro a ha; exact absurd ha (List.not_mem_nil)
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at hsum
    have hrest : (l.map g).sum ≤ l.length * m :=
      sum_map_le_mul_length fun b hb ↦ hle b (List.mem_cons_of_mem _ hb)
    have ha : g a = m := by
      have := hle a List.mem_cons_self
      omega
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ih (fun c hc ↦ hle c (List.mem_cons_of_mem _ hc)) (by omega) b hb

/-! ## Reading a two-per-source family by position

A construction that replaces each source object by exactly *two* new ones —
the MAX 2SAT split, whose blocks are the pairs `2i` and `2i + 1` — is a
`flatMap` of two-element blocks. A certificate iterating the source list once
and emitting both must line its own index `i` up with the construction's `2i`
and `2i + 1`, in both directions: reading the pair at a known position, and
splitting an existential over positions into one over sources. -/

theorem getElem?_flatMap_two {α β : Type*} (f g : β → α) :
    ∀ (l : List β) (i : ℕ),
      (l.flatMap fun b ↦ [f b, g b])[2 * i]? = (l[i]?).map f ∧
      (l.flatMap fun b ↦ [f b, g b])[2 * i + 1]? = (l[i]?).map g := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a t ih =>
    intro i
    cases i with
    | zero => simp
    | succ k =>
      have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [List.flatMap_cons, h2]
      simpa using ih k

/-- Reading a flattened four-element-block `flatMap` at the four positions
of block `i` — the four-block analogue of `getElem?_flatMap_two`, for the
certificates that emit four numbers per source object. -/
theorem getElem?_flatMap_four {α β : Type*} (f g h j : β → α) :
    ∀ (l : List β) (i : ℕ),
      (l.flatMap fun b ↦ [f b, g b, h b, j b])[4 * i]? = (l[i]?).map f ∧
      (l.flatMap fun b ↦ [f b, g b, h b, j b])[4 * i + 1]? = (l[i]?).map g ∧
      (l.flatMap fun b ↦ [f b, g b, h b, j b])[4 * i + 2]? = (l[i]?).map h ∧
      (l.flatMap fun b ↦ [f b, g b, h b, j b])[4 * i + 3]? = (l[i]?).map j := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a t ih =>
    intro i
    cases i with
    | zero => simp
    | succ k =>
      rw [List.flatMap_cons,
        show 4 * (k + 1) + 3 = 4 * k + 3 + 1 + 1 + 1 + 1 from by omega,
        show 4 * (k + 1) + 2 = 4 * k + 2 + 1 + 1 + 1 + 1 from by omega,
        show 4 * (k + 1) + 1 = 4 * k + 1 + 1 + 1 + 1 + 1 from by omega,
        show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 from by omega]
      simpa using ih k

/-- `range (2n)` regrouped into consecutive pairs. -/
theorem range_two_flatMap (n : ℕ) :
    List.range (2 * n) = (List.range n).flatMap (fun i ↦ [2 * i, 2 * i + 1]) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ← ih,
      show 2 * (k + 1) = 2 * k + 1 + 1 by omega, List.range_succ, List.range_succ]
    simp

/-- `finRange (2n)` regrouped into consecutive pairs — the `Fin` face, which a
`flatMap` over a doubled index range needs. -/
theorem finRange_two_mul (n : ℕ) :
    (List.finRange n).flatMap
      (fun i ↦ [(⟨2 * i.1, by omega⟩ : Fin (2 * n)), ⟨2 * i.1 + 1, by omega⟩])
      = List.finRange (2 * n) := by
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [List.map_coe_finRange_eq_range, List.map_flatMap]
  have h : (List.finRange n).flatMap
      (fun i ↦ (List.map Fin.val
        [(⟨2 * i.1, by omega⟩ : Fin (2 * n)), ⟨2 * i.1 + 1, by omega⟩]))
      = (List.finRange n).flatMap (fun i ↦ [2 * i.1, 2 * i.1 + 1]) :=
    List.flatMap_congr fun i _ ↦ rfl
  rw [h, range_two_flatMap n, ← List.map_coe_finRange_eq_range, List.flatMap_map]

/-- **A `flatMap` over a doubled index range, regrouped by source.** A
certificate that emits both of a source object's two descendants in one pass
proves its output matches the construction's — which indexes the descendants
`2i` and `2i + 1` separately — through this. -/
theorem flatMap_finRange_two_mul {α : Type*} {n : ℕ} (H : Fin (2 * n) → List α) :
    (List.finRange (2 * n)).flatMap H
      = (List.finRange n).flatMap
          (fun i ↦ H ⟨2 * i.1, by omega⟩ ++ H ⟨2 * i.1 + 1, by omega⟩) := by
  rw [← finRange_two_mul n, List.flatMap_assoc]
  refine List.flatMap_congr fun i _ ↦ ?_
  simp

/-- The same, when the doubled length arrives as a propositional equality rather
than syntactically — which is how a certificate meets it, the constructed list's
length being a theorem, not a definitional `2 * _`. -/
theorem flatMap_finRange_two_of_len {α : Type*} {N n : ℕ} (hN : N = 2 * n)
    (H : Fin N → List α) :
    (List.finRange N).flatMap H
      = (List.finRange n).flatMap
          (fun i ↦ H ⟨2 * i.1, by omega⟩ ++ H ⟨2 * i.1 + 1, by omega⟩) := by
  subst hN
  exact flatMap_finRange_two_mul H

/-- Enumerating a list is mapping its position range — the form a certificate's
`listEnum`-pass takes when matched against a construction indexed by `Fin`. -/
theorem zipIdx_eq_finRange {α : Type*} (l : List α) :
    l.zipIdx = (List.finRange l.length).map (fun i ↦ (l[i.1], i.1)) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [List.getElem_zipIdx]

/-- Reindexing a `finRange` `flatMap` across a length equality. The pure-`Fin`
face of the recurring "the program iterates `x.length`, the construction
`(decode x).length`" transport. -/
theorem finRange_flatMap_cast {α : Type*} {n n' : ℕ} (h : n = n') (f : Fin n → List α) :
    (List.finRange n).flatMap f
      = (List.finRange n').flatMap (fun i ↦ f ⟨i.1, by omega⟩) := by
  subst h; rfl

/-- A position in a doubled range is a source index together with a side. -/
theorem exists_fin_two_mul {n : ℕ} (P : ℕ → Prop) :
    (∃ i' : Fin (2 * n), P i'.1) ↔ ∃ i : Fin n, P (2 * i.1) ∨ P (2 * i.1 + 1) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hP⟩
    refine ⟨⟨k / 2, by omega⟩, ?_⟩
    have h : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h with h | h
    · exact Or.inl (by rwa [show 2 * (k / 2) = k by omega])
    · exact Or.inr (by rwa [show 2 * (k / 2) + 1 = k by omega])
  · rintro ⟨⟨i, hi⟩, hP | hP⟩
    · exact ⟨⟨2 * i, by omega⟩, hP⟩
    · exact ⟨⟨2 * i + 1, by omega⟩, hP⟩

/-- Dropping the zero from `range m` leaves the shifted `range (m - 1)`. The
identity behind an annex that enumerates `1, …, m - 1` by filtering the indices
of a list of length `m`. -/
theorem filter_pos_range (m : ℕ) :
    (List.range m).filter (fun j ↦ decide (0 < j)) = (List.range (m - 1)).map (· + 1) := by
  cases m with
  | zero => simp
  | succ k =>
    rw [List.range_succ_eq_map, Nat.add_sub_cancel, List.filter_cons_of_neg (by simp)]
    refine List.filter_eq_self.mpr fun a ha ↦ ?_
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    simp

end Hardness
