import SparseBoundary.MinorSearch

namespace SparseBoundary.MinorSearch

open Graph

def visitBits (p : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | k+1, bits =>
    if bits == 0 then false else
      p bits.log2 || visitBits p k (bits % (2^bits.log2))

theorem visit_complete {p : Nat → Bool} {m : Nat} (h : p m = true) :
    ∀ k bits, bits < 2^k → bits.testBit m = true → visitBits p k bits = true := by
  intro k
  induction k with
  | zero => intro b hb; have h0 : b=0 := by simpa using hb
            subst b; simp
  | succ k ih =>
    intro b hb hbit
    have hn : b ≠ 0 := by intro e; simp [e] at hbit
    have top : b.log2 < k+1 := (Nat.log2_lt hn).mpr hb
    have hm : m ≤ b.log2 := by
      apply Classical.byContradiction; intro hgt
      have he := Nat.testBit_lt_two_pow (i:=m) ((Nat.log2_lt hn).mp (by omega))
      simp [he] at hbit
    simp only [visitBits,beq_iff_eq,ite_eq_right (fun eq => (hn eq).elim),Bool.or_eq_true]
    by_cases he : m = b.log2
    · exact Or.inl (he ▸ h)
    · right
      apply ih
      · apply Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        exact Nat.pow_le_pow_right (by decide) (by omega)
      · simp [Nat.testBit_mod_two_pow,hbit,show m < b.log2 by omega]

abbrev CompatTable := Array (Nat × Nat)

def rowFor (t : CompatTable) (i : Nat) (edge : Bool) : Nat :=
  let (separate,adjacent) := t[i]?.getD (0,0)
  if edge then adjacent else separate

/-- The table maps a branch set to all the possible next branch sets,
    with or without a required connecting edge. -/
def validTable (cat : Array (Option Nat)) (initial : Nat) (t : CompatTable) : Bool :=
  (pool cat).all fun b => initial.testBit b.verts &&
    (pool cat).all fun c =>
      (!distinctBags b c || (rowFor t b.verts false).testBit c.verts) &&
      (!compat true b c || (rowFor t b.verts true).testBit c.verts)

/-- A bit indexed by a vertex set records whether it avoids the given set. -/
def avoiding (n m : Nat) : Nat :=
  (List.range n).foldl (fun z i => if m.testBit i then z else z ||| (z <<< (2^i))) 1

def makeTable (n : Nat) (cat : Array (Option Nat)) (initial : Nat) : CompatTable :=
  ((List.range cat.size).map fun m =>
    match cat[m]?.join with
    | none => (0,0)
    | some ns =>
      let dis := initial &&& avoiding n m
      (dis,dis ^^^ (dis &&& avoiding n ns))).toArray

def bitSearch {k : Nat} (R : Fin k → Fin k → Bool) (t : CompatTable) :
    List (Fin k) → (Fin k → Nat) → Bool
  | [], _ => true
  | i :: is, opts =>
    visitBits (fun m => bitSearch R t is (fun j => opts j &&& rowFor t m (R i j)))
      ((opts i).log2+1) (opts i)

theorem forbidden_of_table {n k : Nat} (g : Graph n) (R : Fin k → Fin k → Bool)
    (cat : Array (Option Nat)) (initial : Nat) (t : CompatTable)
    (order : List (Fin k)) (ho : order.Nodup)
    (hc : covers g cat = true) (ht : validTable cat initial t = true)
    (hn : bitSearch R t order (fun _ => initial) = false) :
    ¬ ∃ bags, g.minorTest R bags = true := by
  rintro ⟨bags, h⟩
  have rr i := List.all_eq_true.mp h i (List.mem_finRange i)
  simp only [Bool.and_eq_true] at rr
  have hin i := in_pool (covered hc _ (rr i).1)
  have rrow i := List.all_eq_true.mp ht _ (hin i)
  simp only [Bool.and_eq_true] at rrow
  suffices complete : ∀ (is : List (Fin k)), is.Nodup → ∀ (opts : Fin k → Nat),
      (∀ i ∈ is, (opts i).testBit (encode g (bags i)).verts = true) →
      bitSearch R t is opts = true by
    have hh := complete order ho _ (fun i _ => (rrow i).1)
    simp_all
  intro is
  induction is with
  | nil => intros; rfl
  | cons i is ih =>
    intro hnod opts hm
    have hnd := List.nodup_cons.mp hnod
    apply visit_complete (m:=(encode g (bags i)).verts) _ _ _ Nat.lt_log2_self
      (hm i (List.mem_cons_self ..))
    apply ih hnd.2
    intro j hj
    simp only [Nat.testBit_and,hm j (List.mem_cons_of_mem _ hj),Bool.true_and]
    have htj := List.all_eq_true.mp (rrow i).2 _ (hin j)
    simp only [Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at htj
    have cell := List.all_eq_true.mp (rr i).2 j (List.mem_finRange j)
    have ne : i ≠ j := by rintro rfl; exact hnd.1 hj
    simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at cell
    have hd := distinct_of (g:=g) (cell.1.resolve_left ne)
    cases he : R i j with
    | false => exact htj.1.resolve_left (by simp [hd])
    | true =>
      have ht' := touch_of (g:=g) (cell.2.resolve_left (by simp [he]))
      exact htj.2.resolve_left (by simp [compat,hd,ht'])

end SparseBoundary.MinorSearch
