import RowRecognition
import Mathlib.Data.List.Sublists
import Listing

/-! Explicit, layered dynamic programming for the numerical interval rule.
A state stores the multiset already consumed in input order and the current
row of positive balances. Different occurrences may give identical keys. -/
namespace Recognition.IntervalSearch
open RowRule

/-- All prefix/suffix cuts, including the two ends. -/
def cuts : List Nat → List (List Nat × List Nat)
  | [] => [([], [])]
  | x :: xs => ([], x :: xs) :: (cuts xs).map (fun p => (x :: p.1, p.2))

theorem cuts_spec (row a b : List Nat) : (a,b) ∈ cuts row ↔ row = a ++ b := by
  induction row generalizing a b with
  | nil => cases a <;> simp [cuts]
  | cons x xs ih =>
    cases a with
    | nil => simp [cuts, eq_comm]
    | cons y ys =>
      simp [cuts, Prod.exists, ih, and_assoc, eq_comm, and_left_comm]

@[simp] theorem cuts_length (row : List Nat) : (cuts row).length = row.length+1 := by
  induction row <;> simp [cuts, *]

/-- A scan of four cuts enumerates exactly the five pieces of a numerical move. -/
def following (row : List Nat) (d : Nat) : List (List Nat) :=
  (cuts row).flatMap fun (l,r₁) =>
  (cuts r₁).flatMap fun (a,r₂) =>
  (cuts r₂).flatMap fun (b,r₃) =>
  (cuts r₃).filterMap fun (c,r) =>
    if a.length ≤ 1 ∧ c.length ≤ 1 ∧ (∀ x ∈ b, x = 1) ∧ (a++b++c).length ≤ d then
      some ((l ++ (a++b).map (· - 1) ++ (d-(a++b++c).length) :: (c.map (· - 1) ++ r)).filter
        (fun x => 0 < x))
    else none

theorem following_spec (row : List Nat) (d : Nat) (out : List Nat) :
    out ∈ following row d ↔ ∃ m : NumericalMove row d, m.next = out := by
  simp only [following, List.mem_flatMap, List.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨l,r₁,h₁,a,r₂,h₂,b,r₃,h₃,c,r,h₄,h⟩
    rw [cuts_spec] at h₁ h₂ h₃ h₄
    split at h
    · rename_i ok
      refine ⟨⟨l,a,b,c,r,by simp [h₁,h₂,h₃,h₄,List.append_assoc],
        ok.1,ok.2.1,ok.2.2.1,ok.2.2.2⟩,Option.some.inj h⟩
    · contradiction
  · rintro ⟨m,rfl⟩
    refine ⟨m.left, m.first++m.middle++m.last++m.right, (cuts_spec ..).2 ?_,
      m.first, m.middle++m.last++m.right, (cuts_spec ..).2 ?_,
      m.middle, m.last++m.right, (cuts_spec ..).2 ?_,
      m.last,m.right,(cuts_spec ..).2 rfl,?_⟩
    · simpa [List.append_assoc] using m.split
    · simp [List.append_assoc]
    · simp [List.append_assoc]
    · rw [ite_eq_left ⟨m.firstSize,m.lastSize,m.interior,m.affordable⟩]
      rfl

private def bump : List Nat → List Nat
  | [] => [1]
  | a::r => (a+1)::r

/-- Positive compositions of every weight up to the given bound, with harmless
duplicates. Both maps share the list for the preceding budget. -/
def rows : Nat → List (List Nat)
  | 0 => [[]]
  | s+1 => let old := rows s; [] :: (old.map (1::·) ++ old.map bump)

theorem rows_size (s : Nat) : (rows s).length + 1 = 2^(s+1) := by
  induction s with
  | zero => decide
  | succ s ih =>
    simp only [rows,List.length_cons,List.length_append,List.length_map,pow_succ] at *
    omega

theorem rows_complete (s : Nat) (r : List Nat) (pos : ∀ x ∈ r, 0<x) (mass : r.sum ≤ s) :
    r ∈ rows s := by
  induction s generalizing r with
  | zero =>
    cases r with
    | nil => simp [rows]
    | cons a r => have := pos a (by simp); simp only [List.sum_cons] at mass; omega
  | succ s ih =>
    cases r with
    | nil => simp [rows]
    | cons a r =>
      have pa := pos a (.head _)
      have pr : ∀ x ∈ r, 0<x := fun x hx => pos x (.tail _ hx)
      simp only [List.sum_cons] at mass
      simp only [rows,List.mem_cons,List.mem_append,List.mem_map]
      by_cases one : a=1
      · subst a
        exact .inr (.inl ⟨r,ih r pr (by omega),rfl⟩)
      · refine .inr (.inr ⟨(a-1)::r,ih _ ?_ ?_,?_⟩)
        · simp only [List.mem_cons]; rintro t (rfl|ht)
          · omega
          · exact pr _ ht
        · simp; omega
        · simp [bump]; omega

theorem rows_sound {s r} (h : r∈rows s) : (∀ x∈r, 0<x) ∧ r.sum≤s := by
  induction s generalizing r with
  | zero => simp [rows] at h; subst r; simp
  | succ s ih =>
    simp only [rows,List.mem_cons,List.mem_append,List.mem_map] at h
    rcases h with rfl | ⟨l,m,rfl⟩ | ⟨l,m,rfl⟩
    · simp
    · obtain ⟨hp,hs⟩ := ih m
      exact ⟨by simpa using hp,by simp; omega⟩
    · obtain ⟨hp,hs⟩ := ih m
      cases l with
      | nil => simp [bump]
      | cons a r =>
        simp only [List.sum_cons] at hs
        exact ⟨by simpa [bump] using fun x hx => hp x (List.mem_cons_of_mem a hx),
          by simp [bump]; omega⟩

private theorem filtered_le (r : List Nat) : (r.filter (fun x => 0<x)).sum ≤ r.sum := by
  induction r with
  | nil => simp
  | cons x r ih => by_cases h : 0<x <;> simp [h] <;> omega

private theorem pred_le (r : List Nat) : (r.map (·-1)).sum ≤ r.sum := by
  induction r with
  | nil => simp
  | cons x r ih => simp; omega

theorem next_mass {row d} (m : NumericalMove row d) : m.next.sum ≤ row.sum+d := by
  apply (filtered_le _).trans
  have eq := congrArg List.sum m.split
  have a := pred_le (m.first++m.middle)
  have b := pred_le m.last
  simp only [List.sum_append,List.sum_cons] at *
  omega

theorem trace_bounds {xs row} (h : NumericalTrace xs row) : (∀ x∈row, 0<x) ∧ row.sum≤xs.sum := by
  induction h with
  | start => simp
  | advance _ m ih =>
    exact ⟨fun _ hx => decide_eq_true_eq.mp (List.mem_filter.mp hx).2,
      (next_mass m).trans (by simp; omega)⟩

abbrev Key := List Nat × List Nat

def pool (ds : List Nat) : List Key := ds.sublists'.flatMap fun used => (rows ds.sum).map (used,·)

theorem pool_size (ds : List Nat) :
    (pool ds).length = 2^ds.length * (rows ds.sum).length := by
  simp [pool,List.length_flatMap,List.length_sublists']

theorem pool_mem (ds used row : List Nat) (sub : used.Sublist ds)
    (pos : ∀ x∈row,0<x) (mass : row.sum≤ds.sum) : (used,row)∈pool ds := by
  simp [pool,List.mem_sublists',sub,rows_complete _ _ pos mass]

def advances (before after : Key) : Bool :=
  after.1.any fun d => before.1 == after.1.erase d && (following before.2 d).contains after.2

def layer (keys : List Key) : Nat → List Key
  | 0 => [([],[])]
  | k+1 => let prev := layer keys k; keys.filter (fun next => prev.any (advances · next))

theorem advances_spec (u r v s : List Nat) :
    advances (u,r) (v,s) = true ↔ ∃ d∈v, u=v.erase d ∧ ∃ m : NumericalMove r d, m.next=s := by
  simp [advances,following_spec]

theorem layer_sound {ds : List Nat} {k u r} (mem : (u,r)∈layer (pool ds) k) :
    ∃ xs, xs.Perm u ∧ NumericalTrace xs r := by
  induction k generalizing u r with
  | zero =>
    have e : u=[] ∧ r=[] := by simpa [layer] using mem
    obtain ⟨rfl,rfl⟩ := e
    exact ⟨[],.refl _,.start⟩
  | succ k ih =>
    obtain ⟨_,q⟩ := List.mem_filter.mp mem
    obtain ⟨⟨v,w⟩,hit,step⟩ := List.any_eq_true.mp q
    obtain ⟨d,hd,prior,m,eq⟩ := (advances_spec ..).mp step
    obtain ⟨xs,perm,trace⟩ := ih hit
    refine ⟨xs++[d],?_,eq ▸ trace.advance m⟩
    exact (List.perm_append_singleton d xs).trans
      ((perm.trans (prior ▸ List.Perm.refl _)).cons d |>.trans (List.perm_cons_erase hd).symm)

theorem layer_complete {ds xs row} (trace : NumericalTrace xs row) (u : List Nat)
    (perm : xs.Perm u) (sub : u.Sublist ds) : (u,row) ∈ layer (pool ds) xs.length := by
  induction trace generalizing u with
  | start =>
    have : u = [] := (List.Perm.nil_eq perm).symm
    subst u; simp [layer]
  | @advance xs row d t m ih =>
    have pp : (d::xs).Perm u := (List.perm_append_singleton d xs).symm.trans perm
    obtain ⟨mem,p⟩ := List.cons_perm_iff_perm_erase.mp pp
    have prior := ih (u.erase d) p ((List.erase_sublist ..).trans sub)
    have limits := trace_bounds (t.advance m)
    have sm : u.sum ≤ ds.sum := sub.sum_le_sum (by simp)
    have bound : (xs++[d]).sum=u.sum := perm.sum_eq
    simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
    apply List.mem_filter.mpr
    refine ⟨pool_mem ds u m.next sub limits.1 (by omega),?_⟩
    exact List.any_eq_true.mpr ⟨(u.erase d,row),prior,(advances_spec ..).2 ⟨d,mem,rfl,m,rfl⟩⟩

def accepts (ds : List Nat) : Bool :=
  let xs := ds.filter (fun x => 0<x)
  (layer (pool xs) xs.length).contains (xs,[])

theorem accepts_iff (ord : CanonicalRow.CanonicalOrderingInput) (ds : List Nat) :
    accepts ds = true ↔ SparseBoundary.Planaric ds := by
  let xs := ds.filter (fun x => 0<x)
  rw [RowRecognition.interval_iff ord]
  change (layer (pool xs) xs.length).contains (xs,[]) = true ↔ _
  rw [List.contains_iff_mem]
  constructor
  · exact layer_sound
  · rintro ⟨ys,perm,trace⟩
    simpa [perm.length_eq] using layer_complete trace xs perm (.refl xs)

end Recognition.IntervalSearch
