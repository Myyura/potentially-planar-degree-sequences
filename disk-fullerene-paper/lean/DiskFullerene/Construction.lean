import Std

namespace DiskFullerene.Construction

/- Local labels 0, 1,…,5, 6,…,9, 10,11 stand for c, the five rim vertices,
   b₂,…,b₅, b₀,b₁. The last two lie on the marked edge. -/
abbrev Triangle := Nat × Nat × Nat

def rim (i : Nat) := 1 + i % 5

def boundary : Nat → Nat
  | 0 => 10
  | 1 => 11
  | i+2 => 6+i

def endFaces : List Triangle :=
  (List.range 5).map (fun i => (0, rim i, rim (i+1))) ++
  (List.range 5).map (fun i => (rim i, rim (i+1), boundary (i+1))) ++
  (List.range 5).map (fun i => (rim i, boundary i, boundary (i+1))) ++
  [(rim 0, boundary 5, boundary 0)]

def contains (t : Triangle) (v : Nat) : Bool :=
  v == t.1 || v == t.2.1 || v == t.2.2

def capEdge (u v : Nat) : Bool :=
  u != v && endFaces.any (fun t => contains t u && contains t v)

theorem capEdge_comm (u v : Nat) : capEdge u v = capEdge v u := by
  simp only [capEdge, bne_comm, Bool.and_comm (contains _ u) (contains _ v)]

inductive Vertex where
  | pole
  | cap (right : Bool) (localVertex : Fin 10)
  | spine (i : Nat)
deriving DecidableEq, Repr

open Vertex

/-- The parameter is n = h − 12. The strip consists of n+2 consecutive triples. -/
def seamZero (n : Nat) (right : Bool) := if right then n+2 else 1
def seamOne (n : Nat) (right : Bool) := if right then n+3 else 0

def joinEdge (n : Nat) (s : Bool) (u : Fin 10) (i : Nat) : Bool :=
  (capEdge u.val 10 && i == seamZero n s) || (capEdge u.val 11 && i == seamOne n s)

/-- Edges of the consecutive triples (i,i+1,i+2) on the valid spine indices. -/
def stripEdge (i j : Nat) : Bool :=
  decide (i ≠ j ∧ i ≤ j+2 ∧ j ≤ i+2)

def adj (n : Nat) : Vertex → Vertex → Bool
  | pole, pole => false
  | pole, cap _ u | cap _ u, pole => decide (6 ≤ u.val)
  | pole, spine _ | spine _, pole => true
  | cap s u, cap t v => (s == t) && capEdge u.val v.val
  | cap s u, spine i | spine i, cap s u => joinEdge n s u i
  | spine i, spine j => stripEdge i j

theorem adj_symm (n : Nat) (u v : Vertex) : adj n u v = adj n v u := by
  cases u <;> cases v <;> simp only [adj, capEdge_comm, BEq.comm, stripEdge] <;>
    first | rfl | congr 1; apply propext; omega

theorem adj_loopless (n : Nat) (v : Vertex) : adj n v v = false := by
  cases v <;> simp [adj, capEdge, stripEdge]

def vertices (n : Nat) : List Vertex :=
  [pole] ++ (List.finRange 10).map (cap false) ++ (List.finRange 10).map (cap true) ++
    (List.range (n+4)).map spine

def degree (n : Nat) (v : Vertex) := (vertices n).countP (adj n v)

theorem vertexCount (n : Nat) : (vertices n).length = n+25 := by
  simp [vertices]; omega

private theorem countTwo (p q : Bool) (a b m : Nat) (d : a ≠ b) :
    (List.range m).countP (fun i => (p && i == a) || (q && i == b)) =
      (if p && decide (a < m) then 1 else 0) +
      (if q && decide (b < m) then 1 else 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil]
    cases p <;> cases q <;> simp <;> (repeat' first | omega | split)

private theorem countBand (i m : Nat) :
    (List.range m).countP (stripEdge i) =
      min m (i+3) - min m (i-2) - (if i < m then 1 else 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, stripEdge, decide_eq_true_eq]
    (repeat' first | omega | split)

private theorem capNumbers : ∀ u : Fin 10,
    ((List.finRange 10).countP (fun v => capEdge u.val v.val)) +
      (if capEdge u.val 10 then 1 else 0) +
      (if capEdge u.val 11 then 1 else 0) +
      (if 6 ≤ u.val then 1 else 0) = (if u.val = 1 then 6 else 5) := by decide

private theorem seamNumbers (a b : Bool) :
    (List.finRange 10).countP (fun u => (capEdge u.val 10 && a) || (capEdge u.val 11 && b)) =
      (if a then 2 else 0) + (if b then 3 else 0) - (if a && b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem degreePole (n : Nat) : degree n pole = n+12 := by
  have e : (List.finRange 10).countP (fun u => decide (6 ≤ u.val)) = 4 := by decide
  simp [degree, vertices, adj, List.countP_map, Function.comp_def, e]
  omega

theorem degreeCap (n : Nat) (s : Bool) (u : Fin 10) :
    degree n (cap s u) = if u.val = 1 then 6 else 5 := by
  have h := capNumbers u
  have d : seamZero n s ≠ seamOne n s := by cases s <;> simp [seamZero,seamOne]
  have a : seamZero n s < n+4 := by cases s <;> simp [seamZero] <;> omega
  have b : seamOne n s < n+4 := by cases s <;> simp [seamOne] <;> omega
  simp only [degree, vertices, List.countP_append, List.countP_map, Function.comp_def,
    List.countP_cons, List.countP_nil, adj, joinEdge]
  rw [countTwo _ _ _ _ _ d]
  cases s <;> simp [a,b] <;> omega

theorem degreeSpine (n i : Nat) (hi : i < n+4) :
    degree n (spine i) = if i < 2 ∨ n+2 ≤ i then 6 else 5 := by
  simp only [degree, vertices, List.countP_append, List.countP_map, List.countP_cons,
    List.countP_nil, Function.comp_def, adj, joinEdge]
  rw [seamNumbers, seamNumbers, countBand]
  simp only [seamZero, seamOne, Bool.false_eq_true, ite_false, ite_true, beq_iff_eq,
    Bool.and_eq_true, Nat.reduceAdd]
  (repeat' first | omega | split)

theorem vertices_nodup (n : Nat) : (vertices n).Nodup := by
  let ends := [pole] ++ (List.finRange 10).map (cap false) ++ (List.finRange 10).map (cap true)
  have he : ends.Nodup := by decide
  change (ends ++ _).Nodup
  rw [List.nodup_append]
  refine ⟨he, ?_, ?_⟩
  · change (List.map spine (List.range (n+4))).Pairwise _
    rw [List.pairwise_map]
    exact List.nodup_range.imp (fun h eq => h (Vertex.spine.inj eq))
  · intro a ha b hb heq
    rcases List.mem_map.mp hb with ⟨i, _, rfl⟩
    subst a
    simp [ends] at ha

private theorem countOuter (n m : Nat) (outer : Bool) :
    (List.range m).countP (fun i => decide (i < 2 ∨ n+2 ≤ i) == outer) =
      if outer then min m 2 + (m - (n+2)) else min (m-2) n := by
  induction m with
  | zero => cases outer <;> simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, ih]
    cases outer <;> simp [List.countP_cons] <;> (repeat' first | omega | split)

private theorem spineHistogram (n : Nat) (outer : Bool) :
    (List.range (n+4)).countP (fun i => degree n (spine i) == (if outer then 6 else 5)) =
    (if outer then 4 else n) := by
  apply Eq.trans (b := (List.range (n+4)).countP (fun i => decide (i < 2 ∨ n+2 ≤ i) == outer))
  · apply List.countP_congr
    intro i hi
    rw [degreeSpine _ _ (List.mem_range.mp hi)]
    cases outer <;> by_cases h : i < 2 ∨ n+2 ≤ i <;> simp [h]
  · rw [countOuter]
    cases outer <;> simp <;> omega

/-- Exact counts on the finite, repetition-free vertex list of the explicit graph. -/
theorem degreeInventory (n : Nat) :
    (vertices n).countP (fun v => degree n v == n+12) = 1 ∧
    (vertices n).countP (fun v => degree n v == 5) = n+18 ∧
    (vertices n).countP (fun v => degree n v == 6) = 6 := by
  have mid : (List.range (n+4)).countP (fun i => degree n (spine i) == n+12) = 0 := by
    apply List.countP_eq_zero.mpr
    intro i hi
    rw [degreeSpine _ _ (List.mem_range.mp hi)]
    simp only [beq_iff_eq]; split <;> omega
  have cp : (List.finRange 10).countP (fun u => (if u.val = 1 then 6 else 5) == n+12) = 0 := by
    apply List.countP_eq_zero.mpr
    intro _ _
    simp only [beq_iff_eq]; split <;> omega
  have c5 : (List.finRange 10).countP (fun u => ((if u.val = 1 then 6 else 5) : Nat) == 5) = 9 := by decide
  have c6 : (List.finRange 10).countP (fun u => ((if u.val = 1 then 6 else 5) : Nat) == 6) = 1 := by decide
  have s5 := spineHistogram n false
  have s6 := spineHistogram n true
  simp only [Bool.false_eq_true, ite_false, ite_true] at s5 s6
  simp only [vertices, List.countP_append, List.countP_map, Function.comp_def, List.countP_cons,
    List.countP_nil, degreePole, degreeCap, mid, cp, c5, c6, s5, s6, beq_iff_eq]
  repeat' constructor
  all_goals (repeat' first | omega | split)

end DiskFullerene.Construction
