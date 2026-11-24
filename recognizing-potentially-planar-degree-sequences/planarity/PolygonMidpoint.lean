import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic

/-! A rooted polygon triangulation splits at the triangle on its root edge.
The two boundary degrees stay ordered. All other vertices are internal to
the boundary path and can enter an additive degree inventory immediately. -/
namespace Recognition.PolygonMidpoint

inductive Shape where
  | edge
  | triangle (left right : Shape)

def Shape.size : Shape → Nat
  | .edge => 0
  | .triangle l r => l.size + r.size + 1

structure Signature where
  first : Nat
  last : Nat
  middle : Nat
  deriving BEq, DecidableEq

/-- There are only twelve vertices in the application, so the base exceeds
each multiplicity. Only the forward implication (equal profiles have equal
inventories) is needed for the obstruction. -/
def weight (d : Nat) := 16^d

def join (p q : Signature) : Signature :=
  ⟨p.first+1, q.last+1, p.middle + q.middle + weight (p.last+q.first)⟩

def Shape.signature : Shape → Signature
  | .edge => ⟨1,1,0⟩
  | .triangle l r => join l.signature r.signature

def Signature.code (s : Signature) := s.middle + weight s.first + weight s.last

/-- Build by increasing triangle count; the cut position fixes the two
smaller indices and is distinct for each possible root triangle. -/
def spectra : (n : Nat) → List Signature
  | 0 => [⟨1,1,0⟩]
  | n+1 => (List.finRange (n+1)).flatMap fun i =>
      (spectra i.val).flatMap fun left =>
        (spectra (n-i.val)).map (join left)
termination_by n => n
decreasing_by all_goals have := i.isLt; omega

theorem occurs (t : Shape) : t.signature ∈ spectra t.size := by
  induction t with
  | edge => simp [Shape.size,Shape.signature,spectra]
  | triangle l r L R =>
    simp only [Shape.size, Shape.signature,spectra,List.mem_flatMap,List.mem_map]
    let i : Fin (l.size+r.size+1) := ⟨l.size,by omega⟩
    exact ⟨i,List.mem_finRange i,l.signature,L,r.signature,by simpa [i] using R,rfl⟩

def lower := 2 * weight 6 + 5 * weight 4 + 5 * weight 2
def upper := weight 8 + 6 * weight 4 + 5 * weight 2
def middle := weight 7 + weight 5 + 5 * weight 4 + 5 * weight 2

/-- The root edge keeps the two end degrees. Gluing the two boundary
paths adds their apex degrees and adds one edge at each outer end. -/
structure Row where
  first : Nat
  inside : List Nat
  last : Nat

def Shape.row : Shape → Row
  | .edge => ⟨1,[],1⟩
  | .triangle l r =>
    let p := l.row
    let q := r.row
    ⟨p.first+1, p.inside ++ [p.last+q.first] ++ q.inside, q.last+1⟩

theorem signature_row (t : Shape) : t.signature =
    ⟨t.row.first,t.row.last,(t.row.inside.map weight).sum⟩ := by
  induction t with
  | edge => rfl
  | triangle l r L R =>
    simp [Shape.signature,join,Shape.row,L,R,Nat.add_comm,Nat.add_assoc]

def Row.vertices (r : Row) := r.first :: r.inside ++ [r.last]

theorem inventory (t : Shape) :
    (t.row.vertices.map weight).sum = t.signature.code := by
  rw [signature_row]
  simp [Row.vertices,Signature.code,Nat.add_left_comm,Nat.add_assoc]

private abbrev e := Shape.edge
private abbrev t := Shape.triangle

def lowWitness := (t e (t (t e e) (t e (t (t e e) (t (t (t e e) (t e e)) e)))))
def highWitness := (t e (t (t e e) (t e (t (t e e) (t e (t (t e e) (t e e)))))))

def lowPolygon : List Nat := [6,6,4,4,4,4,4,2,2,2,2,2]
def highPolygon : List Nat := [8,4,4,4,4,4,4,2,2,2,2,2]
def midPolygon : List Nat := [7,5,4,4,4,4,4,2,2,2,2,2]

theorem endpoint_witnesses :
    lowWitness.size=10 ∧ lowWitness.row.vertices.Perm lowPolygon ∧
    highWitness.size=10 ∧ highWitness.row.vertices.Perm highPolygon := by decide +kernel

/- The inventory is additive, so the negative certificate needs no
assumption about the ordering of vertices along the polygon. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem forbidden_count :
    ((spectra 10).filter (fun s => s.code == middle)).length = 0 := by decide +kernel

theorem excluded (t : Shape) (h : t.size = 10) : t.signature.code ≠ middle := by
  intro eq
  have mem := occurs t
  rw [h] at mem
  have f : t.signature ∈ (spectra 10).filter (fun s => s.code == middle) :=
    List.mem_filter.mpr ⟨mem,by simp [eq]⟩
  have := List.length_pos_of_mem f
  rw [forbidden_count] at this
  omega

theorem no_midpoint_polygon (t : Shape) (ten : t.size=10) :
    ¬ t.row.vertices.Perm midPolygon := by
  intro p
  have h := (p.map weight).sum_eq
  rw [inventory t] at h
  exact excluded t ten (h.trans (by decide))

private def lowCone : List Int := [12,7,7,5,5,5,5,5,3,3,3,3,3]
private def highCone : List Int := [12,9,5,5,5,5,5,5,3,3,3,3,3]
private def midCone : List Int := [12,8,6,5,5,5,5,5,3,3,3,3,3]

/-- Every affine half-space in the sorted entries that contains both
endpoints contains the integer midpoint as well. The weights and
intercept may be arbitrary real numbers (or elements of any ordered field). -/
theorem midpoint_halfspace {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a : Fin 13 → R) (bound : R)
    (low : ∑ i, a i * (lowCone[i.val]! : R) ≤ bound)
    (high : ∑ i, a i * (highCone[i.val]! : R) ≤ bound) :
    ∑ i, a i * (midCone[i.val]! : R) ≤ bound := by
  have coord : ∀ i : Fin 13, midCone[i.val]! + midCone[i.val]! =
      lowCone[i.val]! + highCone[i.val]! := by decide +kernel
  have sumEq : (∑ i, a i * (midCone[i.val]! : R)) + (∑ i, a i * (midCone[i.val]! : R)) =
      (∑ i, a i * (lowCone[i.val]! : R)) + (∑ i, a i * (highCone[i.val]! : R)) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_add,← mul_add,← Int.cast_add,← Int.cast_add,coord]
  by_contra! h
  exact (not_lt_of_ge (sumEq.le.trans (add_le_add low high))) (add_lt_add h h)

end Recognition.PolygonMidpoint
