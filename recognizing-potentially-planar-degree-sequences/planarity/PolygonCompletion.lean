import PolygonGraph
import Mathlib.Data.Nat.Find
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! A noncrossing set of chords extends to a rooted polygon triangulation.
No initial maximality, boundary edges or embedding are required. -/
namespace Recognition.PolygonCompletion
open PolygonMidpoint

/-- Four interlacing ends cannot support both diagonals. Only increasing
pairs are used by the polygon argument. -/
def Noncrossing (E : Nat → Nat → Prop) :=
  ∀ a b c d, a < b → b < c → c < d → E a c → E b d → False

/-- Complete an interval by taking the last proper neighbour of its first
vertex, or the next boundary vertex if there is no such chord. -/
theorem cover_interval (E : Nat → Nat → Prop) (non : Noncrossing E) (a b : Nat) (lt : a < b) :
    ∃ t : Shape, a + t.size + 1 = b ∧
      ∀ u v, a ≤ u → u < v → v ≤ b → E u v → (u,v) ∈ t.edges a := by
  classical
  induction w : b-a using Nat.strong_induction_on generalizing a b with
  | _ w ih =>
    by_cases unit : a+1=b
    · refine ⟨.edge,by simp only [Shape.size]; omega,?_⟩
      intro u v low strict high _
      have eu : u=a := by omega
      have ev : v=a+1 := by omega
      simp [Shape.edges,eu,ev]
    let P := fun i => i=a+1 ∨ E a i
    let x := Nat.findGreatest P (b-1)
    have base : P (a+1) := Or.inl rfl
    have left : a+1 ≤ x := Nat.le_findGreatest (by omega) base
    have right : x < b := Nat.lt_of_le_of_lt (Nat.findGreatest_le _) (by omega)
    have pick : P x := Nat.findGreatest_spec (by omega : a+1≤b-1) base
    obtain ⟨l,ls,lc⟩ := ih (x-a) (by omega) a x (by omega) rfl
    obtain ⟨r,rs,rc⟩ := ih (b-x) (by omega) x b right rfl
    refine ⟨.triangle l r,by simp only [Shape.size]; omega,?_⟩
    intro u v low strict high edge
    have offset : a+1+l.size=x := by omega
    have last : a+2+l.size+r.size=b := by omega
    simp only [Shape.edges,offset,last,List.mem_append,List.mem_singleton,Prod.mk.injEq]
    by_cases onLeft : v ≤ x
    · exact Or.inl (Or.inl (lc u v low strict onLeft edge))
    by_cases onRight : x ≤ u
    · exact Or.inl (Or.inr (rc u v onRight strict high edge))
    by_cases first : u=a
    · subst u
      by_cases final : v=b
      · exact Or.inr ⟨rfl,final⟩
      have maximal := Nat.findGreatest_is_greatest (P := P) (by omega : x<v) (by omega : v≤b-1)
      exact (maximal (Or.inr edge)).elim
    · rcases pick with nxt | chord
      · omega
      · exact (non a u x v (by omega) (by omega) (by omega) chord edge).elim

private theorem edge_count (t : Shape) (a : Nat) : (t.edges a).length = 2*t.size+1 := by
  induction t generalizing a with
  | edge => rfl
  | triangle l r L R => simp only [Shape.edges,List.length_append,List.length_singleton,L,R,Shape.size]; omega

/-- At equality in the polygonal edge bound, the enumerated edge list and
that of a single rooted triangulation are permutations of each other. -/
theorem tight_list (n : Nat) (es : List (Nat × Nat)) (nd : es.Nodup)
    (bound : ∀ p ∈ es, p.1 < p.2 ∧ p.2 ≤ n+1)
    (non : Noncrossing fun x y => (x,y) ∈ es) (count : es.length=2*n+1) :
    ∃ t : Shape, t.size=n ∧ es.Perm (t.edges 0) := by
  obtain ⟨t,size,all⟩ := cover_interval (fun x y => (x,y) ∈ es) non 0 (n+1) (by omega)
  have sz : t.size=n := by omega
  have subset : es ⊆ t.edges 0 := by
    rintro ⟨x,y⟩ eq
    exact all x y (Nat.zero_le _) (bound _ eq).1 (bound _ eq).2 eq
  obtain ⟨l,perm,sub⟩ := List.subperm_iff.mp (nd.subperm subset)
  have eq : es = l := sub.eq_of_length (by rw [perm.length_eq,edge_count,sz,count])
  exact ⟨t,sz,eq ▸ perm⟩

/-- No simple noncrossing 21-edge system on the twelve cyclic labels has
this degree inventory. The input may list the chords in any order. -/
theorem exclude_tight_midpoint (es : List (Nat × Nat)) (nd : es.Nodup)
    (bound : ∀ p ∈ es, p.1 < p.2 ∧ p.2 ≤ 11)
    (non : Noncrossing fun x y => (x,y) ∈ es) (count : es.length=21) :
    ¬ ((List.range 12).map (valence es)).Perm midPolygon := by
  obtain ⟨t,ten,perm⟩ := tight_list 10 es nd bound non count
  have val (i : Nat) : valence es i = valence (t.edges 0) i :=
    (perm.filter _).length_eq
  have row : (List.range 12).map (valence es) = t.row.vertices := by
    rw [List.map_congr_left (fun i _ => val i)]
    simpa only [ten,List.range_eq_range'] using t.degree_row 0
  rw [row]
  exact no_midpoint_polygon t ten

end Recognition.PolygonCompletion
