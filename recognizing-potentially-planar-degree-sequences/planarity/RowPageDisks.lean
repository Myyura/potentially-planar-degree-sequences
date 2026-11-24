import RowPlane
import LeanPool.K5MinorFreeChoosability.Wagner.RotRing

/-! Oriented polygon faces for the two-page construction. Splitting each
spine vertex into two consecutive ports prevents independent triangulations
from producing coincident interior diagonals. -/
namespace Recognition.RowPageDisks
open Recognition.PolygonMidpoint Recognition.RowPlane LeanPool.K5MinorFreeChoosability

structure Triangle where
  a : Nat
  b : Nat
  c : Nat
deriving DecidableEq

def Triangle.sides (t : Triangle) : List (Nat × Nat) := [(t.a,t.b),(t.b,t.c),(t.c,t.a)]

def faces : Shape → Nat → List Triangle
  | .edge, _ => []
  | .triangle l r, a => faces l a ++ faces r (a+1+l.size) ++ [⟨a,a+1+l.size,a+2+l.size+r.size⟩]

@[simp] theorem faces_length (t : Shape) (a : Nat) : (faces t a).length = t.size := by
  induction t generalizing a with
  | edge => rfl
  | triangle l r L R => simp [faces,Shape.size,L,R]; omega

/-- A diagonal contributes both orientations. A unit boundary edge
contributes its increasing orientation. -/
def oriented (e : Nat × Nat) : List (Nat × Nat) :=
  e :: (if e.1+1<e.2 then [e.swap] else [])

/-- The oriented sides of the triangles contain exactly the oriented edge
inventory after restoring the missing forward dart of the root edge. -/
theorem face_inventory (t : Shape) (a : Nat) :
    (((faces t a).flatMap Triangle.sides) ++ [(a,a+t.size+1)]).Perm ((t.edges a).flatMap oriented) := by
  induction t generalizing a with
  | edge => simp [faces, Shape.size, Shape.edges, oriented]
  | triangle l r L R =>
    let m := a+1+l.size
    let z := a+2+l.size+r.size
    have mid : a+l.size+1=m := by dsimp [m]; omega
    have right : m+r.size+1=z := by dsimp [m,z]; omega
    have root : a+(Shape.triangle l r).size+1=z := by simp [Shape.size,z]; omega
    have long : a+1<z := by dsimp [z]; omega
    have split : (Shape.triangle l r).edges a = l.edges a ++ r.edges m ++ [(a,z)] := rfl
    have triangles : faces (.triangle l r) a = faces l a ++ faces r m ++ [⟨a,m,z⟩] := rfl
    rw [List.perm_iff_count]
    intro p
    have lc := List.perm_iff_count.mp (L a) p
    have rc := List.perm_iff_count.mp (R m) p
    simp only [List.count_append,mid,right] at lc rc
    rw [split,triangles,root]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.count_append, Triangle.sides]
    have rootDarts : oriented (a,z) = [(a,z),(z,a)] := by simp [oriented,long]
    rw [rootDarts]
    simp only [List.count_cons, List.count_nil] at *
    omega

/-- For each ordered side of a triangle the reverse is a legal dual
adjacency if it occurs on another face. -/
def Across (p q : Triangle) : Prop := ∃ i j, (i,j) ∈ p.sides ∧ (j,i) ∈ q.sides

def FaceStep (mesh : List Triangle) (p q : Triangle) : Prop :=
  p ∈ mesh ∧ q ∈ mesh ∧ Across p q

private theorem facePath_mono {left right : List Triangle} (h : left ⊆ right) {p q}
    (path : Relation.ReflTransGen (FaceStep left) p q) : Relation.ReflTransGen (FaceStep right) p q := by
  induction path with
  | refl => exact .refl
  | tail prev e ih => exact ih.tail ⟨h e.1,h e.2.1,e.2.2⟩

private theorem root_face {t : Shape} {a : Nat} (nonempty : faces t a ≠ []) :
    ∃ p ∈ faces t a, (a+t.size+1,a) ∈ p.sides := by
  cases t with
  | edge => simp [faces] at nonempty
  | triangle l r =>
    let m := a+1+l.size
    let z := a+2+l.size+r.size
    refine ⟨⟨a,m,z⟩, by simp [faces,m,z], ?_⟩
    have top : a+(Shape.triangle l r).size+1=z := by simp [Shape.size,z]; omega
    simp [Triangle.sides,top]

/-- The triangles of each filled polygon form a connected dual graph,
with every step witnessed by oppositely oriented sides. -/
theorem disk_connected (t : Shape) (a : Nat) {p q : Triangle} (hp : p ∈ faces t a)
    (hq : q ∈ faces t a) : Relation.ReflTransGen (FaceStep (faces t a)) p q := by
  induction t generalizing a p q with
  | edge => simp [faces] at hp
  | triangle l r L R =>
    let m := a+1+l.size
    let z := a+2+l.size+r.size
    let apex : Triangle := ⟨a,m,z⟩
    let all := faces (.triangle l r) a
    have split : all = faces l a ++ faces r m ++ [apex] := rfl
    have left : faces l a ⊆ all := fun _ mem => by simp [split,mem]
    have right : faces r m ⊆ all := fun _ mem => by simp [split,mem]
    have root : apex ∈ all := by simp [split]
    have path {u} (inRows : u∈all) : Relation.ReflTransGen (FaceStep all) u apex := by
      rw [split, List.mem_append, List.mem_append, List.mem_singleton] at inRows
      rcases inRows with (inL|inR)|rfl
      · obtain ⟨k,hk,side⟩ := root_face (List.ne_nil_of_mem inL)
        have perm := facePath_mono left (L a inL hk)
        apply perm.tail
        refine ⟨left hk,root, a+l.size+1,a,side,?_⟩
        have pivot : a+l.size+1=m := by dsimp [m]; omega
        simp [apex,Triangle.sides,pivot]
      · obtain ⟨k,hk,side⟩ := root_face (List.ne_nil_of_mem inR)
        have perm := facePath_mono right (R m inR hk)
        apply perm.tail
        refine ⟨right hk,root, m+r.size+1,m,side,?_⟩
        have pivot : m+r.size+1=z := by dsimp [m,z]; omega
        simp [apex,Triangle.sides,pivot]
      · exact .refl
    have symm {x y} (adj : FaceStep all x y) : FaceStep all y x := by
      obtain ⟨h1,h2,i,j,one,two⟩ := adj
      exact ⟨h2,h1,j,i,two,one⟩
    have back {x y} (h : Relation.ReflTransGen (FaceStep all) x y) : Relation.ReflTransGen (FaceStep all) y x := by
      induction h with
      | refl => exact .refl
      | tail _ step ih => exact Relation.ReflTransGen.head (symm step) ih
    exact (path hp).trans (back (path hq))

/-- All unit sides appear in the perimeter, including those incident on
the split point of a nontrivial binary polygon. -/
theorem boundary_edges (t : Shape) (a i : Nat) (lo : a ≤ i) (hi : i < a+t.size+1) :
    (i,i+1) ∈ t.edges a := by
  induction t generalizing a with
  | edge => have e : i=a := by simp [Shape.size] at hi; omega
            simp [Shape.edges,e]
  | triangle l r L R =>
    have top : a+(Shape.triangle l r).size+1 = (a+1+l.size)+r.size+1 := by simp [Shape.size]; omega
    rw [top] at hi
    by_cases front : i < a+1+l.size
    · have m := L a lo (by omega)
      simp [Shape.edges,m]
    · have m := R (a+1+l.size) (by omega) hi
      simp [Shape.edges,m]

/-- Sorted polygon edges never repeat. In the recursive split, edges on
the two sides have disjoint interiors, and neither side contains the root. -/
theorem edges_nodup (t : Shape) (a : Nat) : (t.edges a).Nodup := by
  induction t generalizing a with
  | edge => simp [Shape.edges]
  | triangle l r L R =>
    let m := a+1+l.size
    let z := a+2+l.size+r.size
    change (l.edges a ++ r.edges m ++ [(a,z)]).Nodup
    rw [List.nodup_append', List.nodup_append']
    refine ⟨⟨L a,R m,?_⟩,by simp,?_⟩
    · intro e h1 h2
      obtain ⟨u,v⟩ := e
      have one := l.edge_bounds a h1
      have two := r.edge_bounds m h2
      dsimp [m] at two
      omega
    · intro e inPage root
      obtain rfl : e=(a,z) := List.mem_singleton.mp root
      rcases List.mem_append.mp inPage with left|right
      · have one := l.edge_bounds a left
        dsimp [z] at one
        omega
      · have two := r.edge_bounds m right
        dsimp [m] at two
        omega

private def missingUnit (e : Nat × Nat) := if e.1+1=e.2 then [e.swap] else []

private theorem missing_units (t : Shape) (a : Nat) :
    (t.edges a).flatMap missingUnit = (List.range' a (t.size+1)).map (fun i => (i+1,i)) := by
  induction t generalizing a with
  | edge => simp [Shape.edges,Shape.size,missingUnit,List.range']
  | triangle l r L R =>
    let m := a+1+l.size
    let z := a+2+l.size+r.size
    have long : a+1≠z := by dsimp [z]; omega
    have split : (Shape.triangle l r).edges a = l.edges a ++ r.edges m ++ [(a,z)] := rfl
    rw [split]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,L,R]
    have none : missingUnit (a,z) = [] := by simp [missingUnit,long]
    rw [none, List.append_nil, ←List.map_append]
    congr 1
    simp [m, Shape.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Cap the root by its forward dart and each unit side by its reverse.
Then every undirected polygon edge appears in both directions exactly once. -/
theorem disk_edge_pairs (t : Shape) (a : Nat) :
    (((faces t a).flatMap Triangle.sides ++ [(a,a+t.size+1)]) ++
      (List.range' a (t.size+1)).map (fun i => (i+1,i))).Perm
      ((t.edges a).flatMap (fun e => [e,e.swap])) := by
  rw [← missing_units]
  apply ((face_inventory t a).append_right _).trans
  apply (List.flatMap_append_perm (t.edges a) oriented missingUnit).trans
  apply List.Perm.of_eq
  apply List.flatMap_congr
  rintro ⟨u,v⟩ hit
  have bound := t.edge_bounds a hit
  by_cases unit : u+1=v
  · simp [oriented,missingUnit,unit]
  · simp [oriented,missingUnit,unit, show u+1<v by omega]

/-- An edge within either of two lifted polygons joins ports of the same
parity. Distinct pages have no common such edge, including new diagonals. -/
def liftEdge (page : Nat) (e : Nat × Nat) : Nat × Nat := (2*e.1+page,2*e.2+page)

theorem disjoint_diagonals (s t : Shape) (a b : Nat) :
    (s.edges a).map (liftEdge 0) |>.Disjoint ((t.edges b).map (liftEdge 1)) := by
  intro p low high
  obtain ⟨⟨u,v⟩,_,one⟩ := List.mem_map.mp low
  obtain ⟨⟨x,y⟩,_,two⟩ := List.mem_map.mp high
  have same := congrArg Prod.fst (one.trans two.symm)
  simp only [liftEdge] at same
  omega

/-- A boundary vertex with label `i` has an even and an odd copy. -/
def port (i side : Nat) := 2*i+side

def Triangle.lift (side : Nat) (reverse : Bool) (f : Triangle) : Triangle :=
  if reverse then ⟨port f.a side,port f.c side,port f.b side⟩
  else ⟨port f.a side,port f.b side,port f.c side⟩

private theorem lifted_side {i j : Nat} {f : Triangle} (side : Nat) (rev : Bool)
    (s : (i,j)∈f.sides) :
    (if rev then (port j side,port i side) else (port i side,port j side))∈(f.lift side rev).sides := by
  rcases f with ⟨a,b,c⟩
  simp only [Triangle.sides, List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at s
  rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases rev <;> simp [Triangle.sides,Triangle.lift]

private theorem across_lift {f g : Triangle} (p : Nat) (rev : Bool) (h : Across f g) :
    Across (f.lift p rev) (g.lift p rev) := by
  obtain ⟨i,j,h1,h2⟩ := h
  cases rev
  · exact ⟨_,_,lifted_side p false h1,lifted_side p false h2⟩
  · exact ⟨_,_,lifted_side p true h1,lifted_side p true h2⟩

private theorem lift_path (page : Nat) (rev : Bool) {mesh : List Triangle} {x y : Triangle}
    (p : Relation.ReflTransGen (FaceStep mesh) x y) :
    Relation.ReflTransGen (FaceStep (mesh.map (Triangle.lift page rev))) (x.lift page rev) (y.lift page rev) := by
  induction p with
  | refl => exact .refl
  | tail prev step ih => exact ih.tail ⟨List.mem_map_of_mem step.1,List.mem_map_of_mem step.2.1,
      across_lift page rev step.2.2⟩

def next (n i : Nat) := (i+1)%n

def leftEar (n i : Nat) : Triangle := ⟨port i 0,port i 1,port (next n i) 0⟩

def rightEar (n i : Nat) : Triangle := ⟨port i 1,port (next n i) 1,port (next n i) 0⟩

/-- Disjoint copies of the two disks and the explicitly triangulated
annulus between their boundary cycles; the second disk is reversed. -/
def doubled (s t : Shape) : List Triangle :=
  let n := s.size+2
  (faces s 0).map (Triangle.lift 0 false) ++ (faces t 0).map (Triangle.lift 1 true) ++
    (List.range n).map (leftEar n) ++ (List.range n).map (rightEar n)

/-- The doubled mesh has the Euler face count for twice as many vertices. -/
theorem doubled_euler (s t : Shape) (eq : s.size=t.size) : (doubled s t).length + 4 = 2*(2*(s.size+2)) := by
  simp only [doubled,List.length_append,List.length_map,List.length_range,faces_length]
  omega

private theorem back_path {mesh : List Triangle} {x y : Triangle}
    (h : Relation.ReflTransGen (FaceStep mesh) x y) : Relation.ReflTransGen (FaceStep mesh) y x := by
  induction h with
  | refl => exact .refl
  | tail _ e ih =>
    obtain ⟨h1,h2,i,j,a,b⟩ := e
    exact Relation.ReflTransGen.head ⟨h2,h1,j,i,b,a⟩ ih

/-- Every two faces of the explicitly doubled mesh are connected across
oppositely oriented sides, including the seam between the two disks. -/
theorem doubled_connected (s t : Shape) (eq : s.size=t.size) {f g : Triangle}
    (hf : f∈doubled s t) (hg : g∈doubled s t) : Relation.ReflTransGen (FaceStep (doubled s t)) f g := by
  let n := s.size+2
  let mesh := doubled s t
  have np : 0<n := by dsimp [n]; omega
  have last : next n (n-1)=0 := by rw [next,Nat.sub_add_cancel (by omega),Nat.mod_self]
  have left (i) (hi : i<n) : leftEar n i∈mesh := by
    simp only [mesh,doubled,List.mem_append]; exact .inl (.inr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))
  have right (i) (hi : i<n) : rightEar n i∈mesh := by
    simp only [mesh,doubled,List.mem_append]; exact .inr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  have across (i) (hi : i<n) : FaceStep mesh (leftEar n i) (rightEar n i) := by
    refine ⟨left _ hi,right _ hi,port i 1,port (next n i) 0,?_,?_⟩ <;> simp [leftEar,rightEar,Triangle.sides]
  have rise (i) (hi : i<n) : FaceStep mesh (rightEar n i) (leftEar n (next n i)) := by
    refine ⟨right _ hi,left _ (Nat.mod_lt _ np),port (next n i) 1,port (next n i) 0,?_,?_⟩ <;>
      simp [leftEar,rightEar,Triangle.sides]
  have along (i) (hi : i<n) : Relation.ReflTransGen (FaceStep mesh) (leftEar n 0) (leftEar n i) := by
    induction i with
    | zero => exact .refl
    | succ i ih =>
      have hp : i<n := by omega
      have path := ((ih hp).tail (across _ hp)).tail (rise _ hp)
      simpa [next,Nat.mod_eq_of_lt hi] using path
  have reach {u} (hu : u∈mesh) : Relation.ReflTransGen (FaceStep mesh) (leftEar n 0) u := by
    change u∈doubled s t at hu
    simp only [doubled,List.mem_append,List.mem_map,List.mem_range] at hu
    rcases hu with ((⟨v,hv,rfl⟩|⟨v,hv,rfl⟩)|⟨i,hi,rfl⟩)|⟨i,hi,rfl⟩
    · obtain ⟨k,hk,side⟩ := root_face (List.ne_nil_of_mem hv)
      have tail : 0+s.size+1=n-1 := by dsimp [n]; omega
      rw [tail] at side
      have sub : (faces s 0).map (Triangle.lift 0 false) ⊆ mesh := fun _ h => by simp [mesh,doubled,h]
      have attach : FaceStep mesh (k.lift 0 false) (leftEar n (n-1)) := by
        refine ⟨sub (List.mem_map_of_mem hk),left _ (by omega),_,_,lifted_side 0 false side,?_⟩
        simp [leftEar,Triangle.sides,last]
      exact ((along _ (by omega)).trans (back_path (Relation.ReflTransGen.single attach))).trans
        (facePath_mono sub (lift_path 0 false (disk_connected s 0 hk hv)))
    · obtain ⟨k,hk,side⟩ := root_face (List.ne_nil_of_mem hv)
      have tail : 0+t.size+1=n-1 := by dsimp [n]; omega
      rw [tail] at side
      have sub : (faces t 0).map (Triangle.lift 1 true) ⊆ mesh := fun _ h => by simp [mesh,doubled,h]
      have attach : FaceStep mesh (k.lift 1 true) (rightEar n (n-1)) := by
        refine ⟨sub (List.mem_map_of_mem hk),right _ (by omega),_,_,lifted_side 1 true side,?_⟩
        simp [rightEar,Triangle.sides,last]
      exact (((along _ (by omega)).tail (across _ (by omega))).trans (back_path (Relation.ReflTransGen.single attach))).trans
        (facePath_mono sub (lift_path 1 true (disk_connected t 0 hk hv)))
    · exact along i hi
    · exact (along i hi).tail (across i hi)
  exact (back_path (reach hf)).trans (reach hg)

private def dartPair (e : Nat × Nat) := [e,e.swap]

private def mapDart (side : Nat) (rev : Bool) (e : Nat × Nat) : Nat × Nat :=
  let p := liftEdge side e
  if rev then p.swap else p

private theorem triangle_map_sides (side : Nat) (rev : Bool) (f : Triangle) :
    (f.lift side rev).sides.Perm (f.sides.map (mapDart side rev)) := by
  cases rev with
  | false => rfl
  | true =>
    rw [show (Triangle.lift side true f).sides=(f.sides.map (mapDart side true)).reverse from rfl]
    exact List.reverse_perm _

private theorem disk_map_sides (side : Nat) (rev : Bool) (fs : List Triangle) :
    ((fs.map (Triangle.lift side rev)).flatMap Triangle.sides).Perm ((fs.flatMap Triangle.sides).map (mapDart side rev)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simpa only [List.map_cons,List.flatMap_cons,List.map_append] using
      (triangle_map_sides side rev f).append ih

private theorem symmetric_mapping (side : Nat) (rev : Bool) (es : List (Nat × Nat)) :
    ((es.flatMap dartPair).map (mapDart side rev)).Perm ((es.map (liftEdge side)).flatMap dartPair) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_cons]
    apply List.Perm.append _ ih
    cases rev with
    | false => rfl
    | true => exact List.Perm.swap ..

private def cap (n i : Nat) := (next n i,i)

private theorem cyclic_caps (t : Shape) :
    ((List.range (t.size+2)).map (cap (t.size+2))).Perm
      ([(0,t.size+1)] ++ (List.range' 0 (t.size+1)).map (fun i => (i+1,i))) := by
  let n := t.size+2
  have capEnd : cap n (t.size+1) = (0,t.size+1) := by simp [cap,next,n]
  rw [List.range_succ, List.map_append]
  change (_ ++ [cap n (t.size+1)]).Perm _
  rw [capEnd, List.range_eq_range']
  have all : (List.range' 0 (t.size+1)).map (cap n) = (List.range' 0 (t.size+1)).map (fun i => (i+1,i)) := by
    apply List.map_congr_left
    intro i mem
    have lt : i < t.size+1 := by simpa [←List.range_eq_range'] using mem
    simp [cap,next,Nat.mod_eq_of_lt (show i+1<n by dsimp [n]; omega)]
  rw [all]
  exact List.perm_append_comm

private theorem all_caps (t : Shape) (side : Nat) (rev : Bool) :
    (((faces t 0).map (Triangle.lift side rev)).flatMap Triangle.sides ++
     (List.range (t.size+2)).map (fun i => mapDart side rev (cap (t.size+2) i))).Perm
      (((t.edges 0).map (liftEdge side)).flatMap dartPair) := by
  have left := disk_map_sides side rev (faces t 0)
  have right := (cyclic_caps t).map (mapDart side rev)
  rw [List.map_map] at right
  apply (left.append right).trans
  rw [← List.map_append]
  have pairs := (disk_edge_pairs t 0).map (mapDart side rev)
  simp only [Nat.zero_add,List.append_assoc] at pairs
  exact pairs.trans (symmetric_mapping side rev (t.edges 0))

private def nearRung (i : Nat) := (port i 0,port i 1)
private def farRung (n i : Nat) := (port i 1,port (next n i) 0)

private theorem three_columns (xs : List α) (A B C : α → β) :
    (xs.flatMap (fun i => [A i,B i,C i])).Perm ((xs.map A ++ xs.map B) ++ xs.map C) := by
  classical
  rw [List.perm_iff_count]
  intro x
  induction xs with
  | nil => simp
  | cons z zs ih =>
    simp only [List.flatMap_cons,List.map_cons,List.count_append,List.count_cons,List.count_nil] at *
    omega

private theorem cycles_range (n : Nat) (np : 0<n) : ((List.range n).map (next n)).Perm (List.range n) := by
  have bounds {i} (m : i∈List.range n) : next n i = (if i+1=n then 0 else i+1) := by
    have small := List.mem_range.mp m
    by_cases eq : i+1=n
    · simp [next,eq]
    · simp [next,eq,Nat.mod_eq_of_lt (by omega : i+1<n)]
  have nodup : ((List.range n).map (next n)).Nodup := by
    apply (List.nodup_range (n:=n)).map_on
    intro a ha b hb eq
    rw [bounds ha,bounds hb] at eq
    split at eq <;> split at eq <;> omega
  apply (List.perm_ext_iff_of_nodup nodup List.nodup_range).mpr
  intro i
  constructor
  · rintro m
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp m
    exact List.mem_range.mpr (Nat.mod_lt _ np)
  · intro mem
    have lt := List.mem_range.mp mem
    cases i with
    | zero => exact List.mem_map.mpr ⟨n-1,List.mem_range.mpr (by omega),by simp [next,Nat.sub_add_cancel (by omega : 1≤n)]⟩
    | succ i => exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by omega),Nat.mod_eq_of_lt lt⟩

/-- The full edge list of the two lids and the equatorial band. It stores
one representative per edge, with a consistent side assigned by parity. -/
def doubledEdges (s t : Shape) :=
  let n := s.size+2
  (s.edges 0).map (liftEdge 0) ++ (t.edges 0).map (liftEdge 1) ++
    (List.range n).map nearRung ++ (List.range n).map (farRung n)

/-- Every directed side of the doubled sphere occurs together with its
reverse, with the exact multiplicity of the indicated edge list. -/
theorem doubled_darts (s t : Shape) (eq : s.size=t.size) :
    ((doubled s t).flatMap Triangle.sides).Perm ((doubledEdges s t).flatMap dartPair) := by
  let n := s.size+2
  let idx := List.range n
  let capA := fun i => mapDart 0 false (cap n i)
  let capB := fun i => mapDart 1 true (cap n i)
  have left := all_caps s 0 false
  have right := all_caps t 1 true
  rw [←eq] at right
  have leftEars : ((idx.map (leftEar n)).flatMap Triangle.sides).Perm
      ((idx.map nearRung ++ idx.map (farRung n)) ++ idx.map capA) := by
    rw [List.flatMap_map]; exact three_columns idx nearRung (farRung n) capA
  have rightEars : ((idx.map (rightEar n)).flatMap Triangle.sides).Perm
      ((idx.map capB ++ idx.map (fun i => (nearRung (next n i)).swap)) ++ idx.map (fun i => (farRung n i).swap)) := by
    rw [List.flatMap_map]
    exact three_columns idx capB (fun i => (nearRung (next n i)).swap) (fun i => (farRung n i).swap)
  have shift := (cycles_range n (by dsimp [n]; omega)).map (fun i => (nearRung i).swap)
  rw [List.map_map] at shift
  have pairCount (xs : List (Nat × Nat)) (e : Nat × Nat) :
      (xs.flatMap dartPair).count e = xs.count e + (xs.map Prod.swap).count e := by
    induction xs with
    | nil => simp
    | cons x xs IH => simp only [List.flatMap_cons,List.count_append,dartPair,List.count_cons,List.count_nil,
        List.map_cons,IH]; omega
  rw [List.perm_iff_count]
  intro e
  have A := List.perm_iff_count.mp left e
  have B := List.perm_iff_count.mp right e
  have C := List.perm_iff_count.mp leftEars e
  have D := List.perm_iff_count.mp rightEars e
  have E := List.perm_iff_count.mp shift e
  have F := pairCount (idx.map nearRung) e
  have K := pairCount (idx.map (farRung n)) e
  change (((faces s 0).map _ ++ (faces t 0).map _ ++ idx.map _ ++ idx.map _).flatMap Triangle.sides).count e = _
  change _ = (((s.edges 0).map _ ++ (t.edges 0).map _ ++ idx.map _ ++ idx.map _).flatMap dartPair).count e
  change ((List.flatMap Triangle.sides ((faces s 0).map _) ++ idx.map capA).count e) = _ at A
  change ((List.flatMap Triangle.sides ((faces t 0).map _) ++ idx.map capB).count e) = _ at B
  simp only [List.flatMap_append,List.count_append,List.map_map,Function.comp_def,idx,n] at A B C D E F K ⊢
  omega

private theorem next_ne {n i : Nat} (two : 2≤n) (lt : i<n) : next n i ≠ i := by
  by_cases last : i+1=n
  · simp [next,last]; omega
  · rw [next,Nat.mod_eq_of_lt (by omega : i+1<n)]; omega

private theorem pair_unique {es : List (Nat × Nat)} (nd : es.Nodup)
    (separate : ∀ e ∈ es, e.1≠e.2 ∧ e.swap ∉ es) : (es.flatMap dartPair).Nodup := by
  induction es with
  | nil => simp
  | cons a l ih =>
    have n := List.nodup_cons.mp nd
    have pair := separate a (.head _)
    rw [List.flatMap_cons, List.nodup_append']
    refine ⟨?_, ih n.2 (fun e h => ⟨(separate e (.tail _ h)).1,fun bad => (separate e (.tail _ h)).2 (.tail _ bad)⟩), ?_⟩
    · have diff : a≠a.swap := fun eq => pair.1 (congrArg Prod.fst eq)
      simp [dartPair,diff]
    · intro e ha hl
      obtain ⟨b,hb,hside⟩ := List.mem_flatMap.mp hl
      have diff := (separate b (.tail _ hb)).2
      simp only [dartPair,List.mem_cons,List.not_mem_nil,or_false] at ha hside
      rcases ha with rfl|rfl <;> rcases hside with same|other
      · exact n.1 (same.symm ▸ hb)
      · exact diff (List.mem_cons.mpr (.inl other.symm))
      · exact pair.2 (List.mem_cons.mpr (.inr (same.symm ▸ hb)))
      · have eq : a=b := by simpa using congrArg Prod.swap other
        exact n.1 (eq.symm ▸ hb)

private inductive EdgeType (n : Nat) : (Nat × Nat) → Prop where
  | left (i j) : i<j → j<n → EdgeType n (2*i,2*j)
  | right (i j) : i<j → j<n → EdgeType n (2*i+1,2*j+1)
  | near (i) : i<n → EdgeType n (2*i,2*i+1)
  | far (i) : i<n → EdgeType n (2*i+1,2*(next n i))

private theorem edge_type (s t : Shape) (eq : s.size=t.size) {e} (hit : e∈doubledEdges s t) : EdgeType (s.size+2) e := by
  simp only [doubledEdges,List.mem_append,List.mem_map,List.mem_range] at hit
  rcases hit with ((⟨⟨i,j⟩,h,rfl⟩|⟨⟨i,j⟩,h,rfl⟩)|⟨i,h,rfl⟩)|⟨i,h,rfl⟩
  · have sz := s.edge_bounds 0 h
    exact .left i j sz.2.1 (by omega)
  · have sz := t.edge_bounds 0 h
    exact .right i j sz.2.1 (by omega)
  · exact .near i h
  · exact .far i h

private theorem incompatible {n : Nat} (two : 2≤n) {p q : Nat × Nat} (hp : EdgeType n p) (hq : EdgeType n q) :
    p.1≠p.2 ∧ p.swap≠q := by
  constructor
  · cases hp <;> dsimp <;> omega
  · cases hp <;> cases hq <;> intro eq <;> simp only [Prod.swap, Prod.mk.injEq] at eq <;>
      first | omega | grind [next_ne (n:=n) two]

private theorem doubledEdges_nodup (s t : Shape) : (doubledEdges s t).Nodup := by
  let n := s.size+2
  have one (p : Nat) : Function.Injective (liftEdge p) := by
    rintro ⟨i,j⟩ ⟨x,y⟩ eq
    simp only [liftEdge,Prod.mk.injEq] at eq ⊢; omega
  have near : Function.Injective nearRung := by
    intro i j eq; have := congrArg Prod.fst eq; dsimp [nearRung,port] at this; omega
  have far : Function.Injective (farRung n) := by
    intro i j eq; have := congrArg Prod.fst eq; dsimp [farRung,port] at this; omega
  unfold doubledEdges
  rw [List.nodup_append',List.nodup_append',List.nodup_append']
  refine ⟨⟨⟨(edges_nodup ..).map (one 0),(edges_nodup ..).map (one 1),?_⟩,List.nodup_range.map near,?_⟩,
    List.nodup_range.map far,?_⟩
  · rintro e h1 h2
    obtain ⟨⟨i,j⟩,_,eq⟩ := List.mem_map.mp h1
    obtain ⟨⟨x,y⟩,_,eq'⟩ := List.mem_map.mp h2
    have h := congrArg Prod.fst (eq.trans eq'.symm); dsimp [liftEdge] at h; omega
  · intro e h1 h2
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp h2
    rcases List.mem_append.mp h1 with h|h <;> obtain ⟨⟨i,j⟩,_,eq⟩ := List.mem_map.mp h <;>
      simp only [liftEdge,nearRung,port,Prod.mk.injEq] at eq <;> omega
  · intro e h1 h2
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp h2
    rcases List.mem_append.mp h1 with h|h
    · rcases List.mem_append.mp h with h|h <;> obtain ⟨⟨i,j⟩,_,eq⟩ := List.mem_map.mp h <;>
        simp only [liftEdge,farRung,port,Prod.mk.injEq] at eq <;> omega
    · obtain ⟨i,_,eq⟩ := List.mem_map.mp h
      have x := congrArg Prod.fst eq; dsimp [nearRung,farRung,port] at x; omega

/-- There are no loops or repeated directed incidences in the completed
sphere. Opposite faces meet their common edge in opposite directions. -/
theorem doubled_darts_nodup (s t : Shape) (eq : s.size=t.size) : ((doubled s t).flatMap Triangle.sides).Nodup := by
  apply (doubled_darts s t eq).nodup_iff.mpr
  refine pair_unique (doubledEdges_nodup ..) (fun e h => ?_)
  have tag := edge_type s t eq h
  have two : 2≤s.size+2 := by omega
  exact ⟨(incompatible two tag tag).1, fun rev => (incompatible two tag (edge_type s t eq rev)).2 rfl⟩

/-- The dart list uses each undirected edge of the closed mesh in both
directions. -/
theorem doubled_side_iff (s t : Shape) (eq : s.size=t.size) (e : Nat × Nat) :
    e∈(doubled s t).flatMap Triangle.sides ↔ e∈doubledEdges s t ∨ e.swap∈doubledEdges s t := by
  rw [(doubled_darts s t eq).mem_iff,List.mem_flatMap]
  constructor
  · rintro ⟨q,hq,h⟩
    simp only [dartPair,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact .inl hq
    · simpa using Or.inr (a:=q.swap∈doubledEdges s t) hq
  · rintro (h|h)
    · exact ⟨e,h,by simp [dartPair]⟩
    · exact ⟨e.swap,h,by simp [dartPair]⟩

/-- All sides of the closed mesh have distinct endpoints and use no
labels beyond the two copies of the common spine. -/
theorem doubled_bounds (s t : Shape) (eq : s.size=t.size) {e : Nat × Nat}
    (h : e∈(doubled s t).flatMap Triangle.sides) : e.1<2*(s.size+2) ∧ e.2<2*(s.size+2) ∧ e.1≠e.2 := by
  let n := s.size+2
  have two : 2≤n := by dsimp [n]; omega
  have safe {p : Nat × Nat} (tag : EdgeType n p) : p.1<2*n ∧ p.2<2*n ∧ p.1≠p.2 := by
    have diff := (incompatible two tag tag).1
    cases tag with
    | left i j _ _ => dsimp; omega
    | right i j _ _ => dsimp; omega
    | near i _ => dsimp; omega
    | far i _ => have q := Nat.mod_lt (i+1) (by omega : n>0)
                 dsimp [next]; omega
  rcases (doubled_side_iff s t eq e).mp h with yes|yes
  · exact safe (edge_type s t eq yes)
  · have rev := safe (edge_type s t eq yes)
    exact ⟨rev.2.1,rev.1,rev.2.2.symm⟩

/-- The edge joining each pair of copies on the boundary is present. -/
theorem boundary_pair (s t : Shape) {i : Nat} (hi : i<s.size+2) :
    (port i 0,port i 1)∈doubledEdges s t := by
  unfold doubledEdges
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))

theorem doubled_used (s t : Shape) (eq : s.size=t.size) (v : Fin (2*(s.size+2))) :
    ∃ y, (v.val,y)∈(doubled s t).flatMap Triangle.sides := by
  let i := v.val/2
  have small : i<s.size+2 := by dsimp [i]; omega
  have p := boundary_pair s t small
  rcases (show v.val = 2*i ∨ v.val=2*i+1 by dsimp [i]; omega) with even|odd
  · exact ⟨port i 1,(doubled_side_iff s t eq _).mpr (.inl (by simpa [even,port] using p))⟩
  · exact ⟨port i 0,(doubled_side_iff s t eq _).mpr (.inr (by simpa [odd,port] using p))⟩

/-- Any two graphs on the same labels arise as a minor of two disjoint
copies joined by a matching. Extra edges in the host are allowed. -/
noncomputable def matchingMinor {V : Type*} (A B : SimpleGraph V) (H : SimpleGraph (V × Bool))
    (pairs : ∀ v, H.Adj (v,false) (v,true))
    (low : ∀ x y, A.Adj x y → H.Adj (x,false) (y,false))
    (high : ∀ x y, B.Adj x y → H.Adj (x,true) (y,true)) : MinorModel H (A ⊔ B) := by
  classical
  let P (v : V) : Finset (V × Bool) := {(v,false),(v,true)}
  refine ⟨P, fun v => ⟨(v,false),by simp [P]⟩, ?_, ?_, ?_⟩
  · intro v
    rw [← connSet_iff_induce_connected]
    have touch : Touch H {(v,false)} {(v,true)} :=
      ⟨_,Finset.mem_singleton_self _,_,Finset.mem_singleton_self _,pairs v⟩
    have joined := ConnSet.union_touch (connSet_finset_singleton (v,false)) (connSet_finset_singleton (v,true)) touch
    simpa [P] using joined
  · intro x y ne
    apply Finset.disjoint_left.mpr
    intro z hx hy
    have key {v} (mem : z∈P v) : z.1=v := by
      simp only [P,Finset.mem_insert,Finset.mem_singleton] at mem
      rcases mem with rfl|rfl <;> rfl
    exact ne ((key hx).symm.trans (key hy))
  · intro x y edge
    rcases edge with l|h
    · exact ⟨(x,false),by simp [P],(y,false),by simp [P],low x y l⟩
    · exact ⟨(x,true),by simp [P],(y,true),by simp [P],high x y h⟩

end Recognition.RowPageDisks
