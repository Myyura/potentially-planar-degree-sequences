import RowPageDisks
import SphereRotation

/-! Turn an explicitly assembled, oriented triangle list into a sphere
rotation on its actual simple graph, with the two directions of every
edge checked as darts. -/
namespace Recognition.RowSphere
open Recognition.RowPlane Recognition.RowPageDisks Recognition.PolygonMidpoint
open LeanPool.K5MinorFreeChoosability PlanarDegrees.Frontier

abbrev darts (rows : List Triangle) := rows.flatMap Triangle.sides

def graph (n : Nat) (rows : List Triangle) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ((x.val,y.val) ∈ darts rows ∨ (y.val,x.val) ∈ darts rows)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private def corner (T : Triangle) : Fin 3 → Nat := ![T.a,T.b,T.c]

private theorem side_iff (T : Triangle) (a b : Nat) : (a,b)∈T.sides ↔
    ∃ k : Fin 3, corner T k=a ∧ corner T (k+1)=b := by
  constructor
  · intro e
    simp only [Triangle.sides,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at e
    rcases e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨0,rfl,rfl⟩
    · exact ⟨1,rfl,rfl⟩
    · exact ⟨2,rfl,rfl⟩
  · rintro ⟨k,rfl,rfl⟩
    fin_cases k <;> simp [corner,Triangle.sides]

private theorem dlength (fs : List Triangle) : (darts fs).length = 3 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [darts,List.flatMap_cons,List.length_append,List.length_cons] at *
    change 3 + (List.flatMap Triangle.sides fs).length = _
    omega

/-- Every hypothesis is a check on the triangle list. The underlying
graph is recovered from that list and carries no embedding assumption. -/
theorem list_plane (n F : Nat) (rows : List Triangle) (length : rows.length=F+1)
    (bounds : ∀ e∈darts rows, e.1<n ∧ e.2<n ∧ e.1≠e.2)
    (twins : ∀ e∈darts rows, e.swap∈darts rows) (nodup : (darts rows).Nodup)
    (used : ∀ x : Fin n, ∃ y, (x.val,y)∈darts rows)
    (connected : ∀ a∈rows, ∀ b∈rows, Relation.ReflTransGen (FaceStep rows) a b)
    (count : rows.length+4=2*n) : IsPlanar (graph n rows) := by
  classical
  let H := graph n rows
  let row (i : Fin (F+1)) := rows[i.val]'(by omega)
  have rows_mem (i) : row i∈rows := List.getElem_mem ..
  let raw (p : Fin (F+1) × Fin 3) := (corner (row p.1) p.2, corner (row p.1) (p.2+1))
  have stored (p) : raw p∈darts rows := List.mem_flatMap.mpr
    ⟨row p.1,rows_mem _, (side_iff ..).mpr ⟨p.2,rfl,rfl⟩⟩
  have covers (e : Nat × Nat) (hit : e∈darts rows) : ∃ p, raw p=e := by
    obtain ⟨f,inRows,hSide⟩ := List.mem_flatMap.mp hit
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem inRows
    obtain ⟨k, A, B⟩ := (side_iff f e.1 e.2).mp hSide
    let idx : Fin (F+1) := ⟨i,by omega⟩
    have same : row idx=f := he
    exact ⟨(idx,k), Prod.ext (by change corner (row idx) k = _; rwa [same])
      (by change corner (row idx) (k+1) = _; rwa [same])⟩
  have oriented {u v : Fin n} (edge : H.Adj u v) : (u.val,v.val)∈darts rows :=
    edge.2.elim id (fun h => twins _ h)
  let fromPair (x : {e // e∈(darts rows).toFinset}) : H.Dart :=
    let h := List.mem_toFinset.mp x.property
    let b := bounds x.val h
    ⟨(⟨x.val.1,b.1⟩,⟨x.val.2,b.2.1⟩),fun eq => b.2.2 (congrArg Fin.val eq),Or.inl h⟩
  let pack : {e // e∈(darts rows).toFinset} ≃ H.Dart := {
    toFun := fromPair
    invFun := fun d => ⟨(d.fst.val,d.snd.val),List.mem_toFinset.mpr (oriented d.adj)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let mark (p : Fin (F+1) × Fin 3) : {e // e∈(darts rows).toFinset} := ⟨raw p,List.mem_toFinset.mpr (stored p)⟩
  have hit : Function.Surjective mark := by
    rintro ⟨e,m⟩
    obtain ⟨p,eq⟩ := covers _ (List.mem_toFinset.mp m)
    exact ⟨p,Subtype.ext eq⟩
  have bij : Function.Bijective mark := (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hit,by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe]
    rw [List.toFinset_card_of_nodup nodup, dlength, length, Nat.mul_comm]⟩
  let label := (Equiv.ofBijective mark bij).trans pack
  have fstLabel (i k) : ((label (i,k)).fst : Nat)=corner (row i) k := rfl
  have sndLabel (i k) : ((label (i,k)).snd : Nat)=corner (row i) (k+1) := rfl
  have twin {i j k l} (x : corner (row i) k = corner (row j) (l+1))
      (y : corner (row i) (k+1) = corner (row j) l) : (label (i,k)).symm = label (j,l) :=
    SimpleGraph.Dart.ext _ _ (Prod.ext (Fin.ext y) (Fin.ext x))
  apply Recognition.SphereRotation.planar_of_rows H label (fun _ _ => rfl) _ _ (by omega)
  · intro v
    obtain ⟨w,h⟩ := used v
    exact ⟨fromPair ⟨_,List.mem_toFinset.mpr h⟩,rfl⟩
  · intro dest
    have reach := connected _ (rows_mem 0) _ (rows_mem dest)
    let R (i j : Fin (F+1)) := ∃ k l, (label (i,k)).symm=label (j,l)
    have go {x y} (walk : Relation.ReflTransGen (FaceStep rows) x y) :
        ∀ i j : Fin (F+1), row i=x → row j=y → Walk R i j := by
      induction walk with
      | refl =>
        intro i j A B
        have h : raw (i,0) = raw (j,0) := by simp only [raw,A,B]
        have same : (i,(0 : Fin 3))=(j,0) := bij.1 (Subtype.ext h)
        cases congrArg Prod.fst same
        exact .refl
      | tail prev step ih =>
        intro i j A B
        obtain ⟨inX,inY,u,v,one,two⟩ := step
        obtain ⟨k,hk,krow⟩ := List.getElem_of_mem inX
        let k' : Fin (F+1) := ⟨k,by omega⟩
        have left : row k'= _ := krow
        have a := (side_iff ..).mp (left ▸ one)
        have b := (side_iff ..).mp (B ▸ two)
        obtain ⟨m,ma,mb⟩ := a
        obtain ⟨l,la,lb⟩ := b
        exact (ih i k' A left).step ⟨m,l,twin (ma.trans lb.symm) (mb.trans la.symm)⟩
    exact go reach 0 dest rfl rfl

/-- Opposite orientations on the two disks and the equatorial matching
give a spherical rotation on their closed, simple doubled graph. -/
theorem doubled_planar (s t : Shape) (eq : s.size=t.size) :
    IsPlanar (graph (2*(s.size+2)) (doubled s t)) := by
  let rows := doubled s t
  have count := doubled_euler s t eq
  have positive : 0<rows.length := by dsimp [rows]; omega
  apply list_plane (2*(s.size+2)) (rows.length-1) rows (by omega)
  · exact fun e hit => doubled_bounds s t eq hit
  · intro p hit
    rw [doubled_side_iff s t eq] at hit ⊢
    simpa using hit.symm
  · exact doubled_darts_nodup s t eq
  · exact doubled_used s t eq
  · exact fun _ x _ y => doubled_connected s t eq x y
  · exact count

/-- Gluing the two triangulated pages gives a plane host even if their
independent completions chose the same diagonal. Vertex copies are kept
distinct on the two disks and connected across the equatorial band. -/
theorem portGraph_planar (layers : List Layer) (w : Nat) : IsPlanar (portGraph layers w) := by
  classical
  let n := (layers.length+1)*w+2
  obtain ⟨s,ss,zero⟩ := page_triangulation layers w 0
  obtain ⟨t,ts,one⟩ := page_triangulation layers w 1
  have eq : s.size=t.size := ss.trans ts.symm
  let H := graph (2*(s.size+2)) (doubled s t)
  let label (v : Fin n) (b : Bool) : Fin (2*(s.size+2)) :=
    ⟨port v.val b.toNat,by dsimp [port,n] at *; cases b <;> dsimp <;> omega⟩
  have paired (v : Fin n) : H.Adj (label v false) (label v true) := by
    constructor
    · intro same
      have h := congrArg Fin.val same; dsimp [label,port] at h; omega
    · exact .inl ((doubled_side_iff s t eq _).mpr (.inl (boundary_pair s t (by dsimp [n] at v; omega))))
  have left {x y : Fin n} (ch : Chord layers w 0 x.val y.val) : H.Adj (label x false) (label y false) := by
    have lt := chord_increases ch
    constructor
    · intro same; have h := congrArg Fin.val same; dsimp [label,port] at h; omega
    · apply Or.inl
      apply (doubled_side_iff s t eq _).mpr
      apply Or.inl
      have mem : liftEdge 0 (x.val,y.val) ∈ (s.edges 0).map (liftEdge 0) := List.mem_map_of_mem (zero _ _ ch)
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ mem))
  have right {x y : Fin n} (ch : Chord layers w 1 x.val y.val) : H.Adj (label x true) (label y true) := by
    have lt := chord_increases ch
    constructor
    · intro same; have h := congrArg Fin.val same; dsimp [label,port] at h; omega
    · apply Or.inl
      apply (doubled_side_iff s t eq _).mpr
      apply Or.inl
      have mem : liftEdge 1 (x.val,y.val) ∈ (t.edges 0).map (liftEdge 1) := List.mem_map_of_mem (one _ _ ch)
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ mem))
  let bag (v : Fin n) : Finset (Fin (2*(s.size+2))) := {label v false,label v true}
  apply isPlanar_of_minorModel (doubled_planar s t eq)
  refine ⟨bag,fun v => ⟨_, Finset.mem_insert_self ..⟩, ?_, ?_, ?_⟩
  · intro v
    rw [← connSet_iff_induce_connected]
    have touch : Touch H {label v false} {label v true} :=
      ⟨_, Finset.mem_singleton_self _, _, Finset.mem_singleton_self _, paired v⟩
    have joined := ConnSet.union_touch (connSet_finset_singleton (label v false))
      (connSet_finset_singleton (label v true)) touch
    simpa [bag] using joined
  · intro x y ne
    apply Finset.disjoint_left.mpr
    intro z hx hy
    have id {v : Fin n} (m : z∈bag v) : z.val/2 = v.val := by
      rcases Finset.mem_insert.mp m with rfl|h
      · dsimp [label,port]; omega
      · obtain rfl := Finset.mem_singleton.mp h; dsimp [label,port]; omega
    exact ne (Fin.ext ((id hx).symm.trans (id hy)))
  · intro x y edge
    obtain ⟨p,hp,ch⟩ := edge
    rcases (show p=0 ∨ p=1 by omega) with rfl|rfl
    · exact ⟨label x false, Finset.mem_insert_self .., label y false, Finset.mem_insert_self ..,
        ch.elim left (fun c => (left c).symm)⟩
    · exact ⟨label x true, by simp [bag], label y true, by simp [bag],
        ch.elim right (fun c => (right c).symm)⟩

end Recognition.RowSphere
