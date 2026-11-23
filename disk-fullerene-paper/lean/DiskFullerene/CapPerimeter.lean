import DiskFullerene.CapLabels
import DiskFullerene.TraceFresh

namespace DiskFullerene.StripFresh
open EndFans EndFans.BoundaryLabel Dual EndLabels EndEuler Separation

private def route (k : I) (second : Bool) : Nat → BoundaryLabel
  | 0 => .middle
  | n+1 => if second then retreat k (route k second n) else advance k (route k second n)

private def strong (k : I) (second : Bool) : BoundaryLabel := .corner (if second then after k else k)

private theorem route_last : ∀ k s, route k s 5=strong k s := by decide
private theorem route_inj : ∀ k s, ∀ i j : Fin 6, route k s i.val=route k s j.val → i=j := by decide

variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

private structure EdgeData (C : Cap d) (a b : BoundaryLabel) where
  edge : RimEdge G (C.outer a) (C.outer b)
  selected : vertexSide d.seam d.side edge.label=true
  exposed : ∀ f∈triangle edge.label, IsBoundary G f → f=C.outer a ∨ f=C.outer b

private def EdgeData.rev {C : Cap d} {a b} (k : EdgeData C a b) : EdgeData C b a :=
  ⟨k.edge.rev,k.selected,fun f fm out=>(k.exposed f fm out).symm⟩

private theorem forward_edge (C : Cap d) (hh : 3≤h) {a b : BoundaryLabel} (ab : advance C.index a=b)
    (notSeam : ¬((a=.middle ∧ b=strong C.index C.second) ∨ (a=strong C.index C.second ∧ b=.middle))) :
    Nonempty (EdgeData C a b) := by
  have sep : (C.outer .middle=atSide G (apex M) d.i ∧ C.outer (strong C.index C.second)=atSide G (apex M) d.j) ∨
    (C.outer .middle=atSide G (apex M) d.j ∧ C.outer (strong C.index C.second)=atSide G (apex M) d.i) := by
    cases f : C.second <;> simpa [strong,Cap.outer,f] using C.seam
  have cyclic : OnCycle (dualRow G (apex M)) (C.outer a) (C.outer b) := by
    rcases ab ▸ C.adj_or_seam hh a with yes|seam
    · exact yes
    · exfalso;apply notSeam
      have both : (C.outer a=C.outer .middle ∧ C.outer b=C.outer (strong C.index C.second)) ∨
          (C.outer a=C.outer (strong C.index C.second) ∧ C.outer b=C.outer .middle) := by grind
      rcases both with ⟨p,q⟩|⟨p,q⟩ <;>
        first | exact .inl ⟨C.outer_injective hh _ _ p,C.outer_injective hh _ _ q⟩ |
          exact .inr ⟨C.outer_injective hh _ _ p,C.outer_injective hh _ _ q⟩
  obtain ⟨i,step⟩ := ab ▸ C.first_arc hh a
  obtain ⟨e,v,ac,ends,mem,other⟩ := cornerEdge G step
  have sel := core_corner_selected d.seam (C.rim_in i) v mem
  have nodes := (endpoint_iff G hh e v).1 ends
  have upper (f) (m : f∈triangle v) := other f ((mem_triangle v f).1 m)
  have core := (mem_diskInterior G _).1 (core_disk (C.rim_in i))
  have na : C.outer a≠apex M := fun eq=>row_no_loop G hh _ (eq ▸ C.outer_boundary a)
  have nb : C.outer b≠apex M := fun eq=>row_no_loop G hh _ (eq ▸ C.outer_boundary b)
  have pole : apex M∉triangle v := fun m=>by
    rcases upper _ m with r|r|r <;> first | exact core.1 r.symm | exact na r.symm | exact nb r.symm
  have hit : C.outer a∈triangle v ∧ C.outer b∈triangle v := by rcases ac with o|o <;> rw [o] at nodes <;> grind
  refine ⟨⟨⟨v,cyclic,pole,hit.1,hit.2⟩,sel,?_⟩⟩
  intro f fm out
  exact (upper f fm).resolve_left (fun eq=>core.2 (eq ▸ out))

/-- The five genuine boundary edges left after removing the marked chord
of a cap, starting at its weak endpoint. -/
theorem cap_walk (C : Cap d) (hh : 3≤h) :
    ∃ p : RimWalk G C.middle (C.junction (if C.second then after C.index else C.index)),
      p.labels.length=5 ∧ p.labels.Nodup ∧ (∀ t∈p.labels,vertexSide d.seam d.side t=true) ∧
      (∀ x, x∈p.vertices ↔ ∃ a, C.outer a=x) := by
  let F := route C.index C.second
  have no {i : Fin 5} : ¬((F i.val=.middle ∧ F (i.val+1)=strong C.index C.second) ∨
      (F i.val=strong C.index C.second ∧ F (i.val+1)=.middle)) := by
    exact (by decide : ∀ k s, ∀ i : Fin 5, ¬((route k s i.val=.middle ∧ route k s (i.val+1)=strong k s) ∨
      (route k s i.val=strong k s ∧ route k s (i.val+1)=.middle))) C.index C.second i
  have arc (i : Fin 5) : Nonempty (EdgeData C (F i.val) (F (i.val+1))) := by
    cases s : C.second with
    | false => exact forward_edge C hh (by simp [F,route,s]) no
    | true =>
      have eq : advance C.index (F (i.val+1))=F i.val := by simp [F,route,s,(BoundaryLabel.cycle _ _).1]
      obtain ⟨e⟩ := forward_edge C hh eq (by
        rintro (⟨a,b⟩|⟨a,b⟩)
        · exact (no (i:=i)) (.inr ⟨b,a⟩)
        · exact (no (i:=i)) (.inl ⟨b,a⟩))
      exact ⟨e.rev⟩
  let E (i : Fin 5) := Classical.choice (arc i)
  let p : RimWalk G (C.outer (F 0)) (C.outer (F 5)) :=
    .cons (E 0).edge (.cons (E 1).edge (.cons (E 2).edge (.cons (E 3).edge (.single (E 4).edge))))
  have lbl : p.labels=(List.finRange 5).map (fun i=>(E i).edge.label) := rfl
  have vrt : p.vertices=(List.finRange 6).map (fun i=>C.outer (F i.val)) := rfl
  have inj : Function.Injective (fun i=>(E i).edge.label) := by
    intro i j eq
    have both (k l : Fin 6) (same : C.outer (F k.val)=C.outer (F l.val)) : k=l :=
      route_inj C.index C.second _ _ (C.outer_injective hh _ _ same)
    change (E i).edge.label=(E j).edge.label at eq
    have lo := (E j).exposed _ (eq ▸ (E i).edge.first) (C.outer_boundary _)
    have hi := (E j).exposed _ (eq ▸ (E i).edge.last) (C.outer_boundary _)
    let i₀ : Fin 6 := ⟨i.val,by omega⟩; let i₁ : Fin 6 := ⟨i.val+1,by omega⟩
    let j₀ : Fin 6 := ⟨j.val,by omega⟩; let j₁ : Fin 6 := ⟨j.val+1,by omega⟩
    have x := lo.imp (both i₀ j₀) (both i₀ j₁)
    have y := hi.imp (both i₁ j₀) (both i₁ j₁)
    apply Fin.ext
    rcases x with a|a <;> rcases y with b|b <;> have k:=congrArg Fin.val a <;> have l:=congrArg Fin.val b <;>
      dsimp [i₀,i₁,j₀,j₁] at k l <;> omega
  have rlast : C.outer (F 5)=C.junction (if C.second then after C.index else C.index) := by rw [show F 5=_ from route_last C.index C.second];rfl
  have base : ∃ p : RimWalk G (C.outer (F 0)) (C.outer (F 5)), p.labels.length=5 ∧ p.labels.Nodup ∧
      (∀ t∈p.labels,vertexSide d.seam d.side t=true) ∧ (∀ x, x∈p.vertices ↔ ∃ a, C.outer a=x) := by
    refine ⟨p,by simp [lbl],by rw [lbl];exact (List.nodup_finRange 5).map _ (fun _ _ ne eq=>ne (inj eq)),?_,?_⟩
    · intro t tm;rw [lbl] at tm;obtain ⟨i,_,rfl⟩:=List.mem_map.mp tm;exact (E i).selected
    · intro x;rw [vrt];simp only [List.mem_map,List.mem_finRange,true_and]
      refine ⟨fun ⟨i,e⟩=>⟨_,e⟩,?_⟩
      rintro ⟨a,rfl⟩
      have all : ∀ k s a, ∃ i : Fin 6, route k s i.val=a := by
        intro k s a; cases a <;> decide +revert
      obtain ⟨i,h⟩:=all C.index C.second a
      exact ⟨i,congrArg C.outer h⟩
  exact rlast ▸ base

end DiskFullerene.StripFresh

namespace DiskFullerene.StripFresh
open EndFans Dual EndLabels EndEuler Strip

variable {M : MapData} {G : IsDiskFullerene M h}

/-- Either order of the physical endpoint pair at a terminal chord. -/
def MarkedBy {d : EndPiece M G} (C : Cap d) (x y : Face M) : Prop :=
  let v := C.junction (if C.second then after C.index else C.index)
  (x=C.middle ∧ y=v) ∨ (x=v ∧ y=C.middle)

private theorem reverse_outer {x y} (p : RimWalk G x y) (q : Face M) :
    q∈p.reverse.vertices ↔ q∈p.vertices := by simp

private theorem oriented_cap {d : EndPiece M G} (C : Cap d) (hh : 3≤h) {x y}
    (xy : MarkedBy C x y) :
    ∃ p : RimWalk G x y, p.labels.length=5 ∧ p.labels.Nodup ∧
      (∀ u∈p.labels, vertexSide d.seam d.side u=true) ∧
      (∀ z, z∈p.vertices ↔ ∃ i,C.outer i=z) := by
  obtain ⟨p,sz,simple,tags,outer⟩ := cap_walk C hh
  rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨p,sz,simple,tags,outer⟩
  · exact ⟨p.reverse,by simpa using sz,by rw [RimWalk.labels_reverse];exact (List.reverse_perm _).nodup_iff.mpr simple,fun u m=>tags _ (by simpa using m),
      fun z=>(reverse_outer p z).trans (outer z)⟩

private theorem not_apical {x y} (p : RimWalk G x y) {t} (hm : t∈p.labels) :
    apex M∉triangle t := by
  induction p with
  | nil => contradiction
  | cons e q ih => rcases List.mem_cons.mp hm with rfl|m;exact e.nonapex;exact ih m

structure LabeledBoundary {d e : EndPiece M G} (C : Cap d) (D : Cap e) (P Q : SeamState G) (moves : List Side) where
  line : Trace G P.x P.y Q.x Q.y
  first : RimWalk G P.x P.y
  last : RimWalk G Q.y Q.x
  agrees : line.moves=moves
  actualFaces : line.records
  firstCover : ∀ f, f∈first.vertices ↔ ∃ i, C.outer i=f
  lastCover : ∀ f, f∈last.vertices ↔ ∃ i, D.outer i=f
  rare : (first.vertices++line.newVertices++last.starts.tail).Nodup
  cover : (first.vertices++line.newVertices++last.starts.tail).Perm (dualRow G (apex M))
  count : moves.length+10=h

/-- Combine a face-by-face trace with two genuine caps. The local side
identifications at the first and last seam imply pairwise distinctness
of every supporting nonapical triangle; no new-label or global
boundary-bijection premise is needed. -/
theorem labeled_boundary {d e : EndPiece M G} (C : Cap d) (D : Cap e) (hh : 3≤h)
    {P Q : SeamState G} {moves} (trace : ActualTrace P moves Q)
    (firstMarks : MarkedBy C P.x P.y) (lastMarks : MarkedBy D Q.y Q.x)
    (firstSide : ∀ u, vertexSide d.seam d.side u=true → sideOf P u=true)
    (lastSide : ∀ u, vertexSide e.seam e.side u=true → sideOf Q u=false) :
    Nonempty (LabeledBoundary C D P Q moves) := by
  obtain ⟨line,agrees,actual,nd,colors,mono⟩ := extract_trace hh trace
  obtain ⟨left,szL,ndL,tagsL,coverL⟩ := oriented_cap C hh firstMarks
  obtain ⟨right,szR,ndR,tagsR,coverR⟩ := oriented_cap D hh lastMarks
  have sepL (x) (xl : x∈left.labels) (y) (yl : y∈line.triangles) : x≠y := by
    rintro rfl
    exact Bool.noConfusion ((colors x yl).2.1.symm.trans (firstSide x (tagsL x xl)))
  have lead : (left.labels++line.triangles).Nodup := List.nodup_append.mpr ⟨ndL,nd,sepL⟩
  have rare : (left.labels++line.triangles++right.labels).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨lead,ndR,?_⟩
    intro x mem y endp eq; subst y
    have cold := lastSide x (tagsR x endp)
    rcases List.mem_append.mp mem with xl|xm
    · exact Bool.noConfusion (cold.symm.trans (mono x (not_apical left xl) (firstSide x (tagsL x xl))))
    · exact Bool.noConfusion (cold.symm.trans (colors x xm).2.2)
  obtain ⟨simple,all,sz⟩ := line.fresh_and_length left right hh szL szR rare
  exact ⟨⟨line,left,right,agrees,actual,coverL,coverR,simple,all,by rwa [←agrees,line.moves_count]⟩⟩

end DiskFullerene.StripFresh
