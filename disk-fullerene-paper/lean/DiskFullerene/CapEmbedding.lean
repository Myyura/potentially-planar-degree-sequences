import DiskFullerene.CapLabels

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels Separation

namespace Cap
variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

theorem real_edge (C : Cap d) (hh : 3≤h) (a b : Node) (edge : nodeEdge C.index a b=true) :
    C.real b∈dualRow G (C.real a) := by
  have center (j : I) : C.W.rim j∈dualRow G C.W.center := (C.W.central _).mpr ⟨j,rfl⟩
  have outer (a b : BoundaryLabel) (near : BoundaryLabel.neighbor C.index a b) : C.outer b∈dualRow G (C.outer a) := by
    rcases near with rfl|rfl
    · obtain ⟨_,step⟩ := C.first_arc hh a; exact cyclic_link G _ step
    · obtain ⟨_,step⟩ := C.first_arc hh (BoundaryLabel.retreat C.index a)
      rw [(BoundaryLabel.cycle C.index a).1] at step; exact (dual_adj_symmetric G _ _).mp (cyclic_link G _ step)
  cases a with
  | center => cases b with | center => contradiction | rim j => exact center j | outside b => contradiction
  | rim i => cases b with
    | center => exact (dual_adj_symmetric G _ _).mp (center i)
    | rim j => have near : j=before i ∨ j=after i := of_decide_eq_true edge
               apply (C.W.wheel i _ (C.rim_in j)).mpr; rcases near with rfl|rfl <;> simp
    | outside b => exact C.fans.in_row ((C.arm_row hh i b).mpr (of_decide_eq_true edge))
  | outside a => cases b with
    | center => contradiction
    | rim j => exact (dual_adj_symmetric G _ _).mp (C.fans.in_row ((C.arm_row hh j a).mpr (of_decide_eq_true edge)))
    | outside b => exact outer a b (of_decide_eq_true edge)

def modelEnd (i : I) (s : Bool) : GluingIso.End := ⟨CapRing.singletonPattern i,i,s⟩

def readLabel (v : CapRing.Label) : Node :=
  if v.val=0 then .center else if v.val<6 then .rim ⟨(v.val-1)%5,by omega⟩
  else if v.val<11 then .outside (.corner ⟨(v.val-6)%5,by omega⟩) else .outside .middle

def localNode (i : I) (s : Bool) (v : Fin 10) := readLabel ((modelEnd i s).place v)

def strongLabel (i : I) (s : Bool) := BoundaryLabel.corner (if s then after i else i)

def referenceBoundary : Node→Bool | .outside _ => true | _ => false

private theorem localTable (k : I) (s : Bool) (v : Fin 10) :
    code k (localNode k s v) = ((modelEnd k s).place v).val ∧
    localNode k s v ≠ .outside .middle ∧ localNode k s v ≠ .outside (strongLabel k s) ∧
    (referenceBoundary (localNode k s v) = true ↔ 6 ≤ v.val) := by decide +revert

private theorem coverTable (k : I) (s : Bool) (n : Node) :
    n=.outside .middle ∨ n=.outside (strongLabel k s) ∨ ∃ v : Fin 10, n=localNode k s v := by
  cases n with | center => decide +revert | rim i => decide +revert | outside v => cases v <;> decide +revert

noncomputable def localFace (C : Cap d) (v : Fin 10) := C.real (localNode C.index C.second v)

def weak (C : Cap d) := C.middle
def strong (C : Cap d) := C.outer (strongLabel C.index C.second)

theorem marks (C : Cap d) : (C.weak=atSide G (apex M) d.i ∧ C.strong=atSide G (apex M) d.j) ∨
    (C.weak=atSide G (apex M) d.j ∧ C.strong=atSide G (apex M) d.i) := by
  cases e : C.second <;> simpa [weak,strong,strongLabel,outer,e] using C.seam

theorem local_injective (C : Cap d) (hh : 3≤h) (a b : Fin 10) (same : C.localFace a=C.localFace b) : a=b := by
  let E:=modelEnd C.index C.second
  have ok : E.ok := (CapRing.classify _ _ _).mpr rfl
  have equal := C.real_injective hh _ _ same
  have ea := (localTable C.index C.second a).1
  have eb := (localTable C.index C.second b).1
  exact (GluingIso.local_agreement E ok).injective a b (Fin.ext (ea.symm.trans ((congrArg (code C.index) equal).trans eb)))

theorem local_avoids_marks (C : Cap d) (hh : 3≤h) (v : Fin 10) : C.localFace v ≠ C.weak ∧ C.localFace v≠C.strong :=
  ⟨fun e=>(localTable C.index C.second v).2.1 (C.real_injective hh _ (.outside .middle) e),
   fun e=>(localTable C.index C.second v).2.2.1 (C.real_injective hh _ (.outside (strongLabel _ _)) e)⟩

theorem local_edges (C : Cap d) (hh : 3≤h) (a b : Fin 10) (ed : Construction.capEdge a.val b.val=true) : C.localFace b∈dualRow G (C.localFace a) := by
  let E:=modelEnd C.index C.second; have ok : E.ok := (CapRing.classify _ _ _).mpr rfl
  apply C.real_edge hh
  rw [edges_in_table,(localTable _ _ a).1,(localTable _ _ b).1]; exact ((GluingIso.local_agreement E ok).edge a b).trans ed

theorem local_weak (C : Cap d) (hh : 3≤h) (a : Fin 10) (ed : Construction.capEdge a.val 10=true) : C.weak∈dualRow G (C.localFace a) := by
  let E:=modelEnd C.index C.second; have ok : E.ok := (CapRing.classify _ _ _).mpr rfl
  apply C.real_edge hh _ (.outside .middle)
  rw [edges_in_table,(localTable _ _ a).1]; exact ((GluingIso.local_agreement E ok).weak a).trans ed

theorem local_strong (C : Cap d) (hh : 3≤h) (a : Fin 10) (ed : Construction.capEdge a.val 11=true) : C.strong∈dualRow G (C.localFace a) := by
  let E:=modelEnd C.index C.second; have ok : E.ok := (CapRing.classify _ _ _).mpr rfl
  apply C.real_edge hh _ (.outside (strongLabel _ _))
  rw [edges_in_table,(localTable _ _ a).1]; exact ((GluingIso.local_agreement E ok).strong a).trans ed

theorem local_boundary (C : Cap d) (v : Fin 10) : IsBoundary G (C.localFace v) ↔ 6≤v.val := by
  have all (n : Node) : IsBoundary G (C.real n) ↔ referenceBoundary n=true := by
    cases n with
    | center => have no := (mem_diskInterior G _).mp (core_disk ((C.W.chosen _).mpr (.inl rfl))) |>.2; simp [real,referenceBoundary,IsBoundary,no]
    | rim j => have no := (mem_diskInterior G _).mp (core_disk (C.rim_in j)) |>.2; simp [real,referenceBoundary,IsBoundary,no]
    | outside a => simp [real,referenceBoundary,C.outer_boundary a]
  exact (all _).trans (localTable C.index C.second v).2.2.2

theorem local_notPole (C : Cap d) (hh : 3≤h) (v : Fin 10) : C.localFace v≠apex M := by
  have all (n : Node) : C.real n≠apex M := by
    cases n with
    | center => exact ((mem_diskInterior G _).mp (core_disk ((C.W.chosen _).mpr (.inl rfl)))).1
    | rim j => exact ((mem_diskInterior G _).mp (core_disk (C.rim_in j))).1
    | outside a => exact fun eq=>row_no_loop G hh _ (eq ▸ (show IsBoundary G (C.real (.outside a)) from C.outer_boundary a))
  exact all _

/-- The nonmarked boundary nodes belong strictly to the terminal side
as original faces. This is what excludes their occurrence in the spine. -/
theorem local_side (C : Cap d) (hh : 3≤h) (v : Fin 10) : faceSide d.seam d.side (C.localFace v)=true := by
  classical
  have notMarks := C.local_avoids_marks hh v
  have away : C.localFace v≠apex M ∧ C.localFace v≠atSide G (apex M) d.i ∧ C.localFace v≠atSide G (apex M) d.j := by
    have ord := C.marks; exact ⟨C.local_notPole hh v,by grind,by grind⟩
  generalize e : localNode C.index C.second v=n at *
  have orig : C.localFace v=C.real n := congrArg C.real e
  rw [orig] at away ⊢
  cases n with
  | center => exact (Bool.and_eq_true_iff.mp ((C.W.chosen _).mpr (.inl rfl))).2
  | rim j => exact (Bool.and_eq_true_iff.mp (C.rim_in j)).2
  | outside a =>
    obtain ⟨i,im⟩ : ∃ i, C.outer a∈(C.fans.arc i).word := by
      cases a with | corner i => exact ⟨i,by simp [outer,TerminalAnnulus.junction,Arc.word]⟩ | middle => exact ⟨C.index,by simp [outer,Arc.word,C.split]⟩
    obtain ⟨z,iz,az⟩ := (mem_row_iff G _ _).mp (C.fans.in_row im)
    let p : Fin M.ord := ⟨z.1,(dart_info G (incident_dart G iz)).1⟩
    have pick := core_corner_selected d.seam (C.rim_in i) p (sideEnds iz).1
    have am : p.val∈M.faces[(C.outer a).val] := (sideEnds az).2
    have eq := d.seam.color_at away am
    have cf : d.seam.color p.val ↔ d.seam.part.left p := ⟨fun ⟨_,l⟩=>l,fun l=>⟨p.isLt,l⟩⟩
    change faceSide d.seam d.side (C.real (.outside a))=true
    simpa [faceSide,away,←eq,vertexSide,←cf] using pick

/-- A chosen original face has constant side on its entire primal
boundary. Applied to a private cap label, every triangle touching it is
on the same side of the terminal chord. -/
theorem local_vertex_side (C : Cap d) (hh : 3≤h) (v : Fin 10) {u : Fin M.ord} (hit : C.localFace v∈triangle u) :
    vertexSide d.seam d.side u=true := by
  classical
  have yes := C.local_side hh v
  have parts := Bool.and_eq_true_iff.mp yes
  have nf : C.localFace v≠apex M ∧ C.localFace v≠atSide G (apex M) d.i ∧ C.localFace v≠atSide G (apex M) d.j := of_decide_eq_true parts.1
  have ft := d.seam.color_at nf ((mem_triangle u _).mp hit)
  have cf : d.seam.color u.val ↔ d.seam.part.left u := ⟨fun ⟨_,l⟩=>l,fun l=>⟨u.isLt,l⟩⟩
  have eq := parts.2
  change (decide (d.seam.faceColor (C.localFace v)) == d.side)=true at eq
  simpa [vertexSide,← cf,←ft] using eq

theorem outer_iff (C : Cap d) (f : Face M) :
    (∃ a, C.outer a=f) ↔ f=C.weak ∨ f=C.strong ∨ ∃ v : Fin 10, 6≤v.val ∧ C.localFace v=f := by
  constructor
  · rintro ⟨a,rfl⟩
    rcases coverTable C.index C.second (.outside a) with e|e|⟨v,e⟩
    · exact .inl (congrArg C.real e)
    · exact .inr (.inl (congrArg C.real e))
    · have eq : C.localFace v=C.outer a := (congrArg C.real e).symm
      exact .inr (.inr ⟨v,(C.local_boundary v).mp (eq ▸ C.outer_boundary a),eq⟩)
  · rintro (rfl|rfl|⟨v,hv,rfl⟩)
    · exact ⟨.middle,rfl⟩
    · exact ⟨strongLabel _ _,rfl⟩
    · have kind := (localTable C.index C.second v).2.2.2.mpr hv
      unfold localFace
      cases e : localNode C.index C.second v with
      | center => simp [e,referenceBoundary] at kind
      | rim j => simp [e,referenceBoundary] at kind
      | outside a => exact ⟨a,rfl⟩

end Cap
end DiskFullerene.EndFans
