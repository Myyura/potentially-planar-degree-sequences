import DiskFullerene.CycleSides
import DiskFullerene.SimpleContour

namespace DiskFullerene.Dual
open Separation

noncomputable def contourPiece {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    (z : {x // IsBoundary G x}) :=
  let A := boundaryArc G hh hc z.val z.property
  (List.range A.steps).map fun k => A.node (k+1)

theorem contourPiece_nodup {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    (z : {x // IsBoundary G x}) : (contourPiece G hh hc z).Nodup := by
  let A := boundaryArc G hh hc z.val z.property
  have ne : z.val≠apex M := fun eq => row_no_loop G hh _ (eq ▸ z.property)
  have deg := inner_degree G ne
  have sz := A.length_eq
  change (dualRow G z.val).length=5 ∨ (dualRow G z.val).length=6 at deg
  have small : A.steps≤2 := by omega
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj ij eq
  change i<(List.map _ (List.range A.steps)).length at hi
  change j<(List.map _ (List.range A.steps)).length at hj
  simp only [List.length_map,List.length_range] at hi hj
  change (List.map _ (List.range A.steps))[i] = (List.map _ (List.range A.steps))[j] at eq
  simp only [List.getElem_map,List.getElem_range] at eq
  change A.node (i+1)=A.node (j+1) at eq
  have consecutive : i+1=j := by omega
  have link := cyclic_link G z.val (A.stepSide (i+1) (by omega))
  rw [consecutive] at link eq
  exact row_no_loop G hh _ (eq ▸ link)

theorem contourPiece_switch {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    {z : {x // IsBoundary G x}} {u : Face M} (m : u∈contourPiece G hh hc z) :
    u∈diskInterior G ∧ ∃ a ∈ diskInterior G, (z.val,a)∈sides (dualRow G u) := by
  let A := boundaryArc G hh hc z.val z.property
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp m
  have lt : k<A.steps := List.mem_range.mp hk
  exact ⟨A.inside _ (by omega),A.node k,A.inside _ (by omega),(turn_triangle G (A.stepSide k lt)).2⟩

theorem attached_nodup {α : Type} [DecidableEq α] {C : List α} (cn : C.Nodup) : C.attach.Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj ij eq
  have z := congrArg Subtype.val eq
  simp only [List.getElem_attach] at z
  have eqI := index_eq cn (by simpa using hi) (by simpa using hj) z
  omega
/-- Two separate visits to the same contour vertex give two different
boundary-to-interior transitions in its actual cyclic link. -/
theorem repeated_switches {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (hc : ¬HasChord G) (repeated : ¬(contourWord G hh hc).Nodup) :
    ∃ u x y a b, u ∈ diskInterior G ∧ x≠y ∧ IsBoundary G x ∧ IsBoundary G y ∧
      a ∈ diskInterior G ∧ b ∈ diskInterior G ∧
      (x,a) ∈ sides (dualRow G u) ∧ (y,b) ∈ sides (dualRow G u) := by
  classical
  let C := dualRow G (apex M)
  let piece := contourPiece G hh hc
  have nd := contourPiece_nodup G hh hc
  have hit {z} {u} (m : u∈piece z) := contourPiece_switch G hh hc m
  apply Classical.byContradiction
  intro none
  apply repeated
  change (C.attach.flatMap piece).Nodup
  apply List.pairwise_flatMap.mpr
  refine ⟨fun x _ => nd x,?_⟩
  have ca := attached_nodup (row_nodup G (noRepeatOnSphere G hh) (apex M))
  apply ca.imp
  intro x y neq u hu v hv eq
  subst v
  obtain ⟨ui,a,ai,sa⟩ := hit hu
  obtain ⟨_,b,bi,sb⟩ := hit hv
  exact none ⟨u,x.val,y.val,a,b,ui,fun e => neq (Subtype.ext e),x.property,y.property,ai,bi,sa,sb⟩

def CoreAvoid {M : MapData} (G : IsDiskFullerene M h) (u x y : Face M) : Prop :=
  x≠u ∧ y≠u ∧ InteriorAdj G x y

private theorem finFour {P : Fin 4 → Prop} (z : P 0) (o : P 1) (t : P 2) (s : P 3) :
    ∀ i, P i := by
  intro i
  have eq : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases eq with rfl|rfl|rfl|rfl <;> assumption

/-- Distinct boundary-to-interior transitions at a core vertex lead into
different components after that vertex is removed. -/
theorem switches_separate {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    {u x y a b : Face M} (ui : u∈diskInterior G) (distinct : x≠y)
    (xc : IsBoundary G x) (yc : IsBoundary G y) (ai : a∈diskInterior G) (bi : b∈diskInterior G)
    (xa : (x,a)∈sides (dualRow G u)) (yb : (y,b)∈sides (dualRow G u)) : ¬Walk (CoreAvoid G u) a b := by
  let W := apex M
  let v (j : Fin 4) := ([u,x,W,y][j.val]'(by simp))
  have xw : x≠W := fun eq => row_no_loop G hh _ (eq ▸ xc)
  have yw : y≠W := fun eq => row_no_loop G hh _ (eq ▸ yc)
  have us := (mem_diskInterior G u).1 ui
  have nx : u≠x := fun eq => us.2 (eq ▸ xc)
  have ny : u≠y := fun eq => us.2 (eq ▸ yc)
  have uw : u≠W := us.1
  have vi : Function.Injective v := by
    intro i j
    apply finFour (P := fun i => v i=v j → i=j) _ _ _ _ i <;>
      apply finFour (P := fun j => v _=v j → _=j) _ _ _ _ j <;>
      intro eq <;> first | rfl | exact (nx eq).elim | exact (nx eq.symm).elim | exact (ny eq).elim | exact (ny eq.symm).elim | exact (uw eq).elim | exact (uw eq.symm).elim | exact (xw eq).elim | exact (xw eq.symm).elim | exact (yw eq).elim | exact (yw eq.symm).elim | exact (distinct eq).elim | exact (distinct eq.symm).elim
  have au := (endsOfWordSide xa).2; have bu := (endsOfWordSide yb).2
  have xu := (endsOfWordSide xa).1; have yu := (endsOfWordSide yb).1
  obtain ⟨S⟩ := cycleSides G hh (n := 3) (by decide) v vi (finFour
    (show x ∈ dualRow G u from xu) (show W ∈ dualRow G x from (dual_adj_symmetric G _ _).1 xc)
    (show y ∈ dualRow G W from yc) (show u ∈ dualRow G y from (dual_adj_symmetric G _ _).1 yu))
  have off (k : Face M) (ki : k ∈ diskInterior G) (ku : k≠u) : ∀ j, k≠v j :=
    finFour ku (fun eq => ((mem_diskInterior G k).1 ki).2 (eq ▸ xc))
      ((mem_diskInterior G k).1 ki).1 (fun eq => ((mem_diskInterior G k).1 ki).2 (eq ▸ yc))
  have na : a≠u := fun eq => row_no_loop G hh _ (eq ▸ au)
  have nb : b≠u := fun eq => row_no_loop G hh _ (eq ▸ bu)
  have apart := S.sectors_separate hh vi 0 xa yb distinct (off a ai na) (off b bi nb)
  have lift {p q} (path : Walk (CoreAvoid G u) p q) :
      Walk (fun r s : Face M => (∀ j, r≠v j) ∧ (∀ j, s≠v j) ∧ s ∈ dualRow G r) p q := by
    induction path with
    | refl => exact .refl
    | step _ edge ih =>
      obtain ⟨nu,nv,tu,tv,ed⟩ := edge
      exact ih.step ⟨off _ tu nu, off _ tv nv, ed⟩
  exact fun path => apart (S.walk_stays (lift path))

/-- A repeated visit forces an actual cut vertex of the induced core
graph: two surviving core neighbours lie in different components. -/
theorem repeated_cut_vertex {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (hc : ¬HasChord G) (repeated : ¬(contourWord G hh hc).Nodup) :
    ∃ u a b : Face M, u ∈ diskInterior G ∧ a ∈ diskInterior G ∧ b ∈ diskInterior G ∧
      a ∈ dualRow G u ∧ b ∈ dualRow G u ∧ ¬Walk (CoreAvoid G u) a b := by
  obtain ⟨u,x,y,a,b,ui,distinct,xc,yc,ai,bi,xa,yb⟩ := repeated_switches G hh hc repeated
  exact ⟨u,a,b,ui,ai,bi,(endsOfWordSide xa).2,(endsOfWordSide yb).2,
    switches_separate G hh ui distinct xc yc ai bi xa yb⟩

theorem chordless_cut_vertex {M : MapData} (G : IsDiskFullerene M h) (hh : 12≤h)
    (hc : ¬HasChord G) (small : M.hexagons≤6) :
    ∃ u a b : Face M, u ∈ diskInterior G ∧ a ∈ diskInterior G ∧ b ∈ diskInterior G ∧
      a ∈ dualRow G u ∧ b ∈ dualRow G u ∧ ¬Walk (CoreAvoid G u) a b :=
  repeated_cut_vertex G (by omega) hc (chordless_repeats G hh hc small)

end DiskFullerene.Dual
