import DiskFullerene.RepeatedContour
import DiskFullerene.EndRotations

namespace DiskFullerene.Dual
open Separation EndEuler

/-- Removing any one dual vertex leaves the actual spherical dual connected. -/
theorem punctured_connected {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (u : Face M) {x y : Face M} (nx : x≠u) (ny : y≠u) :
    Walk (fun i j => i≠u ∧ j≠u ∧ j∈dualRow G i) x y := by
  classical
  let C := dualRow G u
  let R := fun i j : Face M => i≠u ∧ j≠u ∧ j∈dualRow G i
  have sym : ∀ i j, R i j → R j i := fun _ _ h => ⟨h.2.1,h.1,(dual_adj_symmetric G _ _).1 h.2.2⟩
  have rim (a b : Face M) (ar : a∈C) (br : b∈C) : Walk R a b := by
    apply traverseWord C id R sym _ ar br
    intro i j ij
    have e := endsOfWordSide ij
    change Walk R i j
    exact .step .refl ⟨fun eq => row_no_loop G hh _ (eq ▸ e.1),
      fun eq => row_no_loop G hh _ (eq ▸ e.2),cyclic_link G u ij⟩
  have deg : 0<C.length := by
    by_cases eu : u=apex M
    · subst u; change 0<(dualRow G (apex M)).length; have := (boundary_cycle G hh).2.1; omega
    · have := inner_degree G eu; dsimp [C]; omega
  let q := C[0]
  have qr : q∈C := List.getElem_mem _
  let proxy (i : Face M) := if i=u then q else i
  have lifted {i j : Face M} (e : j∈dualRow G i) : Walk R (proxy i) (proxy j) := by
    by_cases iu : i=u
    · subst i
      have nu : j≠u := fun eq => row_no_loop G hh _ (eq ▸ e)
      simpa [proxy,nu] using rim q j qr e
    by_cases ju : j=u
    · subst j
      simpa [proxy,iu] using rim i q ((dual_adj_symmetric G _ _).1 e) qr
    · simpa [proxy,iu,ju] using (Walk.step (R:=R) Walk.refl (⟨iu,ju,e⟩ : R i j))
  have path {i j} (p : Walk (Step M (fun _ => True)) i j) : Walk R (proxy i) (proxy j) := by
    induction p with
    | refl => exact .refl
    | step _ edge ih =>
      obtain ⟨_,_,hit|hit⟩ := edge
      · exact ih.trans (lifted ((mem_row_iff G _ _).2 ⟨_,hit⟩))
      · exact ih.trans (lifted ((dual_adj_symmetric G _ _).1 ((mem_row_iff G _ _).2 ⟨_,hit⟩)))
  simpa [proxy,nx,ny] using path (dual_connected G hh x y)

/-- The closed arm consists of one component of J minus u, together with u. -/
noncomputable def arm {M : MapData} (G : IsDiskFullerene M h) (u a f : Face M) : Bool :=
  open Classical in decide (f=u ∨ Walk (CoreAvoid G u) a f)

theorem in_arm {M : MapData} {G : IsDiskFullerene M h} {u a f : Face M} :
    arm G u a f=true ↔ f=u ∨ Walk (CoreAvoid G u) a f := by classical simp [arm]

theorem arm_stays_inside {M} {G : IsDiskFullerene M h} {u a f} (ui : u∈diskInterior G)
    (ai : a∈diskInterior G) (hit : arm G u a f=true) : f∈diskInterior G := by
  rcases in_arm.mp hit with rfl|p
  · exact ui
  · cases p with
    | refl => exact ai
    | step _ e => exact e.2.2.2.1

theorem arm_frontier {M} {G : IsDiskFullerene M h} {u a f g}
    (ui : u∈diskInterior G) (ai : a∈diskInterior G) (fu : f≠u) (active : arm G u a f=true)
    (outside : arm G u a g=false) (adj : g∈dualRow G f) : IsBoundary G g := by
  rcases in_arm.mp active with eq|p
  · contradiction
  by_cases gi : g∈diskInterior G
  · have gu : g≠u := fun eq => by have yes : arm G u a g = true := in_arm.mpr (Or.inl eq); grind
    have yes : arm G u a g=true := in_arm.mpr (Or.inr (p.step ⟨fu,gu,arm_stays_inside ui ai active,gi,adj⟩))
    grind
  · have fi := (mem_diskInterior G f).1 (arm_stays_inside ui ai active)
    have ne : g≠apex M := fun eq => fi.2 ((dual_adj_symmetric G _ _).1 (eq ▸ adj))
    exact Classical.byContradiction fun off => gi ((mem_diskInterior G _).2 ⟨ne,off⟩)

theorem arm_complement_connected {M} (G : IsDiskFullerene M h) (hh : 3≤h)
    {u a} (ui : u∈diskInterior G) (ai : a∈diskInterior G) (z : Face M) (outside : arm G u a z=false) :
    Walk (Adj (dual G) (fun e => sideEdge (dual G) (fun i=> !arm G u a i) e=true)) (apex M) z := by
  let A := arm G u a
  let R := Adj (dual G) (fun e => sideEdge (dual G) (fun i=> !A i) e=true)
  have base : A (apex M)=false := by
    cases t : A (apex M) with
    | false => rfl
    | true => exact False.elim (((mem_diskInterior G _).1 (arm_stays_inside ui ai t)).1 rfl)
  have one {p q} (hp : A p=false) (hq : A q=false) (adj : q∈dualRow G p) : R p q := by
    obtain ⟨d,di,dj⟩ := (mem_row_iff G _ _).1 adj
    obtain ⟨e,ori⟩ := repr_dart G (incident_dart G di)
    have ac := crossTable G ori (Or.inl ⟨di,dj⟩)
    exact ⟨e,by rcases ac with eq|eq <;> simp [sideEdge,eq,hp,hq],ac⟩
  have main {p} (path : Walk (fun i j => i≠u ∧ j≠u ∧ j∈dualRow G i) (apex M) p) :
      A p=false → Walk R (apex M) p := by
    induction path with
    | refl => exact fun _ => .refl
    | @step t z _ edge ih =>
      intro oz
      cases ot : A t with
      | false => exact (ih ot).step (one ot oz edge.2.2)
      | true => exact .step .refl (one base oz (arm_frontier ui ai edge.1 ot oz edge.2.2))
  have zu : z≠u := by
    intro eq
    have exact' : arm G u a z=true := in_arm.mpr (.inl eq)
    grind
  exact main (punctured_connected G hh u (Ne.symm ((mem_diskInterior G _).1 ui).1) zu) outside

structure ArmData {M} (G : IsDiskFullerene M h) (u a : Face M) : Prop where
  pole : arm G u a (apex M)=false
  hit : arm G u a u=true
  nonisolated : ∀ q, arm G u a q=true → ∃ f ∈ dualRow G q, arm G u a f=true
  single : ∀ q, arm G u a q=true → BoundaryRun G (arm G u a) q → q=u
  euler : num (sideEdge (dual G) (arm G u a))+1 ≤ num (arm G u a) + num (solid G (arm G u a) true)

theorem arm_data {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    {u a} (ui : u∈diskInterior G) (ai : a∈diskInterior G) (au : a∈dualRow G u) : ArmData G u a := by
  let A := arm G u a
  have uhit : A u=true := in_arm.mpr (.inl rfl)
  have ahit : A a=true := in_arm.mpr (.inr .refl)
  have pole : A (apex M)=false := by
    cases z : A (apex M) with
    | false => rfl
    | true => exact False.elim (((mem_diskInterior G _).1 (arm_stays_inside ui ai z)).1 rfl)
  have noniso (f) (hit : A f=true) : ∃ g∈dualRow G f, A g=true := by
    by_cases eq : f=u
    · subst f; exact ⟨a,au,ahit⟩
    have fi := arm_stays_inside ui ai hit
    have min := interior_min_two G hh hc fi
    let L := (dualRow G f).filter (diskInterior G).contains
    have size : 0<L.length := by change 2≤L.length at min; omega
    let g := L[0]
    have gm : g ∈ L := List.getElem_mem _
    have ⟨row,inside⟩ := List.mem_filter.mp gm
    refine ⟨g,row,?_⟩
    cases t : A g with
    | true => rfl
    | false => exact False.elim (((mem_diskInterior G g).1 (List.contains_iff_mem.mp inside)).2 (arm_frontier ui ai eq hit t row))
  have single : ∀ q, A q=true → BoundaryRun G A q → q=u := by
    rintro q hq ⟨p,r,s,ne,op,ort,os,pr,rs⟩
    apply Classical.byContradiction; intro qu
    have out := fun {v} (o : A v=false) (nb : v∈dualRow G q) => arm_frontier ui ai qu hq o nb
    exact no_three_on_boundary G hh hc (arm_stays_inside ui ai hq)
      (out op (endsOfWordSide pr).1) (out ort (endsOfWordSide pr).2) (out os (endsOfWordSide rs).2) ne pr rs
  exact ⟨pole,uhit,noniso,single,
    induced_euler_bound G hh A pole (nonsolid G hh A uhit) (arm_complement_connected G hh ui ai)⟩

/-- Each arm at a cut vertex contains at least five other core vertices. -/
theorem arm_six {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    {u a} (ui : u∈diskInterior G) (ai : a∈diskInterior G) (au : a∈dualRow G u) :
    6≤num (arm G u a) := by
  have armData := arm_data G hh hc ui ai au
  exact EndLabels.six_of_mask G hh _ armData.pole ⟨u,armData.hit⟩ armData.nonisolated ⟨u,armData.single⟩ armData.euler

end DiskFullerene.Dual
