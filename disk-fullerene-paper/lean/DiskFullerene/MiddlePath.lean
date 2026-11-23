import DiskFullerene.SpineWalk
import DiskFullerene.MiddleFaces

namespace DiskFullerene.MiddlePath
open Dual EndLabels EndEuler Separation Dissection

def Proper {M} (G : IsDiskFullerene M h) (e : Edge M) :=
  ∃ a b, Across (dual G) e a b ∧ IsBoundary G a ∧ IsBoundary G b ∧ ¬OnCycle (dualRow G (apex M)) a b

def Crossing {M} (G : IsDiskFullerene M h) (u v : Fin M.ord) :=
  ∃ e, Across (primal G) e u v ∧ Proper G e

def Pure {M} (G : IsDiskFullerene M h) (u : Fin M.ord) := ∀ f∈triangle u, IsBoundary G f

private theorem edgeDistinct {M} (G : IsDiskFullerene M h) (e : Edge M) : (primal G e).1≠(primal G e).2 :=
  fun eq => Nat.ne_of_lt (ordered e) (congrArg Fin.val eq)

theorem symmetric {M} (G : IsDiskFullerene M h) {u v} (e : Crossing G u v) : Crossing G v u :=
  ⟨_,(e.choose_spec.1).symm,e.choose_spec.2⟩

theorem irreflexive {M} (G : IsDiskFullerene M h) (u : Fin M.ord) : ¬Crossing G u u := by
  rintro ⟨e,uv,_⟩; have ne := edgeDistinct G e; rcases uv with eq|eq <;> simp [eq] at ne

theorem edge_corners {M} (G : IsDiskFullerene M h) {e : Edge M} {i j : Face M} {u v : Fin M.ord}
    (p : Across (primal G) e u v) (d : Across (dual G) e i j) :
    i∈triangle u ∧ j∈triangle u ∧ i∈triangle v ∧ j∈triangle v := by
  have l := sideEnds (left_incident G (endpoints_mem e)); have r := sideEnds (left_incident G (dart_reverse G (endpoints_mem e)))
  have a : (dual G e).1∈triangle (primal G e).1 := (mem_triangle _ _).mpr l.1
  have b : (dual G e).1∈triangle (primal G e).2 := (mem_triangle _ _).mpr l.2
  have c : (dual G e).2∈triangle (primal G e).1 := (mem_triangle _ _).mpr r.2
  have k : (dual G e).2∈triangle (primal G e).2 := (mem_triangle _ _).mpr r.1
  rcases p with eq|eq <;> rcases d with de|de <;> rw [eq,de] at a b c k <;> grind

theorem primal_unique {M} (G : IsDiskFullerene M h) {u v : Fin M.ord} {e k : Edge M}
    (euv : Across (primal G) e u v) (kuv : Across (primal G) k u v) : e=k := by
  have orient (z : Edge M) : (primal G z).1.val<(primal G z).2.val := ordered z
  have x := orient e; have y := orient k
  have eq : primal G e=primal G k := by rcases euv with h|h <;> rcases kuv with h'|h' <;> rw [h] at x ⊢ <;> rw [h'] at y ⊢ <;> simp_all <;> omega
  exact repr_unique G (congrArg (fun (p : Fin M.ord × Fin M.ord)=>(p.1.val,p.2.val)) eq)

private theorem opposite {M} (G : IsDiskFullerene M h) {e : Edge M} {u : Fin M.ord}
    (ends : u=(primal G e).1 ∨ u=(primal G e).2) : ∃ v, Across (primal G) e u v := by
  rcases ends with rfl|rfl; exact ⟨_,Or.inl rfl⟩; exact ⟨_,Or.inr rfl⟩

private theorem go {M} (G : IsDiskFullerene M h) {x y : Fin M.ord} {e : Edge M} (s : Across (primal G) e x y) (p : Fin M.ord→Bool) :
    p x≠p y ↔ p (primal G e).1≠p (primal G e).2 := by
  rcases s with eq|eq
  · rw [eq]
  · rw [eq]; exact ne_comm

/-- The cut belonging to a retained primal edge changes color on that
edge alone among all retained edges. It separates the two end markers. -/
theorem edge_cuts {M} (G : IsDiskFullerene M h) (hh : 3≤h) {d t : EndPiece M G}
    (splits : ∀ p, ChordHalf G p → ∃ b : Bool,
      (∀ v, vertexSide d.seam d.side v=true → p v=b) ∧ (∀ v, vertexSide t.seam t.side v=true → p v= !b))
    {l r : Fin M.ord} (hl : vertexSide d.seam d.side l=true) (hr : vertexSide t.seam t.side r=true) :
    SpineWalk.Separates (Crossing G) l r := by
  intro u v uv; obtain ⟨e,pe,a,b,de,ai,bi,ch⟩ := uv
  have ab : a≠b := by have ne := left_ne_right G hh e; rcases de with f|f <;> rw [f] at ne; exact ne; exact ne.symm
  obtain ⟨au,bu,_,_⟩ := edge_corners G pe de
  obtain ⟨p,P,_,cross⟩ := incidence_half G hh u au bu ab ai bi ch
  obtain ⟨bound,left,right⟩ := splits p P
  refine ⟨p,by rw [left l hl,right r hr]; cases bound <;> decide,
    (go G pe p).mpr ((cross ai bi de).mpr (Or.inl ⟨rfl,rfl⟩)),?_⟩
  rintro x y ⟨k,pk,c,f,dk,ci,fi,_⟩ diff
  have names := (cross ci fi dk).mp ((go G pk p).mp diff)
  have same : k=e := by
    rcases names with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact uniqueAcross G hh dk de
    · exact uniqueAcross G hh dk de.symm
  subst k
  rcases pk with x|x <;> rcases pe with y|y <;> have pair := Prod.mk.inj (x.symm.trans y) <;> grind

private theorem positions {M} (G : IsDiskFullerene M h) (hh : 3≤h) (c : Face M)
    (i j : Fin M.faces[c.val].length) (rel : (atSide G c i,atSide G c j)∈sides (dualRow G c)) :
    next M.faces[c.val].length i.val=j.val := by
  let R := dualRow G c
  obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp rel
  rw [sides_size] at hk
  rw [side_at _ _ hk,atSide_eq,atSide_eq] at e
  have nd := row_nodup G (noRepeatOnSphere G hh) c
  have pair := Prod.mk.inj e
  have a := index_eq nd hk _ pair.1; have b := index_eq nd _ _ pair.2
  rw [row_length G c] at b; simpa [a] using b

theorem seam_proper {M} (G : IsDiskFullerene M h) (hh : 3≤h) (d : EndPiece M G) : Proper G d.seam.xy := by
  let N := atSide G (apex M)
  have inRow z : IsBoundary G (N z) := by dsimp [N,IsBoundary]; rw [atSide_eq]; exact List.getElem_mem _
  refine ⟨N d.i,N d.j,d.seam.middle,inRow _,inRow _,?_⟩
  obtain ⟨order,_,_,⟨v,_,h₁,h₂⟩,⟨w,hw,outer⟩⟩ := d.proper
  change d.i.val<d.j.val at order
  change d.i.val<v at h₁; change v<d.j.val at h₂
  change w<d.i.val ∨ d.j.val<w at outer
  intro cut
  rcases cut with e|e
  · have f := positions G hh _ _ _ e; unfold next at f; split at f <;> omega
  · have f := positions G hh _ _ _ e; unfold next at f; split at f <;> omega

/-- The endpoint of the seam edge in the chosen terminal half. -/
def RootSpec {M} {G : IsDiskFullerene M h} (d : EndPiece M G) (v : Fin M.ord) :=
  (v=(primal G d.seam.xy).1 ∨ v=(primal G d.seam.xy).2) ∧ vertexSide d.seam d.side v=true

private theorem different_sides {M} {G : IsDiskFullerene M h} (d : EndPiece M G) :
    vertexSide d.seam d.side (primal G d.seam.xy).1 ≠ vertexSide d.seam d.side (primal G d.seam.xy).2 := by
  classical
  have cut := (d.seam.part.crosses d.seam.xy).mp (Or.inr (Or.inl rfl))
  by_cases a : d.seam.part.left (primal G d.seam.xy).1 <;> by_cases b : d.seam.part.left (primal G d.seam.xy).2 <;>
    cases d.side <;> simp_all [vertexSide]

private theorem root_exists {M} {G : IsDiskFullerene M h} (d : EndPiece M G) : ∃ v, RootSpec d v := by
  have diff := different_sides d
  cases e : vertexSide d.seam d.side (primal G d.seam.xy).1 with
  | true => exact ⟨_,Or.inl rfl,e⟩
  | false => exact ⟨_,Or.inr rfl,by cases z : vertexSide d.seam d.side (primal G d.seam.xy).2 <;> simp_all⟩

private theorem root_unique {M} {G : IsDiskFullerene M h} (d : EndPiece M G) {u v} (hu : RootSpec d u) (hv : RootSpec d v) : u=v := by
  obtain ⟨U,pu⟩ := hu; obtain ⟨V,pv⟩ := hv
  have diff := different_sides d
  rcases U with eq|eq <;> rcases V with eq'|eq' <;> rw [eq,eq'] <;> grind

theorem only_seam_at {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) {u v : Fin M.ord} {e : Edge M}
    (sel : vertexSide d.seam d.side u=true) (uv : Across (primal G) e u v) (prop : Proper G e) : e=d.seam.xy := by
  obtain ⟨a,b,ab,ba,bb,ch⟩ := prop
  have yes : vertexSide d.seam d.side (primal G e).1=true ∨ vertexSide d.seam d.side (primal G e).2=true := by
    rcases uv with q|q <;> simp [q,sel]
  exact (d.terminal.seam_or_cycle hh d.seam d.side ba bb ab yes).resolve_left ch

private theorem root_of_selected {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) {u v : Fin M.ord}
    (sel : vertexSide d.seam d.side u=true) (edge : Crossing G u v) : RootSpec d u := by
  obtain ⟨e,uv,prop⟩ := edge
  have equal := only_seam_at hh d sel uv prop
  subst e
  refine ⟨?_,sel⟩
  rcases uv with q|q <;> simp [q]

private theorem not_apex {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u v : Fin M.ord}
    (edge : Crossing G u v) : apex M∉triangle u := by
  obtain ⟨e,gu,a,b,ab,ba,bb,ch⟩ := edge
  have ne : a≠b := by have d := left_ne_right G hh e; rcases ab with q|q <;> rw [q] at d; exact d; exact d.symm
  obtain ⟨au,bu,_,_⟩ := edge_corners G gu ab
  have aw : a≠apex M := fun eq=>row_no_loop G hh _ (eq ▸ ba)
  have bw : b≠apex M := fun eq=>row_no_loop G hh _ (eq ▸ bb)
  intro apexIn
  obtain ⟨r,s,C,_,_,_,hits⟩ := corners_at G hh ((mem_triangle _ _).mp apexIn)
  have ra := (hits _).mp ((mem_triangle _ _).mp au); have rb := (hits _).mp ((mem_triangle _ _).mp bu)
  have H := C.step
  rcases ra with ra|ra|ra <;> rcases rb with rb|rb|rb <;> first | contradiction | apply ch; unfold OnCycle; grind

private theorem pure_of_unmarked {M} (G : IsDiskFullerene M h) (hh : 3≤h) {d t : EndPiece M G}
    (cover : ∀ f, f∈diskInterior G ↔ sectorCore d.seam d.side f=true ∨ sectorCore t.seam t.side f=true)
    {l r : Fin M.ord} (hl : RootSpec d l) (hr : RootSpec t r) {u v : Fin M.ord}
    (ul : u≠l) (ur : u≠r) (edge : Crossing G u v) : Pure G u := by
  intro f hit
  have na : f≠apex M := fun eq => not_apex G hh edge (eq ▸ hit)
  apply Classical.byContradiction; intro no
  have ins := (mem_diskInterior G f).mpr ⟨na,no⟩
  rcases (cover _).mp ins with ds|ts
  · have yes := core_corner_selected d.seam ds u ((mem_triangle _ _).mp hit)
    exact ul (root_unique d (root_of_selected hh d yes edge) hl)
  · have yes := core_corner_selected t.seam ts u ((mem_triangle _ _).mp hit)
    exact ur (root_unique t (root_of_selected hh t yes edge) hr)

private theorem pure_continues {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u v : Fin M.ord}
    (pure : Pure G u) (edge : Crossing G u v) : ∃ w, Crossing G u w ∧ w≠v := by
  obtain ⟨e,uv,a,b,ab,ba,bb,ch⟩ := edge
  have ne : a≠b := by have d := left_ne_right G hh e; rcases ab with q|q <;> rw [q] at d; exact d; exact d.symm
  obtain ⟨au,bu,_,_⟩ := edge_corners G uv ab
  have third : ∃ c∈triangle u, c≠a ∧ c≠b := by
    apply Classical.byContradiction; intro no
    have sub : triangle u⊆[a,b] := by
      intro z m; by_cases za : z=a; simp [za]; by_cases zb : z=b; simp [zb]; exact False.elim (no ⟨z,m,za,zb⟩)
    have nd : (triangle u).Nodup := (List.nodup_finRange _).filter _
    have high := nd.length_le_of_subset sub; rw [triangle_three G hh] at high; simp at high
  obtain ⟨c,cu,ca,cb⟩ := third
  have bc := pure c cu
  have another (z : Face M) (zu : z∈triangle u) (zb : IsBoundary G z) (zc : z≠c)
      (nz : ¬OnCycle (dualRow G (apex M)) z c) : ∃ w, Crossing G u w ∧ w≠v := by
    obtain ⟨k,kd,ke⟩ := common_edge_at G hh zc zu cu
    obtain ⟨w,uw⟩ := opposite G ke
    refine ⟨w,⟨k,uw,z,c,kd,zb,bc,nz⟩,?_⟩
    rintro rfl
    obtain rfl := primal_unique G uv uw
    rcases kd with q|q <;> rcases ab with d|d <;> have pair := Prod.mk.inj (q.symm.trans d) <;> grind
  by_cases ac : OnCycle (dualRow G (apex M)) a c
  · have stop : ¬OnCycle (dualRow G (apex M)) b c := fun x =>
      no_two_outer_sides G hh u au cu bu ca.symm ne cb ba bc bb ac x.symm
    exact another b bu bb cb.symm stop
  · exact another a au ba ca.symm ac

/-- In the equality case, all proper outer chords in their actual order.
Nodes are primal vertices, hence genuine triangular faces of the dual. -/
private theorem from_pieces {M} (G : IsDiskFullerene M h) (hh : 3≤h) (d t : EndPiece M G)
    (cover : ∀ f, f∈diskInterior G ↔ sectorCore d.seam d.side f=true ∨ sectorCore t.seam t.side f=true)
    (splits : ∀ p, ChordHalf G p → ∃ b : Bool, (∀ v, vertexSide d.seam d.side v=true → p v=b) ∧
      (∀ v, vertexSide t.seam t.side v=true → p v= !b)) :
    ∃ l r : Fin M.ord, RootSpec d l ∧ RootSpec t r ∧ ∃ P : SpineWalk.Path (Crossing G) l r,
        ∀ u∈P.middle, Pure G u := by
  obtain ⟨l,hl⟩ := root_exists d; obtain ⟨r,hr⟩ := root_exists t
  have cuts := edge_cuts G hh splits hl.2 hr.2
  obtain ⟨v,rv⟩ := opposite G hr.1
  have start := symmetric G (show Crossing G r v from ⟨_,rv,seam_proper G hh t⟩)
  have ends (x) (leaf : SpineWalk.Leaf (Crossing G) x) : x=l ∨ x=r := by
    obtain ⟨y,ex,limit⟩ := leaf
    by_cases x1 : x=l; exact Or.inl x1
    by_cases x2 : x=r; exact Or.inr x2
    obtain ⟨z,new,diff⟩ := pure_continues G hh (pure_of_unmarked G hh cover hl hr x1 x2 ex) ex
    exact False.elim (diff (limit z new))
  obtain ⟨P⟩ := SpineWalk.path (List.finRange _) List.mem_finRange (Crossing G) (fun _ _ e=>symmetric G e) (irreflexive G) l r cuts ⟨v,start⟩ ends
  refine ⟨l,r,hl,hr,P,?_⟩
  intro x hx
  have nd := P.simple
  have xl : x≠l := fun e=>(List.nodup_cons.mp nd).1 (List.mem_append_left _ (e ▸ hx))
  have xr : x≠r := by
    have sep := (List.nodup_append.mp (List.nodup_cons.mp nd).2).2.2
    exact sep x hx r (by simp)
  obtain ⟨left,right,shape⟩ := List.append_of_mem hx
  cases right with
  | nil =>
    apply pure_of_unmarked G hh cover hl hr xl xr (v:=r)
    apply P.chain
    rw [shape]; simpa [List.append_assoc] using SpineWalk.pair_after (l::left) x r []
  | cons y ys =>
    apply pure_of_unmarked G hh cover hl hr xl xr (v:=y)
    apply P.chain
    rw [shape]; simpa [List.append_assoc] using SpineWalk.pair_after (l::left) x y (ys++[r])

theorem ordered {M} (G : IsDiskFullerene M h) (hh : 3≤h) (cut : HasChord G) (six : M.hexagons=6) :
    ∃ d t : EndPiece M G, ∃ l r : Fin M.ord, RootSpec d l ∧ RootSpec t r ∧
      ∃ P : SpineWalk.Path (Crossing G) l r, ∀ u∈P.middle, Pure G u := by
  obtain ⟨d,t,cover,_,splits⟩ := equality_chain G hh cut six
  exact ⟨d,t,from_pieces G hh d t cover splits⟩

private theorem pure_has_edge {M} {G : IsDiskFullerene M h} (hh : 3≤h) {u : Fin M.ord} (pu : Pure G u) :
    ∃ v, Crossing G u v := by
  obtain ⟨a,b,c,eq⟩ : ∃ a b c, triangle u=[a,b,c] := ⟨_,_,_,List.eq_getElem_of_length_eq_three _ (triangle_three G hh u)⟩
  have nd : (triangle u).Nodup := (List.nodup_finRange _).filter _
  have dif : a≠b ∧ a≠c ∧ b≠c := by simpa [eq,and_assoc] using nd
  have au : a∈triangle u := by simp [eq]
  have bu : b∈triangle u := by simp [eq]
  have cu : c∈triangle u := by simp [eq]
  have make {x y} (xu : x∈triangle u) (yu : y∈triangle u) (xy : x≠y) (nc : ¬OnCycle (dualRow G (apex M)) x y) : ∃ v, Crossing G u v := by
    obtain ⟨e,ce,pe⟩ := common_edge_at G hh xy xu yu
    obtain ⟨v,uv⟩ := opposite G pe
    exact ⟨v,e,uv,x,y,ce,pu x xu,pu y yu,nc⟩
  by_cases ab : OnCycle (dualRow G (apex M)) a b
  · exact make bu cu dif.2.2 (fun bc=>no_two_outer_sides G hh u au bu cu dif.1 dif.2.1 dif.2.2 (pu _ au) (pu _ bu) (pu _ cu) ab bc)
  · exact make au bu dif.1 ab

private theorem end_not_pure {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) {l} (hl : RootSpec d l) : ¬Pure G l := by
  intro yes
  obtain ⟨v,lv⟩ := pure_has_edge hh yes
  obtain ⟨w,lw,wv⟩ := pure_continues G hh yes lv
  obtain ⟨e,ev,pe⟩ := lv; obtain ⟨k,kw,pk⟩ := lw
  have eq := (only_seam_at hh d hl.2 ev pe).trans (only_seam_at hh d hl.2 kw pk).symm
  subst k
  rcases ev with a|a <;> rcases kw with b|b <;> have := Prod.mk.inj (a.symm.trans b) <;> grind

/-- A single choice of end pieces and traversal, including completeness of
both the six-vertex cores and the list of intermediate triangles. -/
structure Ordered {M} (G : IsDiskFullerene M h) where
  leftEnd : EndPiece M G
  rightEnd : EndPiece M G
  left : Fin M.ord
  right : Fin M.ord
  leftRoot : RootSpec leftEnd left
  rightRoot : RootSpec rightEnd right
  leftSize : num (sectorCore leftEnd.seam leftEnd.side)=6
  rightSize : num (sectorCore rightEnd.seam rightEnd.side)=6
  apart : ∀ v, ¬(vertexSide leftEnd.seam leftEnd.side v=true ∧ vertexSide rightEnd.seam rightEnd.side v=true)
  coreCover : ∀ f, f∈diskInterior G ↔ sectorCore leftEnd.seam leftEnd.side f=true ∨ sectorCore rightEnd.seam rightEnd.side f=true
  path : SpineWalk.Path (Crossing G) left right
  pure_iff : ∀ u, u∈path.middle ↔ Pure G u

theorem extract {M} (G : IsDiskFullerene M h) (hh : 3≤h) (cut : HasChord G) (six : M.hexagons=6) : Nonempty (Ordered G) := by
  obtain ⟨d,t,cover,_,splits⟩ := equality_chain G hh cut six
  obtain ⟨l,r,hl,hr,P,pure⟩ := from_pieces G hh d t cover splits
  obtain ⟨b,one,two⟩ := splits (vertexSide d.seam d.side) d.terminal.1
  have tval := one l hl.2
  have apart (v) : ¬(vertexSide d.seam d.side v=true ∧ vertexSide t.seam t.side v=true) := by
    rintro ⟨x,y⟩; have := two v y; cases b <;> simp_all [hl.2]
  have big (q : EndPiece M G) := EndLabels.terminal_six G hh q.seam q.side q.terminal (q.nonempty hh)
  obtain ⟨ds,ts⟩ := exact_end_sizes hh d t apart (big d) (big t) six
  refine ⟨⟨d,t,l,r,hl,hr,ds,ts,apart,cover,P,fun u=>⟨pure u,?_⟩⟩⟩
  intro pu
  obtain ⟨v,edge⟩ := pure_has_edge hh pu
  have coverEdge := P.covers u v edge
  have hit : u∈l::P.middle++[r] := coverEdge.elim (fun m=>(SpineWalk.step_members m).1) (fun m=>(SpineWalk.step_members m).2)
  have ul : u≠l := fun eq=>end_not_pure hh d hl (eq ▸ pu)
  have ur : u≠r := fun eq=>end_not_pure hh t hr (eq ▸ pu)
  simpa [ul,ur] using hit

end DiskFullerene.MiddlePath
