import BlockRouting
import BoundaryState
import SeparatorInput

/-! The sparse comparison graph of a genuine prefix is routed in its planar
shadow. Directed copies of one retained side share its midpoint and read
components use disjoint connected sets of dual spokes. -/
namespace Recognition.ShadowRoutes
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep Overlay OverlayMinor OverlayRead OverlayCoverage
open QuotientDP BoundaryState StateIso Finset BlockRouting

private inductive Strand {P : Type} (sp : List (Edge × P)) : Overlay.Node P → Overlay.Node P → Prop
  | toCentre {e p} : (e,p)∈sp → Strand sp (.point e) (.centre p)
  | toPoint {e p} : (e,p)∈sp → Strand sp (.centre p) (.point e)

private theorem strand_sym {sp : List (Edge×P)} {x y} : Strand sp x y → Strand sp y x
  | .toCentre h => .toPoint h
  | .toPoint h => .toCentre h

private def Anchor (sp : List (Edge×P)) (e : Edge) : Overlay.Node P → Prop
  | .point g => Overlay.decoded sp e g
  | .centre p => ∃a,(e,a)∈sp ∧ Walk (dualLink sp) a p
  | .vertex _ => False

private theorem dual_walk (sp : List (Edge×P)) (e f : Edge) (start : ∃p,(e,p)∈sp) :
    decoded sp e f ↔ Walk (Strand sp) (.point e) (.point f) := by
  constructor
  · rintro ⟨a,b,ea,fb,route⟩
    have toHub {b} (path : Walk (dualLink sp) a b) : Walk (Strand sp) (.centre a) (.centre b) := by
      induction path with
      | refl => exact .refl
      | step _ d ih => obtain ⟨g,gx,gy⟩:=d; exact (ih.step (.toPoint gx)).step (.toCentre gy)
    exact ((Walk.step .refl (.toCentre ea)).trans (toHub route)).step (.toPoint fb)
  · intro walk
    have invariant {y} (w : Walk (Strand sp) (.point e) y) : Anchor sp e y := by
      induction w with
      | refl => obtain ⟨p,h⟩:=start;exact ⟨p,p,h,h,.refl⟩
      | step _ d ih =>
        cases d with
        | toCentre g =>
          obtain ⟨a,b,ea,fb,r⟩:=ih
          exact ⟨a,ea,r.step ⟨_,fb,g⟩⟩
        | toPoint g =>
          obtain ⟨a,ea,r⟩:=ih
          exact ⟨a,_,ea,g,r⟩
    exact invariant walk

private theorem pending_spoke {fs s} (ok : replay (fs.flatMap Face.sides)=some s)
    {e : Edge} (p : e∈s.pending) : ∃h,(e,h)∈spokes fs (retained s) := by
  have h := (counted fs s ok e).1.mpr p
  rw [incidentCount,spokes_read] at h
  obtain ⟨⟨g,z⟩,mem,eq⟩ := List.mem_map.mp (List.count_pos_iff.mp (show 0<_ from h ▸ Nat.zero_lt_one))
  exact ⟨z,eq ▸ mem⟩

private theorem stay {fs s} {x y : Overlay.Node (Patch fs (retained s))}
    (e : Strand (spokes fs (retained s)) x y) : y∈Overlay.vertices fs s := by
  cases e with
  | toCentre sp => exact OverlayRead.centre_mem ⟨_,sp⟩
  | toPoint sp => apply OverlayRead.pin_in; simp [spokes,contacts,List.mem_flatMap] at sp;grind

private def link (E : Fin h ≃ Nodes fs s) (i j : Fin h) :=
  Strand (spokes fs (retained s)) (E i).val (E j).val

private theorem tract (E : Fin h ≃ Nodes fs s) (i j : Fin h) :
    Walk (link E) i j ↔ Walk (Strand (spokes fs (retained s))) (E i).val (E j).val := by
  classical
  refine ⟨fun path => path.map (fun x => (E x).val) (fun _ _ p => p),?_⟩
  intro path
  let pick (a : Overlay.Node (Patch fs (retained s))) := if ha : a∈Overlay.vertices fs s then E.symm ⟨a,ha⟩ else i
  have inSet {a} (mem : a∈Overlay.vertices fs s) : (E (pick a)).val=a := by simp [pick,mem]
  have atNode (z : Fin h) : pick (E z).val=z := by apply E.injective;apply Subtype.ext;exact inSet (E z).property
  have lift {a} (w : Walk (Strand (spokes fs (retained s))) (E i).val a) :
      a∈Overlay.vertices fs s ∧ Walk (link E) i (pick a) := by
    induction w with
    | refl => exact ⟨(E i).property,by rw [atNode]; exact .refl⟩
    | @step x y _ edge ih =>
      have mem := stay edge
      exact ⟨mem,ih.2.step (by change Strand _ (E (pick x)).val (E (pick y)).val; rwa [inSet ih.1,inSet mem])⟩
  simpa only [atNode] using (lift path).2

private theorem site_side {t : State n} (M : BoundaryState.Model fs s t) (e : Side n)
    (present : StateIncidence.hasSide t e=true) : has (retained s) e.1.val e.2.val := by
  have grow {es : List Edge} (sub : es⊆retained s) : has es e.1.val e.2.val → has (retained s) e.1.val e.2.val :=
    fun ⟨d,m,p⟩ => ⟨d,sub m,p⟩
  rcases e with ⟨x,y⟩
  simp only [StateIncidence.hasSide,Bool.or_eq_true,decide_eq_true_eq] at present
  rcases present with (p|p)|⟨⟨u,v⟩,p|p⟩
  · exact grow (pending_sub _) ((M.pending x y).mp p)
  · exact grow (sealed_sub _) ((M.sealed x y).mp p)
  · obtain ⟨d,dm,f,_,dh,_,_⟩ := (M.blocks ..).mp p
    exact ⟨d,pending_sub s dm,dh⟩
  · obtain ⟨d,_,f,fm,_,fh,_⟩ := (M.blocks ..).mp p
    exact ⟨f,pending_sub s fm,fh⟩

private theorem site_vertex {t : State n} (M : BoundaryState.Model fs s t) (x : Fin n)
    (present : StateIncidence.hasVertex t x=true) : live s x.val=true := by
  simp only [StateIncidence.hasVertex,Bool.or_eq_true,bne_iff_ne,decide_eq_true_eq] at present
  rcases present with red|⟨e,inside,hit⟩
  · rw [M.current] at red;split at red
    · assumption
    · contradiction
  · have touched := scope s (retained s) (fun _ h => h) (site_side M e inside)
    rcases hit with eq|eq
    · exact eq ▸ touched.2.1
    · exact eq ▸ touched.2.2

private abbrev Base (t : State n) := Fin (StateIncidence.names t).length
private def item (t : State n) (i : Base t) := (StateIncidence.names t).get i

private theorem selected (t : State n) (i : Base t) : StateIncidence.present t (item t i)=true :=
  (StateIncidence.names_mem t _).mp (List.get_mem ..)

private noncomputable def asNode {t : State n} (M : BoundaryState.Model fs s t) :
    (a : StateIncidence.Item n) → StateIncidence.present t a=true → Nodes fs s
  | .inl x,h => ⟨.vertex x.val,(BoundaryState.hasVertex _).mpr (site_vertex M x h)⟩
  | .inr p,h => ⟨.point (site_side M p h).choose,OverlayRead.pin_in (site_side M p h).choose_spec.1⟩

private noncomputable def pin {t : State n} (M : BoundaryState.Model fs s t) (i : Base t) : Nodes fs s :=
  asNode M (item t i) (selected t i)

private theorem pin_vertex {t : State n} (M : BoundaryState.Model fs s t) (i : Base t)
    (eq : item t i=.inl x) : (pin M i).val=.vertex x.val := by
  have gen (a : StateIncidence.Item n) (m : StateIncidence.present t a=true) (h : a=.inl x) :
      (asNode M a m).val=.vertex x.val := by subst a;rfl
  exact gen _ _ eq

private theorem pin_point {t : State n} (M : BoundaryState.Model fs s t) (i : Base t)
    (eq : item t i=.inr p) : ∃e, (pin M i).val=.point e ∧ ends e p.1.val p.2.val := by
  have gen (a : StateIncidence.Item n) (m : StateIncidence.present t a=true) (h : a=.inr p) :
      ∃e,(asNode M a m).val=.point e ∧ ends e p.1.val p.2.val := by
    subst a
    exact ⟨_,rfl,(site_side M p m).choose_spec.2⟩
  exact gen _ _ eq

private theorem at_point {t : State n} (M : BoundaryState.Model fs s t) (i : Base t)
    (eq : item t i=.inr p) (h : ends e p.1.val p.2.val) : (pin M i).val=.point e := by
  obtain ⟨d,pin,repr⟩ := pin_point M i eq
  exact (same_pair repr h) ▸ pin

private theorem direction {t : State n} (M : BoundaryState.Model fs s t) :
    ∀i j : Base t, SparseCompare.arc (StateIncidence.graph t) (.inl i) (.inl j)=true →
      (shadow fs s).Adj (pin M i) (pin M j) := by
  intro i j edge
  have small (p : Side n) : 2*(t.pending p).toNat+(t.sealed p).toNat<4 := by
    cases t.pending p <;> cases t.sealed p <;> decide
  change (!(SparseCompare.low _ i && SparseCompare.low _ j) && StateIncidence.arc t (item t i) (item t j))=true at edge
  unfold SparseCompare.low at edge
  change (!(decide (StateIncidence.tint t (item t i)<4) && decide (StateIncidence.tint t (item t j)<4)) && _)=true at edge
  cases p : item t i with
  | inl x =>
    cases q : item t j with
    | inl y => simp [p,q,StateIncidence.arc] at edge
    | inr e =>
      obtain ⟨d,pt,ends⟩ := pin_point M j q
      apply (OverlayRead.primal _ _ (pin_vertex M i p) pt).mpr
      simp [p,q,StateIncidence.arc,StateIncidence.tint] at edge
      rcases ends with ⟨l,r⟩|⟨l,r⟩ <;> simp [touches,edge,l]
  | inr e =>
    cases q : item t j with
    | inl x =>
      obtain ⟨d,pt,ends⟩ := pin_point M i p
      apply (shadow fs s).adj_symm;apply (OverlayRead.primal _ _ (pin_vertex M j q) pt).mpr
      simp [p,q,StateIncidence.arc,StateIncidence.tint] at edge
      rcases ends with ⟨l,r⟩|⟨l,r⟩ <;> simp [touches,←edge,r]
    | inr f => simp [p,q,StateIncidence.tint,small] at edge


private def orientation (t : State n) (i : Base t) : Bool :=
  match item t i with
  | .inl _ => false
  | .inr p => decide (p.1.val<p.2.val)

private theorem pin_unique {t : State n} (M : BoundaryState.Model fs s t) (i j : Base t)
    (same : pin M i=pin M j) (orient : orientation t i=orientation t j) : i=j := by
  have points := congrArg Subtype.val same
  have inj : Function.Injective (item t) := List.nodup_iff_injective_get.mp (StateIncidence.names_nd t)
  apply inj
  cases eq : item t i with
  | inl x =>
    rw [pin_vertex M i eq] at points
    cases eq' : item t j with
    | inl y => rw [pin_vertex M j eq'] at points;exact congrArg Sum.inl (Fin.ext (Overlay.Node.vertex.inj points))
    | inr p => obtain ⟨e,he,_⟩:=pin_point M j eq';rw [he] at points;contradiction
  | inr p =>
    obtain ⟨e,he,rp⟩ := pin_point M i eq
    rw [he] at points
    cases eq' : item t j with
    | inl y => rw [pin_vertex M j eq'] at points;contradiction
    | inr q =>
      obtain ⟨f,hf,rq⟩ := pin_point M j eq';rw [hf] at points
      obtain rfl := Overlay.Node.point.inj points
      simp only [orientation,eq,eq',decide_eq_decide] at orient
      have order := e.increasing
      apply congrArg Sum.inr
      apply Prod.ext <;> apply Fin.ext <;> rcases rp with ⟨l,r⟩|⟨l,r⟩ <;> rcases rq with ⟨l',r'⟩|⟨l',r'⟩ <;> omega

private def enabled {t : State n} (i : Base t) := ∃p,item t i=.inr p ∧ t.pending p=true

private theorem same_at {t : State n} (M : BoundaryState.Model fs s t) (ok : replay (fs.flatMap Face.sides)=some s)
    (E : Fin h ≃ Nodes fs s) {p q : Side n} {e f : Edge} (rp : ends e p.1.val p.2.val) (rq : ends f q.1.val q.2.val)
    {u v : Fin h} (pt : (E u).val=.point e) (qt : (E v).val=.point f) :
    t.blocks p q=true ↔ t.pending p=true ∧ t.pending q=true ∧ Walk (link E) u v := by
  rcases p with ⟨a,b⟩;rcases q with ⟨c,d⟩
  rw [M.blocks,M.pending,M.pending,BoundaryState.relation rp rq]
  have first : has s.pending a.val b.val ↔ e∈s.pending :=
    ⟨fun ⟨g,m,p⟩ => same_pair p rp ▸ m,fun m => ⟨e,m,rp⟩⟩
  have second : has s.pending c.val d.val ↔ f∈s.pending :=
    ⟨fun ⟨g,m,p⟩ => same_pair p rq ▸ m,fun m => ⟨f,m,rq⟩⟩
  rw [first,second,tract,pt,qt]
  by_cases ep : e∈s.pending <;> by_cases fp : f∈s.pending <;> simp [ep,fp]
  exact ((blocks_correct fs s ep fp).symm).trans (dual_walk _ _ _ (pending_spoke ok ep))

noncomputable def host (fs : List Face) (s : Inventory) (E : Fin h ≃ Nodes fs s) : Colored h := by
  classical
  exact ⟨fun _ => 0,fun i j => decide ((shadow fs s).Adj (E i) (E j))⟩

theorem routes {t : State n} (M : BoundaryState.Model fs s t) (ok : replay (fs.flatMap Face.sides)=some s)
    (E : Fin h ≃ Nodes fs s) : Nonempty (Routes (StateIncidence.graph t) (host fs s E) 2) := by
  classical
  let site (i : Base t) := E.symm (pin M i)
  have proj (i) : E (site i)=pin M i := E.apply_symm_apply _
  refine ⟨⟨site,enabled,link E,fun _ _ h => strand_sym h,?_,?_,?_,?_⟩⟩
  · intro x y edge
    left;change decide ((shadow fs s).Adj (E x) (E y))=true
    apply decide_eq_true
    change Strand _ (E x).val (E y).val at edge
    generalize hx : (E x).val=a at edge
    generalize hy : (E y).val=b at edge
    cases edge with
    | toCentre m => exact (shadow fs s).adj_symm ((OverlayRead.spoke _ _ hy hx).mpr m)
    | toPoint m => exact (OverlayRead.spoke _ _ hx hy).mpr m
  · intro i j edge
    right;left;change decide ((shadow fs s).Adj (E (site i)) (E (site j)))=true
    exact decide_eq_true (by rw [proj,proj];exact direction M i j edge)
  · intro i j
    rw [SparseCompare.state_row]
    change (∃p q,item t i=.inr p ∧ item t j=.inr q ∧ t.blocks p q=true) ↔ _
    have classify {p q} (ip : item t i=.inr p) (jq : item t j=.inr q) :
        t.blocks p q=true ↔ t.pending p=true ∧ t.pending q=true ∧ Walk (link E) (site i) (site j) := by
      obtain ⟨e,pt,rp⟩ := pin_point M i ip
      obtain ⟨f,qt,rq⟩ := pin_point M j jq
      exact same_at M ok E rp rq (by rw [proj];exact pt) (by rw [proj];exact qt)
    constructor
    · rintro ⟨p,q,ip,jq,yes⟩
      obtain ⟨p_,q_,w⟩ := (classify ip jq).mp yes
      exact ⟨⟨p,ip,p_⟩,⟨q,jq,q_⟩,w⟩
    · rintro ⟨⟨p,ip,p_⟩,⟨q,jq,q_⟩,w⟩
      exact ⟨p,q,ip,jq,(classify ip jq).mpr ⟨p_,q_,w⟩⟩
  · intro x
    have bound : (univ.filter (fun i => site i=x)).card ≤ (univ : Finset Bool).card := by
      apply card_le_card_of_injOn (orientation t) (fun _ _ => mem_univ _)
      intro i hi j hj o
      apply pin_unique M i j _ o
      have eq := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
      exact E.symm.injective eq
    simpa using bound

/-- Two directed copies of a retained side and one connected component
lane suffice, regardless of the prefix or its number of faces. -/
theorem congestion_three {t : State n} (M : BoundaryState.Model fs s t) (ok : replay (fs.flatMap Face.sides)=some s)
    (E : Fin h ≃ Nodes fs s) :
    Nonempty (MinorWidth.Model (SparseCompare.graph (StateIncidence.graph t)) (host fs s E) 3) := by
  obtain ⟨P⟩ := routes M ok E
  exact BlockRouting.model _ _ P


private theorem model_order {A : Colored n} {H : Colored m} {c} (M : MinorWidth.Model A H c) : n≤c*m := by
  classical
  let pick (i) := (M.nonempty i).choose
  have inside (i) : pick i∈M.pieces i := (M.nonempty i).choose_spec
  have count := Finset.card_le_mul_card_image_of_maps_to (f := pick) (s := univ) (t := univ)
    (fun _ _ => mem_univ _) c (fun x _ => (card_le_card (show
      ((univ.filter (fun i : Fin n => pick i=x)))⊆univ.filter (fun i => x∈M.pieces i) from
        fun i hi => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2 ▸ inside i⟩)).trans (M.load x))
  simpa using count

private theorem sorted_host {fs s} (E : Fin h ≃ Nodes fs s) (sep : SeparatorInput.WeightedPlanarSeparator)
    (planar : LeanPool.K5MinorFreeChoosability.IsPlanar (shadow fs s)) :
    Outline.Separators (List.range h) (MinorWidth.adjacency (host fs s E)) (fun _ => 1) := by
  classical
  let R := (host fs s E).edge
  let G := SparseBoundary.Graph.ofRelation R
  have rel : ∀i j,G.adj i j=R i j := SparseBoundary.Graph.adj_ofRelation R
    (fun i j => by simp [R,host,SimpleGraph.adj_comm]) (fun i => by simp [R,host])
  have iso : Wagner.toSimple G ≃g shadow fs s :=
    { E with map_rel_iff' := by intro i j; rw [Wagner.toSimple_adj,rel];simp [R,host] }
  have inst : Finite (Nodes fs s) := Finite.of_equiv _ E
  have flat := (Wagner.planar_iff_rotation G).mpr (LeanPool.K5MinorFreeChoosability.isPlanar_of_iso planar iso)
  have same : SeparatorInput.adjacent G=MinorWidth.adjacency (host fs s E) := by
    funext x y; simp only [MinorWidth.adjacency,SeparatorInput.adjacent,rel,R]
  rw [←same]; exact sep G flat _ (by simp)

/-- Only the general weighted planar separator theorem appears as a
geometric input. Each actual prefix has at most 30b comparison vertices
and an elimination hierarchy of depth at most 84(√(10b)+1). -/
theorem prefix_hierarchy {v f : Nat} (C : PlanarDegrees.Topology.ClosedTrace v f)
    (terminal : (f+1)+4=2*(v+1)) (read todo : List Face) (perm : (read++todo).Perm (List.ofFn C.faces))
    (ok : replay (read.flatMap Face.sides)=some s) {t : State n} (M : BoundaryState.Model read s t)
    (sep : SeparatorInput.WeightedPlanarSeparator) :
    let b := (activeNames s).eraseDups.length
    let A := StateIncidence.graph t
    (StateIncidence.names t).length+(SparseCompare.blocks A).length≤30*b ∧
      Nonempty (MinorWidth.Hierarchy (SparseCompare.graph A) (84*((10*b).sqrt+1))) := by
  classical
  let N := Nodes read s
  let _ : Fintype N := Fintype.ofFinset (Overlay.vertices read s).toFinset (fun _ => List.mem_toFinset)
  let h := Fintype.card N
  let E : Fin h ≃ N := (Fintype.equivFin N).symm
  let b := (activeNames s).eraseDups.length
  have sparse := SparseOverlay.retained_bound C terminal read todo perm s ok
  have span := (Overlay.size read s ok).2
  have num : h≤(Overlay.vertices read s).length := by
    have c : h=(Overlay.vertices read s).toFinset.card :=
      Fintype.card_ofFinset (p := {x | x∈Overlay.vertices read s}) (Overlay.vertices read s).toFinset (fun _ => List.mem_toFinset)
    exact c ▸ List.toFinset_card_le _
  have bound : h≤10*b := by dsimp [b];omega
  obtain ⟨model⟩:=congestion_three M ok E
  have size:=model_order model
  have sorted:=sorted_host E sep (TraceOverlay.prefix_planar C terminal read todo perm ok)
  obtain ⟨H⟩:=MinorWidth.from_separator _ sorted
  obtain ⟨D⟩:=MinorWidth.contract _ _ model H
  refine ⟨by omega,⟨{D with cap := fun key => (D.cap key).trans ?_}⟩⟩
  have u:=Nat.sqrt_le_sqrt bound
  change 3*(28*(h.sqrt+1))≤84*((10*b).sqrt+1)
  omega

theorem transfer {A : Colored n} {B : Colored m} (eq : StateIso.Iso A B) (D : MinorWidth.Hierarchy B w) :
    Nonempty (MinorWidth.Hierarchy A w) := by
  obtain ⟨p,c,e⟩:=eq
  let home (i) := D.home (p i)
  refine ⟨⟨home,fun i j edge => D.adjacent _ _ (e i j ▸ edge),?_⟩⟩
  intro key
  have map_ : (MinorWidth.spine home key).map p.toEmbedding=MinorWidth.spine D.home key := by
    ext i;obtain ⟨j,rfl⟩:=p.surjective i;simp [MinorWidth.spine,home]
  simpa only [←map_,Finset.card_map] using D.cap key

/-- The same width bound holds for every renamed table representative. -/
theorem same_transfer {r t : State n} (same : Same r t)
    (D : MinorWidth.Hierarchy (SparseCompare.graph (StateIncidence.graph t)) w) :
    Nonempty (MinorWidth.Hierarchy (SparseCompare.graph (StateIncidence.graph r)) w) :=
  transfer ((SparseCompare.graph_iff _ _).mpr ((StateIncidence.same_iff ..).mp same).2.2.2) D

end Recognition.ShadowRoutes
