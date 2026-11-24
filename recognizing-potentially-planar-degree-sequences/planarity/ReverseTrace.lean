import TracePlanarity
import TightFaces
import FacialRotation

/-! Construct a face-ordered degree certificate from the original vertices
of a labelled triangulation. -/
namespace Recognition.ReverseTrace
open PlanarDegrees.Frontier PlanarDegrees.Topology Recognition.Witness SparseBoundary

private abbrev Cell (M : Rigidity.Map (Fin n)) :=
  {p : Fin n × Fin n × Fin n // p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ M.face p.1 p.2.1 p.2.2}
private def member {M : Rigidity.Map (Fin n)} (t : Cell M) (x : Fin n) :=
  x=t.val.1 ∨ x=t.val.2.1 ∨ x=t.val.2.2

private theorem extCell {M : Rigidity.Map (Fin n)} {p q : Cell M}
    (same : ∀ x, member p x ↔ member q x) : p=q := by
  obtain ⟨⟨a,b,c⟩,ab,bc,_⟩ := p
  obtain ⟨⟨x,y,z⟩,xy,yz,_⟩ := q
  change a<b at ab
  change b<c at bc
  change x<y at xy
  change y<z at yz
  simp only [member] at same
  have h₁ := (same a).mp (Or.inl rfl)
  have h₂ := (same b).mp (Or.inr (Or.inl rfl))
  have h₃ := (same c).mp (Or.inr (Or.inr rfl))
  apply Subtype.ext; simp [Prod.ext_iff]; omega

private theorem normalized (M : Rigidity.Map (Fin n)) {a b c : Fin n} (h : M.face a b c) :
    ∃ t : Cell M, ∀ x, member t x ↔ x=a ∨ x=b ∨ x=c := by
  have ab := M.distinct h
  have bc := M.distinct (M.rot h)
  have ca := M.distinct (M.rot (M.rot h))
  have build {i j k : Fin n} (lt : i<j) (lt' : j<k) (face : M.face i j k)
      (mem : ∀ x, (x=i ∨ x=j ∨ x=k) ↔ x=a ∨ x=b ∨ x=c) :
      ∃ t : Cell M, ∀ x, member t x ↔ x=a ∨ x=b ∨ x=c :=
    ⟨⟨(i,j,k),lt,lt',face⟩,mem⟩
  by_cases hs : a<b
  · by_cases ht : b<c
    · exact build hs ht h (by grind)
    · by_cases hu : a<c
      · exact build hu (by omega) (M.flip (M.rot (M.rot h))) (by grind)
      · exact build (by omega) hs (M.rot (M.rot h)) (by grind)
  · by_cases ht : a<c
    · exact build (by omega) ht (M.flip h) (by grind)
    · by_cases hu : b<c
      · exact build hu (by omega) (M.rot h) (by grind)
      · exact build (by omega) (by omega) (M.flip (M.rot h)) (by grind)

private noncomputable def normal (M : Rigidity.Map (Fin n)) {a b c : Fin n} (h : M.face a b c) :=
  (normalized M h).choose
private theorem mem_normal {M : Rigidity.Map (Fin n)} {a b c : Fin n} (h : M.face a b c) (x) :
    member (normal M h) x ↔ x=a ∨ x=b ∨ x=c := (normalized M h).choose_spec x

private def color (A : Graph n) (d : Edge) : Bool :=
  if h : d.hi<n then A.adj ⟨d.lo,Nat.lt_trans d.increasing h⟩ ⟨d.hi,h⟩ else false

private def row {M : Rigidity.Map (Fin n)} (A : Graph n) (t : Cell M) : Face :=
  let x := t.val.1
  let y := t.val.2.1
  let z := t.val.2.2
  ⟨x,y,z,t.property.1,t.property.2.1,A.adj x y,A.adj x z,A.adj y z⟩

private theorem row_corner {M : Rigidity.Map (Fin n)} (A : Graph n) (t : Cell M) (x : Fin n) :
    x.val ∈ cornerNames (row A t) ↔ member t x := by simp [row,cornerNames,member,Fin.ext_iff]

private theorem row_side {M : Rigidity.Map (Fin n)} (A : Graph n) (t : Cell M) (d : Edge) :
    d ∈ sideNames (row A t) ↔
    (∃ x : Fin n, x.val=d.lo ∧ member t x) ∧ (∃ y : Fin n, y.val=d.hi ∧ member t y) := by
  obtain ⟨⟨a,b,c⟩,ab,bc,h⟩ := t
  change a<b at ab
  change b<c at bc
  cases d with
  | mk lo hi lh =>
    simp [sideNames,row,Face.sides,member,Edge.mk.injEq,Fin.ext_iff] at *
    constructor
    · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> grind
    · rintro ⟨⟨x,hx,mem⟩,⟨y,hy,mem'⟩⟩; omega

private theorem row_colored {M : Rigidity.Map (Fin n)} (A : Graph n) (t : Cell M)
    {a : Event} (mem : a ∈ (row A t).sides) : a.red=color A a.edge := by
  rcases t with ⟨⟨x,y,z⟩,h⟩
  simp only [row,Face.sides,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl <;> simp [color]

private theorem third {M : Rigidity.Map (Fin n)} {t : Cell M} {a b : Fin n}
    (h : member t a) (j : member t b) (ne : a≠b) : ∃ c, ∃ hf : M.face a b c, t=normal M hf := by
  obtain ⟨⟨x,y,z⟩,xy,yz,hf⟩ := t
  have ex {a b c : Fin n} (g : M.face a b c) (eq : ∀ u, (u=x ∨ u=y ∨ u=z) ↔ u=a ∨ u=b ∨ u=c) :
      ∃ c, ∃ g : M.face a b c, (⟨(x,y,z),xy,yz,hf⟩ : Cell M)=normal M g :=
    ⟨c,g,extCell (fun u => (eq u).trans (mem_normal g u).symm)⟩
  simp only [member] at h j
  rcases h with rfl|rfl|rfl <;> rcases j with rfl|rfl|rfl <;>
    first | contradiction | exact ex hf (by grind) | exact ex (M.rot hf) (by grind) |
      exact ex (M.rot (M.rot hf)) (by grind) | exact ex (M.flip hf) (by grind) |
      exact ex (M.flip (M.rot hf)) (by grind) | exact ex (M.flip (M.rot (M.rot hf))) (by grind)

private theorem paired {M : Rigidity.Map (Fin n)} (A : Graph n) (q : Fin (f+1) ≃ Cell M)
    (d : Edge) : occurrences (sideTrace (row A ∘ q)) d=0 ∨ occurrences (sideTrace (row A ∘ q)) d=2 := by
  classical
  let fs := row A ∘ q
  let hits (i : Fin (f+1)) := d ∈ sideNames (fs i)
  have eq := face_fiber_length fs d
  change occurrences (sideTrace fs) d=0 ∨ occurrences (sideTrace fs) d=2
  rw [←eq]
  change ((List.finRange (f+1)).filter (fun i => decide (hits i))).length=0 ∨ _
  by_cases has : ∃ i, hits i
  · obtain ⟨i,hi⟩ := has
    obtain ⟨⟨a,ha,am⟩,⟨b,hb,bm⟩⟩ := (row_side A (q i) d).mp hi
    have ab : a≠b := by have := d.increasing; omega
    obtain ⟨c,hc,_⟩ := third am bm ab
    obtain ⟨c',ne,hc',both⟩ := M.twoSides hc
    let j := q.symm (normal M hc)
    let k := q.symm (normal M hc')
    have jk : j≠k := by
      intro eq
      have equiv := q.symm.injective eq
      have mem := (mem_normal hc c).mpr (by simp)
      rw [equiv,mem_normal] at mem
      have ac := M.distinct (M.rot (M.rot hc))
      have bc := M.distinct (M.rot hc)
      grind
    have keep {u} (h : M.face a b u) : hits (q.symm (normal M h)) := by
      change d ∈ sideNames (row A (q (q.symm (normal M h))))
      rw [q.apply_symm_apply,row_side]
      exact ⟨⟨a,ha,(mem_normal h _).mpr (by simp)⟩,⟨b,hb,(mem_normal h _).mpr (by simp)⟩⟩
    have iff (t) : hits t ↔ t=j ∨ t=k := by
      constructor
      · intro ht
        obtain ⟨⟨x,hx,mx⟩,⟨y,hy,my⟩⟩ := (row_side A (q t) d).mp ht
        obtain rfl : x=a := Fin.ext (hx.trans ha.symm)
        obtain rfl : y=b := Fin.ext (hy.trans hb.symm)
        obtain ⟨w,hw,eq⟩ := third mx my ab
        rcases both w hw with rfl|rfl
        · exact Or.inl (q.eq_symm_apply.mpr eq)
        · exact Or.inr (q.eq_symm_apply.mpr eq)
      · rintro (rfl|rfl); exact keep hc; exact keep hc'
    right
    let xs := (List.finRange (f+1)).filter (fun i => decide (hits i))
    have nd : xs.Nodup := (List.nodup_finRange _).filter _
    have seteq : xs.toFinset={j,k} := by ext x; simp [xs,iff]
    change xs.length=2
    rw [←List.toFinset_card_of_nodup nd,seteq,Finset.card_pair jk]
  · left; have none (i) : ¬hits i := fun h => has ⟨i,h⟩
    simp [none]

private theorem within {M : Rigidity.Map (Fin n)} (A : Graph n) {a b c d : Fin n}
    (h : M.face a b c) (j : M.face a b d) :
    ∃ e, e ∈ sideNames (row A (normal M h)) ∧ e ∈ sideNames (row A (normal M j)) ∧ joins e a.val b.val := by
  have mem {w} (g : M.face a b w) : member (normal M g) a ∧ member (normal M g) b :=
    ⟨(mem_normal g _).mpr (by simp),(mem_normal g _).mpr (by simp)⟩
  have mh := mem h
  have mj := mem j
  rcases lt_or_gt_of_ne (M.distinct h) with lt|gt
  · let e : Edge := ⟨a,b,lt⟩
    exact ⟨e,(row_side ..).mpr ⟨⟨_,rfl,mh.1⟩,⟨_,rfl,mh.2⟩⟩,
      (row_side ..).mpr ⟨⟨_,rfl,mj.1⟩,⟨_,rfl,mj.2⟩⟩,by simp [e,joins]⟩
  · let e : Edge := ⟨b,a,gt⟩
    exact ⟨e,(row_side ..).mpr ⟨⟨_,rfl,mh.2⟩,⟨_,rfl,mh.1⟩⟩,
      (row_side ..).mpr ⟨⟨_,rfl,mj.2⟩,⟨_,rfl,mj.1⟩⟩,by simp [e,joins]⟩

private theorem connected {M : Rigidity.Map (Fin n)} (A : Graph n) (q : Fin (f+1) ≃ Cell M)
    (i : Fin (f+1)) : Walk (shared (row A ∘ q)) 0 i := by
  let idx {a b c} (h : M.face a b c) := q.symm (normal M h)
  have own (z) : idx (q z).property.2.2 = z := by
    have eq : normal M (q z).property.2.2=q z := extCell (fun u => mem_normal _ u)
    simp [idx,eq]
  let init := (q 0).property.2.2
  let goal := (q i).property.2.2
  have go {t : Rigidity.Triangle (Fin n)} (p : Rigidity.Walk M.face
      ⟨(q 0).val.1,(q 0).val.2.1,(q 0).val.2.2⟩ t) :
      ∃ h : M.face t.a t.b t.c, Walk (shared (row A ∘ q)) 0 (idx h) := by
    induction p with
    | nil => exact ⟨init,by rw [show idx init = 0 from own 0]; exact .refl⟩
    | rot _ ih =>
      obtain ⟨h,reach⟩ := ih
      have eq : normal M (M.rot h)=normal M h := extCell (fun u => by simp only [mem_normal]; grind)
      exact ⟨M.rot h,by rw [show idx (M.rot h)=idx h from congrArg q.symm eq]; exact reach⟩
    | flip _ ih =>
      obtain ⟨h,reach⟩ := ih
      have eq : normal M (M.flip h)=normal M h := extCell (fun u => by simp only [mem_normal]; grind)
      exact ⟨M.flip h,by rw [show idx (M.flip h)=idx h from congrArg q.symm eq]; exact reach⟩
    | cross _ g ih =>
      obtain ⟨h,reach⟩ := ih
      refine ⟨g,?_⟩
      by_cases eq : idx h=idx g
      · exact eq ▸ reach
      obtain ⟨e,t,w,_⟩ := within A h g
      apply reach.step
      exact ⟨eq,e,by simpa [idx] using t,by simpa [idx] using w⟩
  obtain ⟨_,done⟩ := go (M.connected init goal)
  exact own i ▸ done

private theorem seen {M : Rigidity.Map (Fin n)} (A : Graph n) (q : Fin (f+1) ≃ Cell M) (x y : Fin n) :
    (∃ e ∈ (sideTrace (row A ∘ q)).map Event.edge, joins e x y) ↔ M.adj x y := by
  have mem (d) : d ∈ (sideTrace (row A ∘ q)).map Event.edge ↔ ∃ t : Cell M, d ∈ sideNames (row A t) := by
    simp only [sideTrace,sideNames,List.mem_map,List.mem_flatMap,List.mem_finRange,true_and,Function.comp_apply]
    constructor
    · rintro ⟨a,⟨i,hi⟩,rfl⟩; exact ⟨q i,a,hi,rfl⟩
    · rintro ⟨t,a,ha,rfl⟩; exact ⟨a,⟨q.symm t,by simpa using ha⟩,rfl⟩
  constructor
  · rintro ⟨d,hd,linked⟩
    obtain ⟨t,ht⟩ := (mem d).mp hd
    obtain ⟨⟨u,hu,mu⟩,⟨v,hv,mv⟩⟩ := (row_side A t d).mp ht
    have ne : u≠v := by have := d.increasing; omega
    have ⟨w,face,_⟩ := third mu mv ne
    simp only [joins,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at linked
    rcases linked with ⟨hx,hy⟩|⟨hy,hx⟩
    · exact ⟨w,Fin.ext (hu.trans hx) ▸ Fin.ext (hv.trans hy) ▸ face⟩
    · exact ⟨w,Fin.ext (hu.trans hy) ▸ Fin.ext (hv.trans hx) ▸ M.flip face⟩
  · rintro ⟨w,h⟩
    obtain ⟨d,hd,_,j⟩ := within A h h
    exact ⟨d,(mem _).mpr ⟨_,hd⟩,j⟩

theorem red_mem (p : List Event) (col : Edge → Bool) (h : ∀ a∈p, a.red=col a.edge) (d : Edge) :
    d ∈ reds p ↔ d ∈ p.map Event.edge ∧ col d := by
  induction p with
  | nil => simp [reds]
  | cons a p ih =>
    have c := h a (by simp)
    specialize ih (fun x mem => h x (by simp [mem]))
    have absent : occurrences p a.edge=0 ↔ a.edge ∉ p.map Event.edge := List.count_eq_zero
    by_cases eq : a.edge=d
    · subst d
      by_cases ht : a.edge∈p.map Event.edge <;> cases b : col a.edge <;>
        simp only [reds,absent,c,b,ht,List.map_cons,List.mem_cons] <;> simp_all
    · unfold reds; split <;> simp only [List.map_cons,List.mem_cons,Ne.symm eq,false_or,ih]

private theorem color_at (A : Graph n) (d : Edge) (x y : Fin n) (j : joins d x y) :
    color A d = A.adj x y := by
  simp only [joins,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at j
  rcases j with ⟨a,b⟩|⟨a,b⟩
  · simp [color,a,b]
  · simp [color,a,b,A.adj_comm y x]

private theorem ledger_seen {p : List Event} {s : Inventory} (ok : replay p=some s) (empty : s.pending=[]) (d) :
    d ∈ s.sealed ↔ d ∈ p.map Event.edge := by
  have inv := replay_accurate ok
  have cap := inv.cap d
  have pending := inv.pending d
  simp [empty] at pending
  rw [inv.sealed,← List.count_pos_iff]; change occurrences p d=2 ↔ 0<occurrences p d
  omega

private theorem of_enum (M : Rigidity.Map (Fin (v+1))) (A : Graph (v+1))
    (sub : ∀ x y, A.adj x y → M.adj x y) (q : Fin (f+1) ≃ Cell M) :
    ∃ C : ClosedTrace v f, witnessGraph C=A ∧ ∀ x y, (host C).adj x y ↔ M.adj x y := by
  classical
  let fs := row A ∘ q
  obtain ⟨s,hs,empty⟩ := paired_iff_closed.mp (paired A q)
  have covered (x : Fin (v+1)) : ∃ i, x.val ∈ cornerNames (fs i) := by
    obtain ⟨b,c,h⟩ := M.incident x
    refine ⟨q.symm (normal M h),?_⟩
    simpa only [fs,Function.comp_apply,q.apply_symm_apply,row_corner,mem_normal] using
      (show x=x ∨ x=b ∨ x=c from .inl rfl)
  let C : ClosedTrace v f := ⟨fs,fun i => (q i).val.2.2.isLt,covered,connected A q,s,hs,empty⟩
  have colored (u) (hu : u ∈ sideTrace fs) : u.red=color A u.edge := by
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hu
    exact row_colored A (q i) hi
  refine ⟨C,Graph.eq_of_adj ?_,?_⟩
  · intro x y
    apply Bool.eq_iff_iff.mpr
    rw [witnessGraph,graph_adj]
    change (∃ d ∈ reds (sideTrace fs), joins d x y) ↔ A.adj x y
    constructor
    · rintro ⟨d,hd,j⟩
      have h := ((red_mem _ _ colored _).mp hd).2
      exact (color_at A d x y j) ▸ h
    · intro edge
      obtain ⟨d,hd,j⟩ := (seen A q x y).mpr (sub _ _ edge)
      exact ⟨d,(red_mem _ _ colored _).mpr ⟨hd,(color_at A d x y j).symm ▸ edge⟩,j⟩
  · intro x y
    rw [host,graph_adj,←seen A q x y]
    simp only [C,ledger_seen hs empty]

open Recognition.Wagner LeanPool.K5MinorFreeChoosability

private theorem count_edges {v f} (C : ClosedTrace v f) (H : SimpleGraph (Fin (v+1)))
    (adj : ∀ x y, (host C).adj x y ↔ H.Adj x y) : C.ledger.sealed.length=Nat.card H.edgeSet := by
  classical
  obtain ⟨G,_,he⟩ := C.gluing
  let keys := C.ledger.sealed
  let ed (d : Fin keys.length) := keys[d.val]
  let ends := G.primal
  have ordered (d : Fin keys.length) : (ends d).1<(ends d).2 := by
    have h₁ := congrArg Prod.fst (he d)
    have h₂ := congrArg Prod.snd (he d)
    change (ends d).1.val=(ed d).lo at h₁
    change (ends d).2.val=(ed d).hi at h₂
    change (ends d).1.val < (ends d).2.val
    rw [h₁,h₂]; exact (ed d).increasing
  have join_iff (d : Fin keys.length) (x y : Fin (v+1)) :
      joins (ed d) x y ↔ ends d=(x,y) ∨ ends d=(y,x) := by
    have h₁ := congrArg Prod.fst (he d)
    have h₂ := congrArg Prod.snd (he d)
    change (ends d).1.val=(ed d).lo at h₁
    change (ends d).2.val=(ed d).hi at h₂
    simp [Prod.ext_iff,Fin.ext_iff,joins,h₁,h₂]
  have exists_edge (x y) : H.Adj x y ↔ ∃ d, ends d=(x,y) ∨ ends d=(y,x) := by
    rw [←adj,host,graph_adj]
    constructor
    · rintro ⟨a,ha,h⟩; obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem ha
      exact ⟨⟨j,hj⟩,(join_iff _ _ _).mp h⟩
    · rintro ⟨d,h⟩; exact ⟨ed d,List.getElem_mem _,(join_iff _ _ _).mpr h⟩
  let edge (d : Fin keys.length) : H.edgeSet :=
    ⟨s((ends d).1,(ends d).2),(exists_edge _ _).mpr ⟨d,Or.inl rfl⟩⟩
  have bij : Function.Bijective edge := by
    constructor
    · intro i j eq
      have hh := Sym2.eq_iff.mp (congrArg Subtype.val eq)
      have h₁ := ordered i
      have h₂ := ordered j
      change (ends i).1=(ends j).1 ∧ (ends i).2=(ends j).2 ∨ (ends i).1=(ends j).2 ∧ (ends i).2=(ends j).1 at hh
      have same : ends i=ends j := by
        rcases hh with ⟨a,b⟩|⟨a,b⟩
        · exact Prod.ext a b
        · omega
      have eqEd : ed i=ed j := by
        have spec := (he i).symm.trans ((congrArg (fun t : Fin (v+1) × Fin (v+1) => (t.1.val,t.2.val)) same).trans (he j))
        have extEdge (x y : Edge) (h : (x.lo,x.hi)=(y.lo,y.hi)) : x=y := by cases x; cases y; simp_all
        exact extEdge _ _ spec
      have nd : keys.Nodup := (inventory_counts C.accepted).2.1
      exact Fin.ext ((nd.idxOf_getElem i.val i.isLt).symm.trans ((congrArg keys.idxOf eqEd).trans (nd.idxOf_getElem j.val j.isLt)))
    · rintro ⟨t,ht⟩
      induction t using Sym2.ind with
      | h x y =>
        obtain ⟨d,ab|ba⟩ := (exists_edge x y).mp ht
        · refine ⟨d,Subtype.ext ?_⟩; change s((ends d).1,(ends d).2)=_; rw [ab]
        · refine ⟨d,Subtype.ext ?_⟩; change s((ends d).1,(ends d).2)=_; simp [ba,Sym2.eq_swap]
  simpa using Nat.card_eq_of_bijective edge bij

private theorem trace_of_tight_map {v} (A K : Graph (v+1)) (M : Rigidity.Map (Fin (v+1)))
    (M_adj : ∀ x y, M.adj x y ↔ K.adj x y) (inc : ∀ x y, A.adj x y → K.adj x y)
    (tight : Nat.card (toSimple K).edgeSet+6=3*(v+1)) :
    ∃ f, ∃ C : ClosedTrace v f, witnessGraph C=A ∧ (f+1)+4=2*(v+1) ∧
      ∀ x y, (host C).adj x y ↔ K.adj x y := by
  classical
  let := Fintype.ofFinite (Cell M)
  have nm : Nonempty (Cell M) := by obtain ⟨a,b,h⟩ := M.incident 0; exact ⟨normal M h⟩
  have pos := Fintype.card_pos_iff.mpr nm
  let f := Fintype.card (Cell M)-1
  have eq : f+1=Fintype.card (Cell M) := by dsimp [f]; omega
  let q := (finCongr eq).trans (Fintype.equivFin (Cell M)).symm
  obtain ⟨C,same,edges⟩ := of_enum M A (fun x y h => (M_adj x y).mpr (inc x y h)) q
  have size := count_edges C (toSimple K) (fun x y => (edges x y).trans (M_adj x y))
  obtain ⟨glue,_,_⟩ := C.gluing
  have twice := glue.incidence_count
  change C.ledger.sealed.length=Nat.card (toSimple K).edgeSet at size
  have terminal : (f+1)+4=2*(v+1) := by omega
  exact ⟨f,C,same,terminal,fun x y => (edges x y).trans (M_adj x y)⟩

/-- A finite labelled triangular face map with Euler-tight edge count
already gives a planar graph. Orientability follows from the checked gluing. -/
theorem planar_of_tight_map {v} (K : Graph (v+1)) (M : Rigidity.Map (Fin (v+1)))
    (same : ∀ x y, M.adj x y ↔ K.adj x y) (tight : Nat.card (toSimple K).edgeSet+6=3*(v+1)) :
    K.Planar := by
  obtain ⟨_,C,_,terminal,edges⟩ := trace_of_tight_map K K M same (fun _ _ h => h) tight
  have eq : host C = K := Graph.eq_of_adj fun x y => Bool.eq_iff_iff.mpr (edges x y)
  exact eq ▸ TracePlanarity.host_planar C terminal

/-- Construct accepted fixed-width rows from any same-label, Euler-tight
planar supergraph of minimum degree three. The output graph retains exactly
the prescribed edges of `A`, including the original vertex labels. -/
theorem of_tight_supergraph {v} (A K : Graph (v+1)) (ds : List Nat)
    (order : 4≤v+1) (inc : ∀ x y, A.adj x y → K.adj x y) (sphere : K.Planar)
    (minDeg : ∀ x, 3 ≤ Nat.card {y // (toSimple K).Adj x y})
    (tight : Nat.card (toSimple K).edgeSet+6=3*(v+1))
    (degrees : ((List.finRange (v+1)).map A.degree).Perm ds) :
    ∃ f, ∃ r : TraceCheck.Records v f, TraceCheck.verify ds r ∧ TraceCheck.readGraph r=some A := by
  classical
  let H := toSimple K
  obtain ⟨plane⟩ := (planar_iff_rotation K).mp sphere
  obtain ⟨one,three⟩ := tight_faces plane (fun x => le_trans (by decide : 2≤3) (minDeg x))
    inferInstance (by simpa using tight)
  let tri := rotation K H (fun _ _ => Iff.rfl) plane minDeg one three
  have covered (x : Fin (v+1)) : ∃ y, K.adj x y=true := by
    have sz := minDeg x
    obtain ⟨y⟩ := (Nat.card_pos_iff.mp (by omega : 0<Nat.card {y // (toSimple K).Adj x y})).1
    exact ⟨y.val,y.property⟩
  let M := Rotation.asMap tri covered
  have M_adj (x y) : M.adj x y ↔ K.adj x y := Rotation.asMap_adj tri covered x y
  obtain ⟨f,C,same,terminal,_⟩ := trace_of_tight_map A K M M_adj inc tight
  have vals : witnessDegrees C=(List.finRange (v+1)).map A.degree := by
    apply List.ext_getElem
    · simp [witnessDegrees]
    · intro k h₁ h₂
      have hk : k<v+1 := by simpa [witnessDegrees] using h₁
      have count := witness_degree C ⟨k,hk⟩
      rw [same] at count
      simpa [witnessDegrees] using count.symm
  let r := TraceCheck.recordsOf C
  have yes := TraceCheck.verify_complete ds C order terminal (vals ▸ degrees)
  refine ⟨f,r,yes,?_⟩
  exact (TraceCheck.readGraph_recordsOf C).trans (congrArg some same)

end Recognition.ReverseTrace

namespace Recognition.ReverseTrace
open SparseBoundary Recognition.Wagner

/-- The sole geometric premise needed by the uncompressed verifier in the
reverse direction: triangulate using the existing names. -/
def Augmentation (n : Nat) : Prop := ∀ A : Graph n, A.Planar →
  ∃ K : Graph n, (∀ x y, A.adj x y → K.adj x y) ∧ K.Planar ∧
    (∀ x, 3 ≤ Nat.card {y // (toSimple K).Adj x y}) ∧
    Nat.card (toSimple K).edgeSet+6=3*n

theorem certificate_iff_planaric (d : Nat) (ds : List Nat) (order : 4 ≤ ds.length+1)
    (augment : Augmentation (ds.length+1)) :
    Planaric (d::ds) ↔ ∃ f, ∃ r : TraceCheck.Records ds.length f, TraceCheck.verify (d::ds) r := by
  constructor
  · rintro ⟨A,realizes,planar⟩
    obtain ⟨K,inc,sphere,minDeg,tight⟩ := augment A planar
    have values : (List.finRange (ds.length+1)).map A.degree=d::ds := by
      apply List.ext_getElem
      · simp
      · intro i h₁ h₂
        have bound : i<ds.length+1 := by simpa using h₂
        simpa using realizes ⟨i,bound⟩
    obtain ⟨f,r,yes,_⟩ := of_tight_supergraph A K (d::ds) order inc sphere minDeg tight (values ▸ List.Perm.refl _)
    exact ⟨f,r,yes⟩
  · rintro ⟨_,_,yes⟩; exact TracePlanarity.verify_planaric yes

end Recognition.ReverseTrace
