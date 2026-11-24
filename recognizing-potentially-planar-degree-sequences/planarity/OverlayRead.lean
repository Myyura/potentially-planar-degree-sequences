import OverlayCoverage
import OrbitTable
/-! Read the compact boundary from the anonymous dart view. A midpoint
record is identified by its two active neighbours; dual blocks are found by
unions of centres adjacent to a common midpoint. -/
namespace Recognition.OverlayRead
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep Recognition.Overlay Recognition.OverlayMinor
open Recognition.OverlayCoverage Recognition.MarkedPlane

structure Labels (fs : List Face) (s : Inventory) (n : Nat) (C : View) where
  tail : Fin n → Nodes fs s
  onto : Function.Surjective tail
  same : ∀ a b, C.vertexKey a=C.vertexKey b ↔ tail a=tail b
  marks : ∀ a, C.roles[a.val]?=some (role s (tail a).val).val ∧ C.counter a=value s (tail a).val
  links : ∀ a b, C.edgeBetween a b ↔ (shadow fs s).Adj (tail a) (tail b)

def tag (C : View) (d : Fin n) := C.roles[d.val]?.getD 4

private theorem marked (L : Labels fs s n C) (d : Fin n) : tag C d=(role s (L.tail d).val).val := by
  simp [tag,(L.marks d).1]

theorem point_mem {s : Inventory} {fs : List Face} {e}
    (m : Node.point e∈vertices fs s) : e∈retained s := by simpa [vertices] using m

theorem centre_mem {s : Inventory} {fs : List Face} {p : Patch fs (retained s)}
    (m : ∃ e,(e,p)∈spokes fs (retained s)) : Node.centre p∈vertices fs s := by simpa [vertices] using m

theorem pin_in {s : Inventory} {fs : List Face} {e} (m : e∈retained s) :
    Node.point e∈vertices fs s := by simp [vertices,m]

theorem primal {s : Inventory} {fs : List Face} (a b : Nodes fs s) {v e}
    (hv : a.val=Node.vertex v) (he : b.val=Node.point e) :
    (shadow fs s).Adj a b ↔ touches e v := by
  have ne : a≠b := fun eq => by have h := hv.symm.trans ((congrArg Subtype.val eq).trans he); contradiction
  have kept := point_mem (he ▸ b.property)
  change a≠b ∧ _ ↔ _
  simp [ne,hv,he,edges,segments,List.mem_flatMap,touches]
  grind

theorem spoke {s : Inventory} {fs : List Face} (a b : Nodes fs s) {p e}
    (hv : a.val=Node.centre p) (he : b.val=Node.point e) :
    (shadow fs s).Adj a b ↔ (e,p)∈spokes fs (retained s) := by
  have ne : a≠b := fun eq => by have h := hv.symm.trans ((congrArg Subtype.val eq).trans he); contradiction
  change a≠b ∧ _ ↔ _
  simp [ne,hv,he,edges,segments,List.mem_flatMap]

def middle (C : View) (x y m : Fin n) (t : Nat) :=
  tag C m == t && C.edgeBetween x m && C.edgeBetween y m

def edgeKind (C : View) (x y : Fin n) (t : Nat) :=
  (List.finRange n).any fun m => middle C x y m t

private theorem selected (L : Labels fs s n C) (x y m : Fin n) (e : Edge)
    (lo : (L.tail x).val=.vertex e.lo) (hi : (L.tail y).val=.vertex e.hi)
    {t : Nat} (kind : t=1 ∨ t=2) :
    middle C x y m t ↔ (L.tail m).val=Node.point e ∧ (role s (Node.point (P := Patch fs (retained s)) e)).val=t := by
  simp only [middle,Bool.and_eq_true,beq_iff_eq,L.links,marked L]
  cases hm : (L.tail m).val with
  | vertex v => rcases kind with rfl|rfl <;> simp [role]
  | centre p => rcases kind with rfl|rfl <;> simp [role]
  | point g =>
    rw [primal _ _ lo hm, primal _ _ hi hm]
    have inc := e.increasing
    have gin := g.increasing
    cases e; cases g; simp [touches,role,Node.point.injEq] at *
    grind

theorem edges_read (L : Labels fs s n C) (ok : replay (fs.flatMap Face.sides)=some s) (x y : Fin n) (e : Edge)
    (lo : (L.tail x).val=.vertex e.lo) (hi : (L.tail y).val=.vertex e.hi) :
    (edgeKind C x y 1 ↔ e∈s.pending) ∧ (edgeKind C x y 2 ↔ e∈retain (live s) s) := by
  have eq {t : Nat} (k : t=1 ∨ t=2) :
      edgeKind C x y t ↔ e∈retained s ∧ (role s (Node.point (P := Patch fs (retained s)) e)).val=t := by
    simp only [edgeKind,List.any_eq_true,List.mem_finRange,true_and]
    constructor
    · rintro ⟨m,h⟩
      obtain ⟨he,g⟩ := (selected L x y m e lo hi k).mp h
      exact ⟨point_mem (he ▸ (L.tail m).property),g⟩
    · rintro ⟨m,h⟩
      obtain ⟨a,eq⟩ := L.onto ⟨.point e,pin_in m⟩
      exact ⟨a,(selected L x y a e lo hi k).mpr ⟨congrArg Subtype.val eq,h⟩⟩
  rw [eq (t := 1) (Or.inl rfl),eq (t := 2) (Or.inr rfl)]
  by_cases p : e∈s.pending
  · have single := ((replay_accurate ok).pending e).mp p
    have closed : e∉s.sealed := fun m => by have := ((replay_accurate ok).sealed e).mp m; omega
    simp [role,retained,p,retain,closed]
  · simp [role,retained,p]

/-- All darts at a common hub are aliases. Centres joined to the same
midpoint belong to one read component, independent of midpoint status. -/
def hop (C : View) (a b : Fin n) := C.vertexKey a==C.vertexKey b ||
  (tag C a==3 && tag C b==3 && (List.finRange n).any fun m =>
    (tag C m==1 || tag C m==2) && C.edgeBetween a m && C.edgeBetween b m)

def unions (C : View) (n : Nat) :=
  ((List.finRange n).flatMap (fun a => (List.finRange n).map (a,·))).filter (fun p => hop C p.1 p.2)

def hubKey (C : View) (n : Nat) := OrbitTable.key (OrbitTable.run (List.finRange n) (unions C n))

private theorem hop_sym (C : View) (a b : Fin n) (h : hop C a b) : hop C b a := by
  simp [hop,List.any_eq_true] at *; grind

private theorem hub_connected (C : View) (a b : Fin n) :
    hubKey C n a=hubKey C n b ↔ Walk (fun x y : Fin n => hop C x y=true) a b := by
  let R := fun x y : Fin n => hop C x y=true
  let S : Setoid (Fin n) := ⟨Walk R,fun x => .refl,fun h => h.symm (hop_sym C),fun h g => h.trans g⟩
  have mem (x y : Fin n) : (x,y)∈unions C n ↔ hop C x y := by simp [unions,List.mem_flatMap]
  apply OrbitTable.generated _ List.mem_finRange _ S _ _ a b
  · rintro ⟨x,y⟩ m; exact Walk.step .refl ((mem ..).mp m)
  · intro r adds a b p
    change Walk R a b at p
    induction p with
    | refl => exact r.refl _
    | step _ step ih => exact r.trans ih (adds _ ((mem ..).mpr step))

private theorem to_centre (L : Labels fs s n C) (d : Fin n) (h : tag C d=3) :
    ∃ p, (L.tail d).val=Node.centre p := by
  rw [marked L] at h
  cases eq : (L.tail d).val with
  | centre p => exact ⟨p,rfl⟩
  | vertex v => simp [eq,role] at h
  | point e => by_cases p : e∈s.pending <;> simp [eq,role,p] at h

private theorem to_point (L : Labels fs s n C) (d : Fin n) (h : tag C d=1 ∨ tag C d=2) :
    ∃ e, (L.tail d).val=Node.point e := by
  rw [marked L] at h
  cases eq : (L.tail d).val with
  | point e => exact ⟨e,rfl⟩
  | vertex v => simp [eq,role] at h
  | centre p => simp [eq,role] at h

private theorem real_hop (L : Labels fs s n C) {x y : Fin n} {p} (start : (L.tail x).val=.centre p)
    (h : hop C x y) : ∃ q, (L.tail y).val=.centre q ∧ (p=q ∨ dualLink (spokes fs (retained s)) p q) := by
  simp only [hop,Bool.or_eq_true,beq_iff_eq,Bool.and_eq_true,List.any_eq_true,
    List.mem_finRange,true_and] at h
  rcases h with same|⟨⟨_,hubY⟩,m,⟨tag_,ax⟩,ay⟩
  · exact ⟨p,((congrArg Subtype.val ((L.same x y).mp same)).symm.trans start),Or.inl rfl⟩
  · obtain ⟨q,yq⟩ := to_centre L y hubY
    obtain ⟨e,me⟩ := to_point L m tag_
    exact ⟨q,yq,Or.inr ⟨e,(spoke _ _ start me).mp ((L.links ..).mp ax),
      (spoke _ _ yq me).mp ((L.links ..).mp ay)⟩⟩

private theorem connected_iff (L : Labels fs s n C) (x y : Fin n) {p q}
    (start : (L.tail x).val=.centre p) (last : (L.tail y).val=.centre q) :
    hubKey C n x=hubKey C n y ↔ Walk (dualLink (spokes fs (retained s))) p q := by
  rw [hub_connected]
  constructor
  · intro w
    have trace {z : Fin n} (h : Walk (fun a b => hop C a b=true) x z) :
        ∃ r, (L.tail z).val=.centre r ∧ Walk (dualLink (spokes fs (retained s))) p r := by
      induction h with
      | refl => exact ⟨p,start,.refl⟩
      | step _ h prev =>
        obtain ⟨r,g,walk⟩ := prev
        obtain ⟨r',eq,join⟩ := real_hop L g h
        refine ⟨r',eq,?_⟩
        rcases join with rfl|j
        · exact walk
        · exact walk.step j
    obtain ⟨r,eq,path⟩ := trace w
    exact Node.centre.inj (eq.symm.trans last) ▸ path
  · intro path
    induction path generalizing y with
    | refl => exact Walk.step .refl (by simp [hop,(L.same x y).mpr (Subtype.ext (start.trans last.symm))])
    | @step r q _ edge ih =>
      obtain ⟨e,sr,sq⟩ := edge
      obtain ⟨z,zEq⟩ := L.onto ⟨_,centre_mem ⟨_,sr⟩⟩
      have zval : (L.tail z).val=.centre r := congrArg Subtype.val zEq
      have em : e∈retained s := by
        simp [spokes,contacts,List.mem_flatMap] at sr; grind
      obtain ⟨m,mEq⟩ := L.onto ⟨.point e,pin_in em⟩
      have mval : (L.tail m).val=.point e := congrArg Subtype.val mEq
      apply (ih z zval).step
      simp only [hop,Bool.or_eq_true]
      right
      have ez := (L.links z m).mpr ((spoke _ _ zval mval).mpr sr)
      have ey := (L.links y m).mpr ((spoke _ _ last mval).mpr sq)
      have mk : tag C m=1 ∨ tag C m=2 := by rw [marked L,mval]; by_cases open_ : e∈s.pending <;> simp [role,open_]
      simp only [Bool.and_eq_true,beq_iff_eq,List.any_eq_true,List.mem_finRange,true_and,Bool.or_eq_true]
      exact ⟨⟨by simp [marked L,zval,role],by simp [marked L,last,role]⟩,m,⟨mk,ez⟩,ey⟩

def connectedPins (C : View) (m l : Fin n) :=
  (List.finRange n).any fun a => (List.finRange n).any fun b =>
    tag C a==3 && tag C b==3 && C.edgeBetween a m && C.edgeBetween b l && hubKey C n a==hubKey C n b

private theorem pins_read (L : Labels fs s n C) (m l : Fin n) {e f : Edge}
    (atE : (L.tail m).val=.point e) (atF : (L.tail l).val=.point f)
    (openE : e∈s.pending) (openF : f∈s.pending) :
    connectedPins C m l ↔ sameBlock fs e f := by
  rw [← blocks_correct fs s openE openF]
  simp only [connectedPins,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨a,b,⟨⟨⟨⟨ha,hb⟩,am⟩,bl⟩,path⟩⟩
    obtain ⟨p,pv⟩ := to_centre L a ha
    obtain ⟨q,qv⟩ := to_centre L b hb
    exact ⟨p,q,(spoke _ _ pv atE).mp ((L.links ..).mp am),
      (spoke _ _ qv atF).mp ((L.links ..).mp bl),(connected_iff L a b pv qv).mp path⟩
  · rintro ⟨p,q,hp,hq,path⟩
    obtain ⟨a,av⟩ := L.onto ⟨_,centre_mem ⟨_,hp⟩⟩
    obtain ⟨b,bv⟩ := L.onto ⟨_,centre_mem ⟨_,hq⟩⟩
    have pa : (L.tail a).val=.centre p := congrArg Subtype.val av
    have pb : (L.tail b).val=.centre q := congrArg Subtype.val bv
    exact ⟨a,b,⟨⟨⟨⟨by simp [marked L,pa,role],by simp [marked L,pb,role]⟩,
      (L.links ..).mpr ((spoke _ _ pa atE).mpr hp)⟩,(L.links ..).mpr ((spoke _ _ pb atF).mpr hq)⟩,
      (connected_iff L a b pa pb).mpr path⟩⟩

/-- Query the component relation on two pairs of anonymous active vertices.
Each argument is an arbitrary representative dart of the given vertex. -/
def block (C : View) (x y u v : Fin n) :=
  (List.finRange n).any fun m => (List.finRange n).any fun l =>
    middle C x y m 1 && middle C u v l 1 && connectedPins C m l

theorem blocks_read (L : Labels fs s n C) (x y u v : Fin n) (e f : Edge)
    (xv : (L.tail x).val=.vertex e.lo) (yv : (L.tail y).val=.vertex e.hi)
    (uv : (L.tail u).val=.vertex f.lo) (vv : (L.tail v).val=.vertex f.hi) :
    block C x y u v ↔ e∈s.pending ∧ f∈s.pending ∧ sameBlock fs e f := by
  simp only [block,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true]
  have get {a : Edge} {i j m : Fin n} (lo : (L.tail i).val=.vertex a.lo)
      (hi : (L.tail j).val=.vertex a.hi) (h : middle C i j m 1) :
      (L.tail m).val=.point a ∧ a∈s.pending := by
    have ⟨p,t⟩ := (selected L i j m a lo hi (Or.inl rfl)).mp h
    exact ⟨p,by by_contra no; simp [role,no] at t⟩
  have put (a : Edge) (h : a∈s.pending) : ∃ i, (L.tail i).val=.point a := by
    have kept : a∈retained s := by simp [retained,h]
    obtain ⟨m,eq⟩ := L.onto ⟨.point a,pin_in kept⟩
    exact ⟨m,congrArg Subtype.val eq⟩
  constructor
  · rintro ⟨m,l,⟨hm,hl⟩,path⟩
    obtain ⟨mv,a⟩ := get xv yv hm
    obtain ⟨lv,b⟩ := get uv vv hl
    exact ⟨a,b,(pins_read L m l mv lv a b).mp path⟩
  · rintro ⟨a,b,yes⟩
    obtain ⟨m,mv⟩ := put e a
    obtain ⟨l,lv⟩ := put f b
    exact ⟨m,l,⟨(selected L x y m e xv yv (Or.inl rfl)).mpr ⟨mv,by simp [role,a]⟩,
      (selected L u v l f uv vv (Or.inl rfl)).mpr ⟨lv,by simp [role,b]⟩⟩,
      (pins_read L m l mv lv a b).mpr yes⟩

/-- Every nonempty record produced for a true prefix carries the exact
active counters, edge statuses and open-component relation. -/
theorem interprets {fs s bits} (covered : Covered fs s bits) :
    (bits=[] ∧ vertices fs s=[]) ∨
    ∃ (n : Nat) (C : View) (L : Labels fs s n C), MarkedPlane.decode bits=some C ∧ C.ribbon.length=n ∧
      (∀ x : Fin n, C.counter x=value s (L.tail x).val) ∧
      (∀ x y e, (L.tail x).val=.vertex e.lo → (L.tail y).val=.vertex e.hi →
        (edgeKind C x y 1 ↔ e∈s.pending) ∧
        (edgeKind C x y 2 ↔ e∈retained s ∧ e∉s.pending)) ∧
      ∀ x y u v e f, (L.tail x).val=.vertex e.lo → (L.tail y).val=.vertex e.hi →
        (L.tail u).val=.vertex f.lo → (L.tail v).val=.vertex f.hi →
        (block C x y u v ↔ e∈s.pending ∧ f∈s.pending ∧ sameBlock fs e f) := by
  rcases covered with nil|⟨n,C,tail,onto,code,size,key,role_,link⟩
  · exact .inl nil
  · let L : Labels fs s n C := ⟨tail,onto,key,role_,link⟩
    refine .inr ⟨n,C,L,code,size,fun x => (L.marks x).2,?_,fun x y u v e f => blocks_read L x y u v e f⟩
    intro x y e lo hi
    have kind {t : Nat} (k : t=1 ∨ t=2) : edgeKind C x y t ↔
        e∈retained s ∧ (role s (Node.point (P := Patch fs (retained s)) e)).val=t := by
      simp only [edgeKind,List.any_eq_true,List.mem_finRange,true_and]
      constructor
      · rintro ⟨m,hm⟩
        obtain ⟨p,r⟩ := (selected L x y m e lo hi k).mp hm
        exact ⟨point_mem (p ▸ (L.tail m).property),r⟩
      · rintro ⟨keep,mark⟩
        obtain ⟨m,mv⟩ := L.onto ⟨.point e,pin_in keep⟩
        exact ⟨m,(selected L x y m e lo hi k).mpr ⟨congrArg Subtype.val mv,mark⟩⟩
    rw [kind (Or.inl rfl),kind (Or.inr rfl)]
    by_cases open_ : e∈s.pending <;> simp [role,retained,open_]

#print axioms blocks_read
#print axioms interprets
end Recognition.OverlayRead
