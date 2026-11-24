import Triangulation.Provenance
import Triangulation.Layers
import Triangulation.Tricolor
import Triangulation.FaceCapacity
import Triangulation.StackedMinor
import SparseBoundary.TruncationData

namespace Recognition.BipartiteMinor
open Rigidity Stacking
abbrev L (i : Fin 3) : Fin 7 := i.castLE (by decide)
abbrev R (i : Fin 3) : Fin 7 := ⟨3+i.val,by omega⟩

/-- An unfinished K₃,₃ model. Each right branch is either present, or is
represented by a distinct facial triangle meeting the three left branches. -/
structure Fork {V : Type} (M : Map V) where
  color : V → Fin 7
  virtual : Fin 3 → Bool
  pin : ∀ r, virtual r = true → Fin 3 → V
  rainbow : ∀ r h i, color (pin r h i) = L i
  facial : ∀ r h, M.face (pin r h 0) (pin r h 1) (pin r h 2)
  unique : ∀ r hr s hs, pin r hr = pin s hs → r = s
  conn : ∀ k : Fin 7, k.val < 6 → ∀ p : V → Prop,
    (∀ x y, color x = k → color y = k → M.adj x y → (p x ↔ p y)) →
    ∀ x y, color x = k → color y = k → (p x ↔ p y)
  links : ∀ i r, virtual r = false → ∃ x y, color x = L i ∧ color y = R r ∧ M.adj x y

private theorem symm {V : Type} (M : Map V) {x y : V} (h : M.adj x y) : M.adj y x :=
  let ⟨c,f⟩ := h
  ⟨c,M.flip f⟩

private theorem noStars {V : Type} (M : Map V) (fill : Choice V) (s t : Star M fill) :
    ¬(stack M fill).adj (.inr s) (.inr t) := by
  rintro ⟨u,f⟩; cases u <;> exact False.elim f

private theorem joint {V : Type} (M : Map V) {fill : Choice V} (s : Star M fill) {u v : V}
    (hu : s.val u) (hv : s.val v) : u=v ∨ M.adj u v := by
  obtain ⟨a,b,c,f,h⟩ := s.property.1
  rw [h] at hu hv
  have N {i j k} (p : M.face i j k) : M.adj i j := ⟨k,p⟩
  have ab := N f; have bc := N (M.rot f); have ca := N (M.rot (M.rot f))
  have ba := symm M ab; have cb := symm M bc; have ac := symm M ca
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> grind

variable {V : Type} (M : Map V) (fill : Choice V) (B : Fork (stack M fill))

private def Live (k : Fin 7) := ∃ v, B.color (.inl v) = k

private theorem isolated (k : Fin 7) (hk : k.val < 6) (s : Star M fill) (tag : B.color (.inr s) = k)
    (noAnchor : ¬ ∃ v, s.val v ∧ B.color (.inl v) = k) {w} (hw : B.color w = k) : w = .inr s := by
  have loc (z) (hz : B.color z = k) : ¬ (stack M fill).adj (.inr s) z := by
    cases z with
    | inl a => exact fun h => noAnchor ⟨a,(star_neighbors M fill s a).mp h,hz⟩
    | inr t => exact noStars M fill s t
  apply (B.conn k hk (fun u => u = .inr s) _ _ _ tag hw).mp rfl
  intro x y hx hy e
  constructor
  · rintro rfl; exact False.elim (loc y hy e)
  · rintro rfl; exact False.elim (loc x hx (symm _ e))

private theorem anchor {k : Fin 7} (hk : k.val < 6) (alive : Live M fill B k)
    (s : Star M fill) (tag : B.color (.inr s) = k) : ∃ v, s.val v ∧ B.color (.inl v) = k := by
  apply Classical.byContradiction
  intro h
  obtain ⟨v,hv⟩ := alive
  have eq := isolated M fill B k hk s tag h hv
  contradiction

private theorem singleton {k : Fin 7} (hk : k.val < 6) (bad : ¬ Live M fill B k)
    {x : Vertex M fill} (tag : B.color x = k) :
    ∃ s : Star M fill, x = .inr s ∧ ∀ w, B.color w = k → w = .inr s := by
  cases x with
  | inl a => exact False.elim (bad ⟨a,tag⟩)
  | inr s =>
    exact ⟨s,rfl,fun _ h => isolated M fill B k hk s tag (fun ⟨a,_,ha⟩ => bad ⟨a,ha⟩) h⟩

private noncomputable def projectVertex {k : Fin 7} (hk : k.val < 6) (live : Live M fill B k)
    (x : Vertex M fill) (tag : B.color x=k) : V :=
  match x with
  | .inl a => a
  | .inr s => (anchor M fill B hk live s tag).choose

private theorem project_tag {k : Fin 7} (hk : k.val < 6) (live : Live M fill B k) (x tag) :
    B.color (.inl (projectVertex M fill B hk live x tag)) = k := by
  cases x with
  | inl a => exact tag
  | inr s => exact (anchor M fill B hk live s tag).choose_spec.2

private theorem project_edge {j k : Fin 7} (hj : j.val < 6) (hk : k.val < 6)
    (lj : Live M fill B j) (lk : Live M fill B k) (x y) (tx : B.color x=j) (ty : B.color y=k)
    (e : (stack M fill).adj x y) :
    projectVertex M fill B hj lj x tx = projectVertex M fill B hk lk y ty ∨
    M.adj (projectVertex M fill B hj lj x tx) (projectVertex M fill B hk lk y ty) := by
  cases x with
  | inl a =>
    cases y with
    | inl b => exact Or.inr ((old_edges M fill a b).mp e)
    | inr s => exact joint M s ((star_neighbors M fill s a).mp (symm _ e)) (anchor M fill B hk lk s ty).choose_spec.1
  | inr s =>
    cases y with
    | inl a => exact joint M s (anchor M fill B hj lj s tx).choose_spec.1 ((star_neighbors M fill s a).mp e)
    | inr t => exact False.elim (noStars M fill s t e)

private theorem old_conn (k : Fin 7) (hk : k.val < 6) (p : V → Prop)
    (along : ∀ x y, B.color (.inl x)=k → B.color (.inl y)=k → M.adj x y → (p x ↔ p y))
    (a b : V) (ta : B.color (.inl a)=k) (tb : B.color (.inl b)=k) : p a ↔ p b := by
  have live : Live M fill B k := ⟨a,ta⟩
  let inside (z : Vertex M fill) := ∃ t : B.color z=k, p (projectVertex M fill B hk live z t)
  have step (x y) (hx : B.color x=k) (hy : B.color y=k) (e : (stack M fill).adj x y) :
      inside x ↔ inside y := by
    have only (z) (hz : B.color z=k) : inside z ↔ p (projectVertex M fill B hk live z hz) :=
      ⟨fun ⟨_,g⟩ => g,fun g => ⟨hz,g⟩⟩
    rw [only _ hx,only _ hy]
    rcases project_edge M fill B hk hk live live x y hx hy e with eq | link
    · rw [eq]
    · exact along _ _ (project_tag M fill B hk live x hx) (project_tag M fill B hk live y hy) link
  have all := B.conn k hk inside step (.inl a) (.inl b) ta tb
  exact ⟨fun h => (all.mp ⟨ta,h⟩).elim (fun _ g => g),fun h => (all.mpr ⟨tb,h⟩).elim (fun _ g => g)⟩

private theorem smallL (i : Fin 3) : (L i).val < 6 := by have := i.isLt; exact Nat.lt_trans this (by decide)
private theorem smallR (i : Fin 3) : (R i).val < 6 := by have := i.isLt; change 3+i.val<6; omega

private def swap (k : Fin 7) : Fin 7 :=
  if h : k.val < 3 then ⟨k.val+3,by omega⟩
  else if k.val < 6 then ⟨k.val-3,by omega⟩ else k

private theorem invol : ∀ k, swap (swap k) = k := by decide +kernel
private theorem swap_small : ∀ k : Fin 7, k.val < 6 → (swap k).val < 6 := by decide +kernel
private theorem swap_lr : ∀ i : Fin 3, swap (L i) = R i ∧ swap (R i) = L i := by decide +kernel
private theorem swap_iff (x y : Fin 7) : swap x = y ↔ x = swap y :=
  ⟨fun h => (invol x).symm.trans (congrArg swap h),fun h => h ▸ invol y⟩

private def transpose {W : Type} (N : Map W) (C : Fork N) (real : ∀r, C.virtual r=false) : Fork N where
  color x := swap (C.color x)
  virtual _ := false
  pin _ h := by contradiction
  rainbow _ h := by contradiction
  facial _ h := by contradiction
  unique _ h := by contradiction
  conn k hk p h x y hx hy := C.conn (swap k) (swap_small k hk) p
    (fun u v hu hv => h _ _ ((swap_iff _ k).mpr hu) ((swap_iff _ k).mpr hv)) x y
    ((swap_iff _ k).mp hx) ((swap_iff _ k).mp hy)
  links i r _ := by
    obtain ⟨x,y,hx,hy,e⟩ := C.links r i (real i)
    exact ⟨y,x,hy ▸ (swap_lr i).2,hx ▸ (swap_lr r).1,symm N e⟩


private def next (i : Fin 3) : Fin 3 := ⟨(i.val+1)%3,by omega⟩
private def last (i : Fin 3) : Fin 3 := ⟨(i.val+2)%3,by omega⟩
private theorem split3 : ∀ i j : Fin 3, j=i ∨ j=next i ∨ j=last i := by decide +kernel
private theorem distinct3 : ∀ i : Fin 3, i≠next i ∧ i≠last i ∧ next i≠last i := by decide +kernel
private theorem left_ne_right : ∀ i j, L i ≠ R j := by decide +kernel

private def translateColor (i : Fin 3) (k : Fin 7) : Fin 7 :=
  if k = L (next i) then 1 else if k = L (last i) then 2 else if 3 ≤ k.val then k else 0
private theorem translate_next : ∀ i, translateColor i (L (next i)) = 1 := by decide +kernel
private theorem translate_last : ∀ i, translateColor i (L (last i)) = 2 := by decide +kernel
private theorem translate_right : ∀ i r, translateColor i (R r) = R r := by decide +kernel

private theorem face_link {W : Type} (N : Map W) (p : Fin 3 → W)
    (f : N.face (p 0) (p 1) (p 2)) (i j : Fin 3) (ne : i≠j) : N.adj (p i) (p j) := by
  have f01 : N.adj (p 0) (p 1) := ⟨_,f⟩
  have f12 : N.adj (p 1) (p 2) := ⟨_,N.rot f⟩
  have f20 : N.adj (p 2) (p 0) := ⟨_,N.rot (N.rot f)⟩
  have := symm N f01; have := symm N f12; have := symm N f20
  have all : ∀ z : Fin 3, z=0 ∨ z=1 ∨ z=2 := by decide +kernel
  have := all i; have := all j
  grind

private def triple {W : Type} (a b c : W) (j : Fin 3) := if j=0 then a else if j=1 then b else c

private theorem slots (s : Star M fill) :
    ∃ t : Fin 3 → V, M.face (t 0) (t 1) (t 2) ∧ s.val = corners (t 0) (t 1) (t 2) ∧
      ∀ w : Vertex M fill, (stack M fill).adj (.inr s) w → ∃ j, w = .inl (t j) := by
  obtain ⟨a,b,c,f,h⟩ := s.property.1
  refine ⟨triple a b c,?_,?_,?_⟩
  · simpa [triple] using f
  · simpa [triple] using h
  intro w link
  cases w with
  | inr y => exact False.elim (noStars M fill s y link)
  | inl v =>
    have member := (star_neighbors M fill s v).mp link
    rw [h] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

/-- A disappearing real right branch exposes a face whose old corners have
the three distinct left colors. -/
private theorem replacement (r : Fin 3) (real : B.virtual r=false) (bad : ¬ Live M fill B (R r)) :
    ∃ (s : Star M fill) (p : Fin 3 → V), B.color (.inr s) = R r ∧
      (∀ i, B.color (.inl (p i))=L i) ∧
      M.face (p 0) (p 1) (p 2) ∧ s.val = corners (p 0) (p 1) (p 2) := by
  classical
  obtain ⟨_,w,_,tag,_⟩ := B.links 0 r real
  obtain ⟨s,rfl,single⟩ := singleton M fill B (smallR r) bad tag
  obtain ⟨t,ft,key,neighbor⟩ := slots M fill s
  have pick (i : Fin 3) : ∃ k, B.color (.inl (t k)) = L i := by
    obtain ⟨x,y,hx,hy,e⟩ := B.links i r real
    rw [single _ hy] at e
    obtain ⟨k,rfl⟩ := neighbor _ (symm _ e)
    exact ⟨k,hx⟩
  let k i := (pick i).choose
  let p i := t (k i)
  have col (i : Fin 3) : B.color (.inl (p i)) = L i := (pick i).choose_spec
  have inj (i j : Fin 3) (e : k i=k j) : i=j := by
    have same : p i = p j := congrArg t e
    exact Fin.ext (congrArg (Fin.val (n := 7)) ((col i).symm.trans ((congrArg (fun v => B.color (.inl v)) same).trans (col j))))
  have perm : ∀ u v w : Fin 3, u≠v → v≠w → u≠w →
      (u=0 ∧ v=1 ∧ w=2) ∨ (u=1 ∧ v=2 ∧ w=0) ∨ (u=2 ∧ v=0 ∧ w=1) ∨
      (u=1 ∧ v=0 ∧ w=2) ∨ (u=2 ∧ v=1 ∧ w=0) ∨ (u=0 ∧ v=2 ∧ w=1) := by decide +kernel
  have ps := perm (k 0) (k 1) (k 2) (fun h => (by decide : (0:Fin 3)≠1) (inj _ _ h))
    (fun h => (by decide : (1:Fin 3)≠2) (inj _ _ h)) (fun h => (by decide : (0:Fin 3)≠2) (inj _ _ h))
  refine ⟨s,p,tag,col,?_,?_⟩
  · have := M.rot ft; have := M.rot (M.rot ft); have := M.flip ft
    have := M.flip (M.rot ft); have := M.flip (M.rot (M.rot ft))
    simp only [p]; grind
  · rw [key]
    funext x
    apply propext
    simp only [corners,p]
    rcases ps with h|h|h|h|h|h <;> rcases h with ⟨e₁,e₂,e₃⟩ <;> rw [e₁,e₂,e₃] <;> grind only


private inductive Origin (r : Fin 3) (p : Fin 3 → V) : Prop where
  | inherited (h : B.virtual r=true) (parent : Tricolor.Parent M fill B.color (B.pin r h) p)
  | exposed (s : Star M fill) (col : B.color (.inr s)=R r)
      (face : M.face (p 0) (p 1) (p 2)) (rainbow : ∀ i, B.color (.inl (p i))=L i)
      (key : s.val = corners (p 0) (p 1) (p 2))

private theorem different {p : Fin 3 → V} {r s : Fin 3} (h : B.virtual r = true)
    (parent : Tricolor.Parent M fill B.color (B.pin r h) p) (x : Star M fill)
    (col : B.color (.inr x) = R s) (key : x.val = corners (p 0) (p 1) (p 2)) : False := by
  rcases parent.form with ⟨no,_⟩ | ⟨y,ky,j,tag,_⟩
  · exact no (key ▸ x.property.2)
  · have eq : y = x := Subtype.ext (ky.trans key.symm)
    have wrong : L j = R s := tag.symm.trans (eq ▸ col)
    exact left_ne_right j s wrong

private theorem unique_parent {r s : Fin 3} {p : Fin 3 → V} (a : Origin M fill B r p)
    (b : Origin M fill B s p) : r = s := by
  cases a with
  | inherited hr pp =>
    cases b with
    | inherited hs qq => exact B.unique r hr s hs (Tricolor.parent_injective M fill pp qq)
    | exposed x col _ _ key => exact False.elim (different M fill B hr pp x col key)
  | exposed x col _ _ key =>
    cases b with
    | inherited hs qq => exact False.elim (different M fill B hs qq x col key)
    | exposed y tag _ _ ky =>
      have eq : x = y := Subtype.ext (key.trans ky.symm)
      have same : R r = R s := col.symm.trans (eq ▸ tag)
      exact Fin.ext (Nat.add_left_cancel (congrArg (Fin.val (n:=7)) same))

private noncomputable def projectFork (left : ∀ i, Live M fill B (L i)) : Fork M := by
  classical
  let vac := fun r => B.virtual r || decide (¬Live M fill B (R r))
  have source (r : Fin 3) (h : vac r=true) : ∃ p, Origin M fill B r p := by
    cases old : B.virtual r with
    | true =>
      obtain ⟨p,parent⟩ := Tricolor.parent_exists M fill B.color (B.pin r old)
        (B.facial r old) (B.rainbow r old) (fun s j hs => by
            obtain ⟨v,hv,tag⟩ := anchor M fill B (smallL j) (left j) s hs
            exact ⟨v,hv,tag.trans hs.symm⟩)
      exact ⟨p,.inherited old parent⟩
    | false =>
      have bad : ¬ Live M fill B (R r) := by simpa [vac,old] using h
      obtain ⟨s,p,col,colors,f,key⟩ := replacement M fill B r old bad
      exact ⟨p,.exposed s col f colors key⟩
  let pin r h := (source r h).choose
  have src r h : Origin M fill B r (pin r h) := (source r h).choose_spec
  refine {
    color := fun x => B.color (.inl x)
    virtual := vac
    pin := pin
    rainbow := ?_
    facial := ?_
    unique := ?_
    conn := old_conn M fill B
    links := ?_
  }
  · intro r h i
    cases src r h with
    | inherited _ P => exact P.colors i
    | exposed _ _ _ color _ => exact color i
  · intro r h
    cases src r h with
    | inherited _ P => exact P.face
    | exposed _ _ f _ _ => exact f
  · intro r hr s hs eq
    exact unique_parent M fill B (src r hr) (eq ▸ src s hs)
  · intro i r real
    have live : Live M fill B (R r) := by
      apply Classical.byContradiction
      intro no
      simp [vac,no] at real
    have old : B.virtual r=false := (Bool.or_eq_false_iff.mp real).1
    obtain ⟨x,y,cx,cy,e⟩ := B.links i r old
    have ax := project_tag M fill B (smallL i) (left i) x cx
    have ay := project_tag M fill B (smallR r) live y cy
    refine ⟨_,_,ax,ay,?_⟩
    rcases project_edge M fill B (smallL i) (smallR r) (left i) live x y cx cy e with eq | g
    · exact False.elim (left_ne_right i r (ax.symm.trans (eq ▸ ay)))
    · exact g


private def Capacity3 := ∀ (o : Fin 3 → Fin 7) (v : Fin 3 → Bool),
  (∀ r, v r=false → ∃ j, (o j).val=3+r.val) → (∃ r, v r=true) →
  ∀ p q : Fin 3 → Fin 3,
    (∀ r, v r=true → (o (p r)).val=1 ∧ (o (q r)).val=2) →
    (∀ r s, v r=true → v s=true → p r=p s → q r=q s → r=s) → False

private theorem left_alive (count : Capacity3) (has : ∃ r, B.virtual r=true) (i : Fin 3) :
    Live M fill B (L i) := by
  classical
  apply Classical.byContradiction
  intro bad
  obtain ⟨r₀,hr⟩ := has
  obtain ⟨s,_,single⟩ := singleton M fill B (smallL i) bad (B.rainbow r₀ hr i)
  obtain ⟨t,_,_,nb⟩ := slots M fill s
  let o (j : Fin 3) := translateColor i (B.color (.inl (t j)))
  have real (r) (h : B.virtual r=false) : ∃j, (o j).val=3+r.val := by
    obtain ⟨x,y,hx,hy,edge⟩ := B.links i r h
    rw [single _ hx] at edge
    obtain ⟨j,hj⟩ := nb _ edge
    subst y
    exact ⟨j,by simp [o,hy,translate_right,R]⟩
  have loc (r) (h : B.virtual r=true) (j : Fin 3) (ne : i≠j) :
      ∃ k, B.pin r h j = .inl (t k) := by
    have edge := face_link (stack M fill) _ (B.facial r h) i j ne
    rw [single _ (B.rainbow r h i)] at edge
    exact nb _ edge
  let a (r : Fin 3) := if h : B.virtual r=true then (loc r h (next i) (distinct3 i).1).choose else 0
  let b (r : Fin 3) := if h : B.virtual r=true then (loc r h (last i) (distinct3 i).2.1).choose else 0
  have n (r h) : B.pin r h (next i) = .inl (t (a r)) := by
    simpa [a,h] using (loc r h (next i) (distinct3 i).1).choose_spec
  have l (r h) : B.pin r h (last i) = .inl (t (b r)) := by
    simpa [b,h] using (loc r h (last i) (distinct3 i).2.1).choose_spec
  refine count o B.virtual real ⟨r₀,hr⟩ a b ?_ ?_
  · intro r h
    have tagA := B.rainbow r h (next i)
    have tagB := B.rainbow r h (last i)
    rw [n _ h] at tagA
    rw [l _ h] at tagB
    simp [o,tagA,tagB,translate_next,translate_last]
  · intro r u hr hu ha hb
    apply B.unique r hr u hu
    funext j
    rcases split3 i j with rfl | rfl | rfl
    · exact (single _ (B.rainbow r hr _)).trans (single _ (B.rainbow u hu _)).symm
    · rw [n r hr,n u hu,ha]
    · rw [l r hr,l u hu,hb]

include fill B in
private theorem descend (count : Capacity3) : Nonempty (Fork M) := by
  classical
  by_cases h : ∀ i, Live M fill B (L i)
  · exact ⟨projectFork M fill B h⟩
  have all : ∀ r, B.virtual r=false := by
    intro r
    cases hr : B.virtual r with
    | false => rfl
    | true => exact False.elim (h (left_alive M fill B count ⟨r,hr⟩))
  let C := transpose _ B all
  have right (r : Fin 3) : Live M fill C (L r) := by
    apply Classical.byContradiction
    intro no
    have rbad : ¬ Live M fill B (R r) := by
      rintro ⟨u,hu⟩
      exact no ⟨u,by change swap (B.color (.inl u)) = L r; rw [hu,(swap_lr r).2]⟩
    apply h
    intro i
    obtain ⟨x,y,hx,hy,e⟩ := B.links i r (all r)
    obtain ⟨s,rfl,_⟩ := singleton M fill B (smallR r) rbad hy
    cases x with
    | inl u => exact ⟨u,hx⟩
    | inr t => exact False.elim (noStars M fill t s e)
  exact ⟨projectFork M fill C right⟩

private def Capacity4 := ∀ (o : Fin 4 → Fin 7) (v : Fin 3 → Bool),
  (∀ i : Fin 3, ∃ j, (o j).val=i.val) →
  (∀ r, v r=false → ∃ j, (o j).val=3+r.val) →
  ∀ p q t : Fin 3 → Fin 4,
    (∀ r, v r=true → (o (p r)).val=0 ∧ (o (q r)).val=1 ∧ (o (t r)).val=2) →
    (∀ r s, v r=true → v s=true → p r=p s → q r=q s → t r=t s → r=s) → False

private theorem tetra_excludes (count : Capacity4) (C : Fork Tetrahedron.map) : False := by
  classical
  let get (i r : Fin 3) := if h : C.virtual r=true then C.pin r h i else (0 : Fin 4)
  have allLeft (i : Fin 3) : ∃ j, (C.color j).val = i.val := by
    cases h : C.virtual 0 with
    | false =>
      obtain ⟨x,_,hx,_,_⟩ := C.links i 0 h
      exact ⟨x,congrArg Fin.val hx⟩
    | true => exact ⟨_,congrArg Fin.val (C.rainbow 0 h i)⟩
  have allReal (r) (h : C.virtual r=false) : ∃j, (C.color j).val=3+r.val := by
    obtain ⟨_,y,_,hy,_⟩ := C.links 0 r h
    exact ⟨y,congrArg Fin.val hy⟩
  refine count C.color C.virtual allLeft allReal (get 0) (get 1) (get 2) ?_ ?_
  · intro r h
    simp [get,h,C.rainbow]
  · intro r s hr hs a b c
    apply C.unique r hr s hs
    funext j
    have which : ∀ i : Fin 3, i=0 ∨ i=1 ∨ i=2 := by decide +kernel
    simp only [get,hr,hs,↓reduceDIte] at a b c
    rcases which j with rfl|rfl|rfl <;> assumption

private theorem noModel (three : Capacity3) (four : Capacity4) {W : Type} {N : Map W} (hist : StackedMap N) :
    ¬Nonempty (Fork N) := by
  induction hist with
  | tetra => exact fun ⟨B⟩ => tetra_excludes four B
  | subdivide h fill ih => exact fun ⟨B⟩ => ih (descend _ fill B three)


open SparseBoundary SparseBoundary.Graph SparseBoundary.Truncation

private theorem graph_fork {d : List Nat} (A : Layers.Model d) (G : Graph d.length)
    (same : ∀ i j : Fin d.length, A.edge i.val j.val ↔ G.adj i j = true)
    (bags : Fin 6 → List (Fin d.length)) (res : G.minorTest biclique33 bags=true) : Nonempty (Fork A.map) := by
  classical
  have B := model_iff.mp res
  let id (v : A.V) : Fin d.length := ⟨A.label v,Layers.bound A v⟩
  let inv (j : Fin d.length) := ((A.hits j.val).mp j.isLt).choose
  have key (j : Fin d.length) : A.label (inv j) = j.val := ((A.hits j.val).mp j.isLt).choose_spec
  have ret (v : A.V) : inv (id v) = v := A.inj _ _ (key (id v))
  have get (j : Fin d.length) : id (inv j) = j := Fin.ext (key j)
  have lift (i j : Fin d.length) (h : G.adj i j = true) : A.map.adj (inv i) (inv j) := by
    obtain ⟨x,y,hx,hy,g⟩ := (same i j).mpr h
    exact A.inj x (inv i) (hx.trans (key i).symm) ▸ A.inj y (inv j) (hy.trans (key j).symm) ▸ g
  let col (x : A.V) := bagLabel bags (id x)
  have membership (k : Fin 7) (hk : k.val<6) (x : A.V) : col x=k ↔ id x ∈ bags ⟨k.val,hk⟩ :=
    Fin.ext_iff.trans (label_iff B (id x) ⟨k.val,hk⟩)
  refine ⟨{
    color := col
    virtual := fun _ => false
    pin := fun _ h => by contradiction
    facial := fun _ h => by contradiction
    rainbow := fun _ h => by contradiction
    unique := fun _ h => by contradiction
    conn := ?_
    links := ?_
  }⟩
  · intro k hk p edge a b ha hb
    let j : Fin 6 := ⟨k.val,hk⟩
    have tag (x : Fin d.length) (h : x ∈ bags j) : col (inv x) = k :=
      (membership k hk _).mpr ((get x).symm ▸ h)
    have H := uniform_bag (B.con j) (fun v => p (inv v)) (fun x hx y hy e =>
      edge (inv x) (inv y) (tag x hx) (tag y hy) (lift x y e)) (id a) ((membership k hk _).mp ha)
      (id b) ((membership k hk _).mp hb)
    simpa only [ret] using H
  · intro i r _
    let u : Fin 6 := ⟨i.val,smallL i⟩
    let v : Fin 6 := ⟨3+r.val,smallR r⟩
    have ne : biclique33 u v = true := by simp [biclique33,u,v,i.isLt]
    obtain ⟨x,hx,y,hy,e⟩ := B.link u v ne
    exact ⟨inv x,inv y,(membership (L i) (smallL i) _).mpr ((get x).symm ▸ hx),
      (membership (R r) (smallR r) _).mpr ((get y).symm ▸ hy),lift x y e⟩


theorem no_biclique33_minor {d : List Nat} (A : Layers.Model d) (built : StackedMap A.map) (G : Graph d.length)
    (same : ∀ i j : Fin d.length, A.edge i.val j.val ↔ G.adj i j = true)
    (bags : Fin 6 → List (Fin d.length)) : G.minorTest biclique33 bags=false := by
  cases res : G.minorTest biclique33 bags with
  | false => rfl
  | true =>
    exact False.elim (noModel FaceCapacity.no_three (fun o v left real => FaceCapacity.no_tetra o v real left)
      built (graph_fork A G same bags res))

theorem stacked_planar {d : List Nat} (A : Layers.Model d) (built : StackedMap A.map) (G : Graph d.length)
    (same : ∀ i j : Fin d.length, A.edge i.val j.val ↔ G.adj i j = true) : G.Planar := by
  constructor
  · rintro ⟨bags,hm⟩
    rw [StackedMinor.no_clique5_minor A built G same bags] at hm
    contradiction
  · rintro ⟨bags,hm⟩
    rw [no_biclique33_minor A built G same bags] at hm
    contradiction

#print axioms stacked_planar

end Recognition.BipartiteMinor
