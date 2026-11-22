import TightFaces
import LeanPool.K5MinorFreeChoosability.Wagner.WagnerA

/-! An edge-maximal spherical embedding has no missing cofacial edge. -/
namespace Recognition.Augment
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem cofacial (M : PlaneMap G) (hm : Maximal IsPlanar G) {p q : G.Dart}
    (same : SameCycle M.facePerm p q) (ne : p.fst ≠ q.fst) : G.Adj p.fst q.fst := by
  by_contra missing
  let H := addEdgeGraph G p.fst q.fst
  have spec := addEdgeGraph_adj (G := G) ne
  obtain ⟨P,_⟩ := exists_planeMap_addEdge M spec missing p q rfl rfl same
  have leq : H ≤ G := hm.2 ⟨P⟩ fun _ _ h => (spec ..).mpr (.inl h)
  exact missing (leq ((spec ..).mpr (.inr (.inl ⟨rfl,rfl⟩))))

omit [DecidableEq V] in
theorem link_edge (M : PlaneMap G) (hm : Maximal IsPlanar G) (d : G.Dart)
    (ne : d.snd ≠ (M.rot d).snd) : G.Adj d.snd (M.rot d).snd := by
  let p := d.symm
  let q := M.facePerm (M.rot d)
  have step : M.facePerm p = M.rot d := by simp [p,PlaneMap.facePerm_apply]
  have same : SameCycle M.facePerm p q := by
    dsimp [q]; rw [←step]
    exact sameCycle_apply_right.mpr (sameCycle_apply_right.mpr (SameCycle.refl ..))
  have qfst : q.fst = (M.rot d).snd := facePerm_fst M.isRotationSystem _
  exact qfst ▸ cofacial M hm same (by rw [qfst]; exact ne)

private theorem cyclic_induction {A : Type*} [Finite A] (π : Perm A) (P : A → Prop)
    {x y : A} (cycle : SameCycle π x y) (base : P x) (step : ∀ z, P z → P (π z)) : P y := by
  obtain ⟨k,rfl⟩ := cycle.exists_nat_pow_eq
  clear cycle
  induction k with
  | zero => simpa using base
  | succ k ih => rw [pow_succ',Perm.mul_apply]; exact step _ ih

private theorem link_colors (M : PlaneMap G) (hm : Maximal IsPlanar G) (z : V)
    (W : Finset V) (small : W.card ≤ 1) (f : V → Bool)
    (edge : ∀a b, G.Adj a b → a ∉ insert z W → b ∉ insert z W → f a = f b)
    {u v : V} (zu : G.Adj z u) (zv : G.Adj z v) (uw : u ∉ W) (vw : v ∉ W) : f u = f v := by
  classical
  let a : G.Dart := ⟨(z,u),zu⟩
  let b : G.Dart := ⟨(z,v),zv⟩
  have prop (start : G.Dart) (c : Bool) (src : start.fst = z) (base : start.snd ∈ W ∨ f start.snd = c)
      (reset : ∀d : G.Dart, d.fst=z → d.snd∈W → f (M.rot d).snd = c)
      (t : G.Dart) (tSrc : t.fst=z) (good : t.snd∉W) : f t.snd=c := by
    have same := M.isRotationSystem.sameCycle start t (src.trans tSrc.symm)
    have got := cyclic_induction M.rot (fun d => d.fst=z ∧ (d.snd ∈ W ∨ f d.snd=c))
      same ⟨src,base⟩ (by
        rintro d ⟨hs,prior⟩
        have rs := (M.isRotationSystem.fst_apply d).trans hs
        refine ⟨rs,?_⟩
        by_cases next : (M.rot d).snd ∈ W
        · exact .inl next
        right
        by_cases cur : d.snd∈W
        · exact reset d hs cur
        have col := prior.resolve_left cur
        by_cases eq : d.snd=(M.rot d).snd
        · exact eq ▸ col
        exact (edge _ _ (link_edge M hm d eq)
          (by simpa [hs,cur] using d.adj.ne.symm)
          (by simpa [rs,next] using (M.rot d).adj.ne.symm)).symm.trans col)
    exact got.2.resolve_left good
  by_cases ex : ∃ d : G.Dart, d.fst=z ∧ d.snd∈W
  · obtain ⟨d,src,bad⟩ := ex
    have reset (e : G.Dart) (h : e.fst=z) (w : e.snd∈W) : f (M.rot e).snd = f (M.rot d).snd := by
      have ed : e=d := (SimpleGraph.Dart.ext_iff _ _).mpr (Prod.ext (h.trans src.symm) (Finset.card_le_one_iff.mp small w bad))
      rw [ed]
    exact (prop d _ src (.inl bad) reset a rfl uw).trans (prop d _ src (.inl bad) reset b rfl vw).symm
  · have e := prop a (f u) rfl (.inr rfl)
      (fun d h w => False.elim (ex ⟨d,h,w⟩)) b rfl vw
    exact e.symm

private theorem constant_off (M : PlaneMap G) (hm : Maximal IsPlanar G) (conn : G.Connected)
    (W : Finset V) (small : W.card ≤ 2) (f : V → Bool)
    (edge : ∀a b, G.Adj a b → a∉W → b∉W → f a=f b)
    (a b : V) (ha : a∉W) (hb : b∉W) : f a=f b := by
  classical
  induction W using Finset.induction generalizing f with
  | empty =>
    have walk {x y : V} (w : G.Walk x y) : f x=f y := by
      induction w with
      | nil => rfl
      | cons h q ih => exact (edge _ _ h (by simp) (by simp)).trans ih
    exact walk (conn.preconnected a b).some
  | @insert z W hz ih =>
    have wsmall : W.card ≤ 1 := by simp [Finset.card_insert_of_notMem hz] at small; omega
    let good := ∃u, G.Adj z u ∧ u∉W
    let c := if p : good then f p.choose else false
    let g (x : V) := if x=z then c else f x
    have fc {u} (adj : G.Adj z u) (out : u∉W) : f u = c := by
      have p : good := ⟨u,adj,out⟩
      dsimp only [c]
      rw [dite_eq_left p]
      exact link_colors M hm z W wsmall f edge adj p.choose_spec.1 out p.choose_spec.2
    have gEdge (x y : V) (xy : G.Adj x y) (xw : x∉W) (yw : y∉W) : g x=g y := by
      by_cases xz : x=z
      · subst x
        have yz := xy.ne.symm
        simp [g,yz,fc xy yw]
      by_cases yz : y=z
      · subst y
        simp [g,xz,fc xy.symm xw]
      dsimp only [g]
      simpa [xz,yz] using edge x y xy (by simp [xz,xw]) (by simp [yz,yw])
    have ah : a ≠ z ∧ a ∉ W := by simpa using ha
    have bh : b ≠ z ∧ b ∉ W := by simpa using hb
    simpa [g,ah.1,bh.1] using ih (by omega) g gEdge ah.2 bh.2

theorem maximal_no_small_sep (M : PlaneMap G) (hm : Maximal IsPlanar G) (conn : G.Connected) :
    NoSmallSep G Finset.univ := by
  classical
  intro A B union small cut
  by_cases sub : A ⊆ B
  · exact .inl sub
  right
  obtain ⟨a,ha,ha'⟩ := Finset.not_subset.mp sub
  intro b hb
  by_contra hb'
  have side (v : V) : v∈A ∨ v∈B := Finset.mem_union.mp (union ▸ Finset.mem_univ v)
  let f (v : V) := decide (v∈A)
  have edge (u v : V) (adj : G.Adj u v) (ou : u ∉ A∩B) (ov : v ∉ A∩B) : f u=f v := by
    by_cases l : u∈A <;> by_cases r : v∈A <;> simp [f,l,r]
    · exact cut u l (fun h => ou (Finset.mem_inter.mpr ⟨l,h⟩)) v ((side v).resolve_left r) r adj
    · exact cut v r (fun h => ov (Finset.mem_inter.mpr ⟨r,h⟩)) u ((side u).resolve_left l) l adj.symm
  have broken := constant_off M hm conn (A∩B) small f edge a b (by simp [ha']) (by simp [hb'])
  simp [f,ha,hb'] at broken

private theorem facial_period (M : PlaneMap G) (hm : Maximal IsPlanar G)
    (sep : NoSmallSep G Finset.univ) (conn : G.Connected)
    (minDeg : ∀v, 2 ≤ Nat.card {u // G.Adj v u}) (d : G.Dart) :
    M.facePerm (M.facePerm (M.facePerm d)) = d := by
  let φ := M.facePerm
  have step (x : G.Dart) : SameCycle φ x (φ x) := sameCycle_apply_right.mpr (SameCycle.refl ..)
  have start (x : G.Dart) : (φ x).fst = x.snd := facePerm_fst M.isRotationSystem _
  have one := numComponents_le_one_of_connected M.isRotationSystem conn
  have simple {x y : G.Dart} (sc : SameCycle φ x y) (eq : x.fst=y.fst) : x=y :=
    M.eq_of_sameCycle_face_of_fst (S := Finset.univ) (fun _ _ _ => Finset.mem_univ _) sep one sc eq
  let g := φ (φ d)
  have sg : SameCycle φ d g := (step d).trans (step (φ d))
  have distinct : d.fst ≠ g.fst := by
    intro eq
    exact face_face_ne_self M.isRotationSystem minDeg d (simple sg eq).symm
  let e : G.Dart := ⟨(d.fst,g.fst), cofacial M hm sg distinct⟩
  have notEdge : d.snd ≠ g.fst := by
    change d.snd ≠ (φ (φ d)).fst
    rw [start,←start d]
    exact (φ d).adj.ne
  have diff : ¬ SameCycle φ d e := fun same => notEdge (congrArg (fun a : G.Dart => a.snd) (simple same rfl))
  have corners := M.two_faces_share (S := Finset.univ) (fun _ _ _ => Finset.mem_univ _)
    sep one (g₁ := d) (g₂ := e) (g₁' := g) (g₂' := φ e) rfl (start e).symm distinct sg (step e) diff
  rcases corners with ⟨contr,_⟩ | ⟨_,rot⟩
  · exact (notEdge contr).elim
  · have close : φ e.symm = d := by simpa [φ,PlaneMap.facePerm_apply] using rot
    have rev : SameCycle φ g e.symm := sg.symm.trans (close ▸ (step e.symm).symm)
    have eq : g = e.symm := simple rev rfl
    change φ g = d
    rw [eq,close]

private theorem sep_min_degree (sep : NoSmallSep G Finset.univ) (order : 4 ≤ Nat.card V) (x : V) :
    3 ≤ Nat.card {y // G.Adj x y} := by
  classical
  let N := Finset.univ.filter (G.Adj x)
  have card : Nat.card {y // G.Adj x y}=N.card := by simp [N,Nat.card_eq_fintype_card,Fintype.card_subtype]
  by_contra low
  have small : N.card ≤ 2 := by omega
  let A := insert x N
  let B := (Finset.univ : Finset V).erase x
  have union : A ∪ B = Finset.univ := by
    ext v; by_cases v=x <;> simp_all [A,B]
  have meet : A∩B ⊆ N := by
    intro v mem
    obtain ⟨va,vb⟩ := Finset.mem_inter.mp mem
    exact (Finset.mem_insert.mp va).resolve_left (Finset.mem_erase.mp vb).1
  have cut (u : V) (_ : u∈A) (ub : u∉B) (v : V) (_ : v∈B) (va : v∉A) : ¬G.Adj u v := by
    have eq : u=x := by simpa [B] using ub
    subst u
    intro adj
    exact va (Finset.mem_insert_of_mem (by simp [N,adj]))
  rcases sep A B union ((Finset.card_le_card meet).trans small) cut with sub|sub
  · have h := sub (Finset.mem_insert_self x N)
    simp [B] at h
  · have eq : A=Finset.univ := by rw [←union,Finset.union_eq_left.mpr sub]
    have size : A.card ≤ N.card+1 := Finset.card_insert_le ..
    rw [eq,Finset.card_univ,←Nat.card_eq_fintype_card] at size
    omega

/-- Every edge-maximal connected planar graph on at least four labels attains
Euler's edge bound and has minimum degree three. -/
theorem maximal_tight (M : PlaneMap G) (hm : Maximal IsPlanar G) (conn : G.Connected)
    (order : 4 ≤ Nat.card V) :
    (∀v, 3 ≤ Nat.card {u // G.Adj v u}) ∧ Nat.card G.edgeSet + 6 = 3 * Nat.card V := by
  classical
  have sep := maximal_no_small_sep M hm conn
  have minDeg := sep_min_degree sep order
  have two (v : V) : 2 ≤ Nat.card {u // G.Adj v u} := (by decide : 2≤3) |>.trans (minDeg v)
  have tri := facial_period M hm sep conn two
  have pow3 (d : G.Dart) : (M.facePerm ^ 3) d = d := by
    simpa [pow_succ,Perm.mul_apply] using tri d
  have up : Nat.card G.Dart ≤ 3*M.numFaces :=
    card_le_mul_numClasses (SameCycle.setoid M.facePerm) 3 (card_sameCycle_le _ _ (by decide) pow3)
  have down : 3*M.numFaces ≤ Nat.card G.Dart :=
    mul_numClasses_le (SameCycle.setoid M.facePerm) 3 (three_le_card_face M.isRotationSystem two)
  have nbr (v : V) : ∃u,G.Adj v u := by
    obtain ⟨u⟩ := (Nat.card_pos_iff.mp (by have := minDeg v; omega : 0<Nat.card {u // G.Adj v u})).1
    exact ⟨_,u.property⟩
  let : Nonempty G.Dart := by
    obtain ⟨v⟩ := conn.nonempty
    obtain ⟨u,adj⟩ := nbr v
    exact ⟨⟨(v,u),adj⟩⟩
  have verts : cycleCount M.rot = Nat.card V := by
    rw [cycleCount_eq_card_nonisolated M.isRotationSystem]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv nbr)
  have euler := M.euler
  rw [verts] at euler
  have one := numComponents_le_one_of_connected M.isRotationSystem conn
  have pos := one_le_numComponents M.rot (dartSymm G)
  have darts := card_dart_eq_two_mul G
  rw [←card_edgeSet_eq_cycleCount] at darts
  exact ⟨minDeg,by omega⟩

end Recognition.Augment
