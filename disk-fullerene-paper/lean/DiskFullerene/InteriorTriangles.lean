import DiskFullerene.ChordlessCore

namespace DiskFullerene.Dual
open Separation

/-- Traversing a cyclic word in the other direction bypasses a deleted
edge. The entry list need only be injective; the target relation and
vertex labels are arbitrary. -/
private theorem cycle_detour {α β} {x y : α} {C : List α} (nd : C.Nodup) (f : α → β)
    {R : β → β → Prop} (symm : ∀ a b, R a b → R b a)
    (e : (x,y) ∈ sides C)
    (step : ∀ a b, (a,b) ∈ sides C → (a,b) ≠ (x,y) → R (f a) (f b)) :
    Walk R (f x) (f y) := by
  obtain ⟨i,hi,ie⟩ := List.mem_iff_getElem.mp e
  rw [sides_size] at hi; rw [side_at C i hi] at ie
  have good {j} (hj : j < C.length) (miss : j ≠ i) :
      R (f C[j]) (f (C[next C.length j]'(next_bound hj))) := by
    apply step
    · exact List.mem_iff_getElem.mpr ⟨j, by simpa [sides_size] using hj, side_at C j hj⟩
    · intro eq
      exact miss (index_eq nd hj hi ((Prod.mk.inj eq).1.trans (Prod.mk.inj ie).1.symm))
  have linear {a b} (leq : a ≤ b) (hb : b < C.length) (skip : i < a ∨ b ≤ i) :
      Walk R (f (C[a]'(Nat.lt_of_le_of_lt leq hb))) (f C[b]) := by
    induction b with
    | zero => have eq : a=0 := by omega
              subst a; exact .refl
    | succ b ih =>
      by_cases eq : a = b+1
      · subst a; exact .refl
      · have adj := good (j := b) (by omega) (by omega)
        have nxt : next C.length b = b+1 := by simp [next,hb]
        exact (ih (by omega) (by omega) (by omega)).step (by simpa only [nxt] using adj)
  rw [← (Prod.mk.inj ie).1, ← (Prod.mk.inj ie).2]
  apply Walk.symm symm
  by_cases last : i+1 < C.length
  · have start := linear (a := i+1) (b := C.length-1) (by omega) (by omega) (by omega)
    have tail := linear (a := 0) (b := i) (by omega) hi (by omega)
    have nz : next C.length (C.length-1) = 0 := by unfold next; split <;> omega
    have turn := good (j := C.length-1) (by omega) (by omega)
    simp only [nz] at turn
    simpa [next,last] using (start.step turn).trans tail
  · simpa [next,last] using (linear (a := 0) (b := i) (by omega) hi (by omega))

/-- Any edge on a face of the actual primal graph is bypassed by its
remaining boundary edges. Duality in the tree-cotree separation lemma
can therefore be applied in both directions. -/
theorem faceBypassTable {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h) :
    FaceBypass (primal G) (dual G) := by
  intro i e hit
  let P := fun x : Nat => (⟨x%M.ord, Nat.mod_lt _ (by have := G.connectivity.1; omega)⟩ : Fin M.ord)
  let R := Adj (primal G) (fun k => k ≠ e ∧ Separation.incident (dual G) k i)
  have symm : ∀ a b, R a b → R b a := fun _ _ ⟨k,ok,ac⟩ => ⟨k,ok,ac.symm⟩
  have build {d : Dart} (di : incident M i d)
      (eo : endpoints e = d ∨ endpoints e=d.swap) : Walk R (P d.1) (P d.2) := by
    have nd := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem i.isLt))).1
    have rare : M.faces[i.val].Nodup := by simpa using nd
    apply cycle_detour rare P symm di
    intro a b xy miss
    have ai : incident M i (a,b) := xy
    have m := incident_dart G ai
    obtain ⟨k,ek⟩ := repr_dart G m
    have near := reverse_owner G ai
    have aconn := crossTable G ek (Or.inl ⟨ai,near⟩ : Cross M (a,b) i _)
    refine ⟨k, ⟨?_,?_⟩,?_⟩
    · intro eq; subst k
      rcases ek with p|p <;> rcases eo with q|q <;> have same := p.symm.trans q
      · exact miss same
      · have revmem : incident M i d.swap := same ▸ ai
        exact opposite_faces_distinct G hh di revmem rfl
      · have rev := congrArg (fun t : Dart => t.swap) same
        simp only [Prod.swap_swap] at rev
        have revmem : incident M i d.swap := rev ▸ ai
        exact opposite_faces_distinct G hh di revmem rfl
      · exact miss (congrArg (fun t : Dart => t.swap) same)
    · rcases aconn with z|z <;> simp [Separation.incident,z]
    · have bounds := dart_endpoints G m
      rcases ek with z|z
      · exact Or.inl (Prod.ext (Fin.ext (by simp [P,primal,z,Nat.mod_eq_of_lt bounds.1]))
                               (Fin.ext (by simp [P,primal,z,Nat.mod_eq_of_lt bounds.2.1])))
      · exact Or.inr (Prod.ext (Fin.ext (by simp [P,primal,z,Nat.mod_eq_of_lt bounds.2.1]))
                               (Fin.ext (by simp [P,primal,z,Nat.mod_eq_of_lt bounds.1])))
  have bounds := dart_info G (endpoints_mem e)
  have p1 : P (endpoints e).1 = (primal G e).1 := Fin.ext (Nat.mod_eq_of_lt bounds.1)
  have p2 : P (endpoints e).2 = (primal G e).2 := Fin.ext (Nat.mod_eq_of_lt bounds.2.1)
  rw [← p1, ← p2]
  rcases hit with eq|eq
  · have di : incident M (dual G e).1 (endpoints e) := left_incident G (endpoints_mem e)
    exact build (eq ▸ di) (Or.inl rfl)
  · have di : incident M (dual G e).2 (endpoints e).swap := left_incident G (dart_reverse G (endpoints_mem e))
    exact (build (d := (endpoints e).swap) (eq ▸ di) (Or.inr rfl)).symm symm

/-- If every interior vertex touches the boundary, an arbitrary nonempty
collection of primal edges dual to interior-interior edges has a leaf.
In particular the adjacency graph of the wholly interior triangles is a
forest under this hypothesis. This uses the actual sphere, even when the
outer contour of its induced interior graph revisits a vertex. -/
theorem exposed_forest {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (exposed : ∀ v ∈ diskInterior G, ∃ b, IsBoundary G b ∧ b ∈ dualRow G v)
    (S : Edge M → Prop) (ne : ∃ e, S e)
    (internal : ∀ e, S e → (dual G e).1 ∈ diskInterior G ∧ (dual G e).2 ∈ diskInterior G) :
    ∃ e, S e ∧ ∃ t, Separation.incident (primal G) e t ∧
      ∀ k, S k → Separation.incident (primal G) k t → k = e := by
  classical
  apply Classical.byContradiction
  intro noLeaf
  let e0 := ne.choose
  have pc (i j) : Walk (Adj (primal G) (fun _ => True)) i j := by
    have P := primalResilient G e0 e0 i j
    induction P with
    | refl => exact .refl
    | step _ a ih => obtain ⟨e,_,adj⟩ := a; exact ih.step ⟨e,trivial,adj⟩
  have chi := table_euler G
  have cuts := separates_on_sphere (primal := dual G) (dual := primal G)
    (by simp [MapData.faces]) (by have := G.connectivity.1; omega)
    (by omega) pc (faceBypassTable G hh) (S := S) ne (by
      intro e se t et
      apply Classical.byContradiction
      intro none
      apply noLeaf ⟨e,se,t,et,?_⟩
      intro k sk kt
      exact Classical.byContradiction fun neq => none ⟨k,sk,kt,neq⟩)
  let safe := Adj (dual G) (fun e => ¬S e)
  have edge {x y : Face M} (xy : y ∈ dualRow G x) (outside : x ∉ diskInterior G) : safe x y := by
    obtain ⟨d,xy,yx⟩ := (mem_row_iff G x y).1 xy
    obtain ⟨e,eo⟩ := repr_dart G (incident_dart G xy)
    have cross := crossTable G eo (Or.inl ⟨xy,yx⟩ : Cross M d x y)
    refine ⟨e,fun se => outside ?_,cross⟩
    have ins := internal _ se
    rcases cross with eq|eq
    · simpa [eq] using ins.1
    · simpa [eq] using ins.2
  have apexOut : apex M ∉ diskInterior G := fun ai => ((mem_diskInterior G _).1 ai).1 rfl
  have reach (v : Face M) : Walk safe (apex M) v := by
    by_cases apexV : v=apex M
    · subst v; exact .refl
    by_cases bound : IsBoundary G v
    · exact .step .refl (edge bound apexOut)
    have ins := (mem_diskInterior G v).2 ⟨apexV,bound⟩
    obtain ⟨b,bC,bv⟩ := exposed v ins
    have bOut : b ∉ diskInterior G := fun e => ((mem_diskInterior G _).1 e).2 bC
    exact (.step (.step .refl (edge bC apexOut)) (edge ((dual_adj_symmetric G _ _).1 bv) bOut))
  apply cuts
  intro x y
  exact ((reach x).symm (fun _ _ ⟨e,se,ac⟩ => ⟨e,se,ac.symm⟩)).trans (reach y)

/-- A dual triangle (primal vertex) lies wholly in the induced interior
complex if every face through this vertex is a strict interior dual vertex. -/
def Pure {M : MapData} (G : IsDiskFullerene M h) (v : Nat) : Prop :=
  ∀ b : Face M, v ∈ M.faces[b.val] → b ∈ diskInterior G

private theorem face_from {M : MapData} {i : Face M} (m : v ∈ M.faces[i.val]) :
    ∃ w, incident M i (v,w) := by
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp m
  exact ⟨M.faces[i.val][next M.faces[i.val].length k]'(next_bound hk),
    List.mem_iff_getElem.mpr ⟨k,by simpa [sides_size] using hk,by
      rw [side_at _ k hk]; simp [he]⟩⟩

private theorem first_in_face {M : MapData} {i : Face M} (xy : incident M i (a,b)) :
    a ∈ M.faces[i.val] := by
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp xy
  rw [sides_size] at hk; rw [side_at _ k hk] at eq
  exact (Prod.mk.inj eq).1 ▸ List.getElem_mem hk

/-- Classify the three actual faces at a primal triangle by the face at
a given corner and the two faces across its incoming and outgoing sides. -/
theorem three_at_corner {M : MapData} (G : IsDiskFullerene M h) {i j : Face M}
    (a : incident M i (p,v)) (t : M.turn (p,v)=(v,q)) (vj : v ∈ M.faces[j.val]) :
    j=i ∨ j=owner G (v,p) ∨ j=owner G (q,v) := by
  obtain ⟨w,jw⟩ := face_from vj
  have vp := dart_iff.mp (dart_reverse G (incident_dart G a))
  obtain ⟨b,c,_,_,neighbors,t1,t2,_⟩ := rooted_rotation G vp
  have eqb : b=q := congrArg Prod.snd (t1.symm.trans t)
  subst b
  rcases (neighbors w).1 (dart_iff.mp (incident_dart G jw)) with eq|eq|eq
  · subst w; exact Or.inr (Or.inl (owner_eq G jw).symm)
  · subst w; exact Or.inl (face_indices_unique G jw (t ▸ incident_turn G a))
  · subst w
    have vq : incident M i (v,q) := t ▸ incident_turn G a
    have k : incident M (owner G (q,v)) (q,v) := reverse_owner G vq
    have k' : incident M (owner G (q,v)) (v,c) := t2 ▸ incident_turn G k
    exact Or.inr (Or.inr (face_indices_unique G jw k'))

theorem pure_iff {M : MapData} (G : IsDiskFullerene M h) {i : Face M}
    (a : incident M i (p,v)) (t : M.turn (p,v)=(v,q)) :
    Pure G v ↔ i ∈ diskInterior G ∧ owner G (v,p) ∈ diskInterior G ∧ owner G (q,v) ∈ diskInterior G := by
  have b : incident M i (v,q) := t ▸ incident_turn G a
  constructor
  · intro av
    refine ⟨av i (first_in_face b), av _ (first_in_face (reverse_owner G a)), ?_⟩
    have rv := reverse_owner G b
    exact av _ (first_in_face (incident_turn G rv))
  · rintro ⟨ip,ap,bp⟩ j hit
    rcases three_at_corner G a t hit with rfl|rfl|rfl <;> assumption

/-- Around a fixed interior face, a run of three consecutive interior neighbors
gives an edge joining two wholly interior triangles. -/
theorem pure_pair_of_three {M : MapData} (G : IsDiskFullerene M h) {i : Face M}
    (hi : i ∈ diskInterior G) {u v : Nat} (uv : incident M i (u,v))
    (other : owner G (v,u) ∈ diskInterior G)
    {s t : Nat} (before : incident M i (s,u)) (step₁ : M.turn (s,u) = (u,v))
    (step₂ : M.turn (u,v) = (v,t)) (first : owner G (u,s) ∈ diskInterior G)
    (last : owner G (t,v) ∈ diskInterior G) : Pure G u ∧ Pure G v :=
  ⟨(pure_iff G before step₁).2 ⟨hi,first,other⟩,(pure_iff G uv step₂).2 ⟨hi,other,last⟩⟩

/-- If the wholly interior triangles are nonempty and every interior vertex
is exposed, some such triangle has at most one wholly interior neighbor.
The neighbors here are the actual primal cubic adjacency rows. -/
theorem exposed_triangle_ear {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (exposed : ∀ v ∈ diskInterior G, ∃ b, IsBoundary G b ∧ b ∈ dualRow G v)
    (nonempty : ∃ v : Fin M.ord, Pure G v.val) :
    ∃ v : Fin M.ord, Pure G v.val ∧ ∃ pinned : Nat, ∀ z, M.adj v.val z → Pure G z → z=pinned := by
  let S : Edge M → Prop := fun e => Pure G (endpoints e).1 ∧ Pure G (endpoints e).2
  have both {v z} (vPure : Pure G v) (zPure : Pure G z) (vz : M.adj v z) :
      ∃ k : Edge M, S k ∧ (endpoints k = (v,z) ∨ endpoints k = (z,v)) := by
    obtain ⟨k,eq⟩ := repr_dart G (dart_iff.mpr vz)
    exact ⟨k, by rcases eq with eq|eq <;> simp_all [S], eq⟩
  by_cases existsEdge : ∃ e, S e
  · have pureFaces {e : Edge M} (se : S e) :
        (dual G e).1 ∈ diskInterior G ∧ (dual G e).2 ∈ diskInterior G := by
      have l := left_incident G (endpoints_mem e)
      have r := left_incident G (dart_reverse G (endpoints_mem e))
      exact ⟨se.1 _ (first_in_face l), se.2 _ (first_in_face r)⟩
    obtain ⟨e,se,v,ev,leaf⟩ := exposed_forest G hh exposed S existsEdge (fun _ => pureFaces)
    have endpointFact (z : Nat) (hz : M.adj v.val z) (pin : Pure G v.val) (pz : Pure G z) :
        endpoints e = (v.val,z) ∨ endpoints e = (z,v.val) := by
      obtain ⟨k,sk,zs⟩ := both pin pz hz
      have inc : Separation.incident (primal G) k v := by
        rcases zs with eq|eq
        · exact Or.inl (Fin.ext (congrArg Prod.fst eq))
        · exact Or.inr (Fin.ext (congrArg Prod.snd eq))
      exact leaf k sk inc ▸ zs
    have ord := ordered e
    rcases ev with rfl|rfl
    · refine ⟨(primal G e).1,se.1,(endpoints e).2,fun z adj pz => ?_⟩
      obtain h1|h2 := endpointFact z adj se.1 pz
      · exact (congrArg Prod.snd h1).symm
      · have eq : (endpoints e).2 = (endpoints e).1 := congrArg Prod.snd h2; omega
    · refine ⟨(primal G e).2,se.2,(endpoints e).1,fun z adj pz => ?_⟩
      obtain h1|h2 := endpointFact z adj se.2 pz
      · have eq : (endpoints e).1 = (endpoints e).2 := congrArg Prod.fst h1; omega
      · exact (congrArg Prod.fst h2).symm
  · obtain ⟨v,pv⟩ := nonempty
    exact ⟨v,pv,0,fun z hz pz => by
      obtain ⟨k,sk,_⟩ := both pv pz hz
      exact False.elim (existsEdge ⟨k,sk⟩)⟩


/-- The ear triangle's two adjacent edges leading to impure triangles can
be taken in their cyclic order. -/
theorem exposed_ear_corner {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (exposed : ∀ v ∈ diskInterior G, ∃ b, IsBoundary G b ∧ b ∈ dualRow G v)
    (nonempty : ∃ v : Fin M.ord, Pure G v.val) :
    ∃ (v : Fin M.ord) (p q : Nat), Pure G v.val ∧ ¬Pure G p ∧ ¬Pure G q ∧
      p ≠ q ∧ M.adj v.val p ∧ M.turn (p,v.val) = (v.val,q) := by
  obtain ⟨v,vp,k,ear⟩ := exposed_triangle_ear G hh exposed nonempty
  have deg := G.cubic _ (List.getElem_mem (l := M.rows) v.isLt)
  obtain ⟨a,am⟩ : ∃ a, M.adj v.val a := by
    refine ⟨(M.rows[v.val]'v.isLt)[0]'(by omega),?_⟩
    unfold MapData.adj; rw [List.getElem?_eq_getElem v.isLt]; exact List.getElem_mem _
  obtain ⟨b,c,ba,ca,neighbors,ab,bc,cfirst⟩ := rooted_rotation G am
  have bm := (neighbors b).2 (by simp)
  have cm := (neighbors c).2 (by simp)
  have ebc : b≠c := by
    intro e; subst c
    have eq : a=b := congrArg Prod.snd (cfirst.symm.trans bc)
    exact ba eq.symm
  have ex (u : Nat) (addr : M.adj v.val u) (nk : u ≠ k) : ¬Pure G u := fun ok => nk (ear u addr ok)
  by_cases ak : a=k
  · exact ⟨v,b,c,vp,ex _ bm (ak ▸ ba),ex _ cm (ak ▸ ca),ebc,bm,bc⟩
  by_cases bk : b=k
  · exact ⟨v,c,a,vp,ex _ cm (bk ▸ Ne.symm ebc),ex _ am ak,ca,cm,cfirst⟩
  exact ⟨v,a,b,vp,ex _ am ak,ex _ bm bk,Ne.symm ba,am,ab⟩

private theorem previous_dart {M} (G : IsDiskFullerene M h) {i : Face M}
    (xy : incident M i (x,y)) : ∃ z, incident M i (z,x) ∧ M.turn (z,x) = (x,y) := by
  let C := sides M.faces[i.val]
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp (show (x,y) ∈ C from xy)
  let j := if k=0 then C.length-1 else k-1
  have hj : j<C.length := by unfold j; split <;> omega
  have rt : next C.length j=k := by unfold next j; split <;> split <;> omega
  have step : (C[j],(x,y)) ∈ sides C := List.mem_iff_getElem.mpr
    ⟨j,by simpa [sides_size] using hj, by rw [side_at C j hj]; simp [rt, eq]⟩
  have good := List.all_eq_true.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem i.isLt))).2 _ step
  have t : M.turn C[j] = (x,y) := by simpa using good
  have first : C[j].2 = x := congrArg Prod.fst t
  obtain ⟨s,r,e⟩ : ∃ s r, C[j] = (s,r) := ⟨_,_,rfl⟩
  simp [e] at first; subst r
  exact ⟨s,e ▸ List.getElem_mem hj, e ▸ t⟩

/-- At a leaf of the wholly interior triangular subcomplex, the two
exposed edges give two consecutive interior neighbors bracketed by
boundary vertices in the link of an interior vertex. -/
theorem exposed_two_run {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (exposed : ∀ v ∈ diskInterior G, ∃ b, IsBoundary G b ∧ b ∈ dualRow G v)
    (nonempty : ∃ v : Fin M.ord, Pure G v.val) :
    ∃ i a b c d : Face M, i ∈ diskInterior G ∧ IsBoundary G a ∧ IsBoundary G d ∧
      b ∈ diskInterior G ∧ c ∈ diskInterior G ∧
      (a,b) ∈ sides (dualRow G i) ∧ (b,c) ∈ sides (dualRow G i) ∧ (c,d) ∈ sides (dualRow G i) := by
  obtain ⟨v,p,q,pv,imp,imq,pq,vp,t⟩ := exposed_ear_corner G hh exposed nonempty
  have pr := dart_reverse G (dart_iff.mpr vp)
  let i := owner G (p,v.val)
  have pin : incident M i (p,v.val) := owner_incident G pr
  have qin : incident M i (v.val,q) := t ▸ incident_turn G pin
  obtain ⟨s,sin,first⟩ := previous_dart G pin
  let r := (M.turn (v.val,q)).2
  have last : M.turn (v.val,q) = (q,r) := rfl
  have rin : incident M i (q,r) := last ▸ incident_turn G qin
  have ⟨ip,bp,cp⟩ := (pure_iff G pin t).1 pv
  have ap : owner G (p,s) ∉ diskInterior G := fun ai => imp ((pure_iff G sin first).2 ⟨ip,ai,bp⟩)
  have dp : owner G (r,q) ∉ diskInterior G := fun di => imq ((pure_iff G qin last).2 ⟨ip,cp,di⟩)
  have aconn : owner G (p,s) ∈ dualRow G i := (mem_row_iff _ _ _).2 ⟨_,sin,reverse_owner G sin⟩
  have dconn : owner G (r,q) ∈ dualRow G i := (mem_row_iff _ _ _).2 ⟨_,rin,reverse_owner G rin⟩
  have rim {j : Face M} (inrow : j ∈ dualRow G i) (off : j ∉ diskInterior G) : IsBoundary G j := by
    apply Classical.byContradiction; intro outside
    have ne : j≠apex M := fun eq => ((mem_diskInterior G i).1 ip).2 (eq ▸ (dual_adj_symmetric G i j).1 inrow)
    exact off ((mem_diskInterior G j).2 ⟨ne,outside⟩)
  refine ⟨i,owner G (p,s),owner G (v.val,p),owner G (q,v.val),owner G (r,q),
    ip,rim aconn ap,rim dconn dp,bp,cp,?_,?_,?_⟩
  · simpa [first] using across_turn G sin
  · simpa [t] using across_turn G pin
  · simpa [last] using across_turn G qin

end DiskFullerene.Dual
