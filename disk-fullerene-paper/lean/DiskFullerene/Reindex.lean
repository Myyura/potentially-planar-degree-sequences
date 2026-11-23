import DiskFullerene.FaceMap
import DiskFullerene.ConstructionPrimal

namespace DiskFullerene.Reindex
open PrimalSplice

structure SparseFaces (V : Nat → Prop) (E : Nat → Nat → Prop) (outer : List Nat)
    (inner : List (List Nat)) : Prop where
  simple : ∀ f∈outer::inner, f.Nodup ∧ 3≤f.length ∧ ∀ x∈f, V x
  unique : ((outer::inner).flatMap sides).Nodup
  edge : ∀ x y, (x,y) ∈ (outer::inner).flatMap sides ↔ E x y

structure SparseGraph (V : Nat → Prop) (E : Nat → Nat → Prop) : Prop where
  cubic : Cubic V E
  symm : ∀ {x y}, E x y → E y x
  loopless : ∀ x, ¬E x x
  bounds : ∀ {x y}, E x y → V x ∧ V y
  conn : ∀ (gone : List Nat), gone.length ≤ 2 → ∀ {x y}, V x → V y →
    x ∉ gone → y ∉ gone → PathAvoiding E gone x y

def code (vs : VertexList V) (x : Nat) := vs.names.idxOf x

private theorem inj (vs : VertexList V) {a b} (ha : V a) (hb : V b) (eq : code vs a=code vs b) : a=b := by
  have aok := List.idxOf_lt_length_iff.mpr ((vs.mem a).mpr ha)
  have bok := List.idxOf_lt_length_iff.mpr ((vs.mem b).mpr hb)
  change vs.names.idxOf a = vs.names.idxOf b at eq
  calc a = vs.names[vs.names.idxOf a] := (List.getElem_idxOf aok).symm
       _ = vs.names[vs.names.idxOf b] := by simp only [eq]
       _ = b := List.getElem_idxOf bok

private theorem codename (vs : VertexList V) (i : Fin vs.names.length) : code vs vs.names[i.val]=i.val :=
  vs.distinct.idxOf_getElem i.val i.isLt

noncomputable def row {V E} (vs : VertexList V) (g : SparseGraph V E) (v : Fin vs.names.length) :=
  let x := vs.names[v.val]
  let hx := (vs.mem x).mp (List.getElem_mem v.isLt)
  (List.finRange 3).map (fun i => code vs ((g.cubic x hx).choose i))

noncomputable def raw {V E} (vs : VertexList V) (g : SparseGraph V E)
    (o : List Nat) (fs : List (List Nat)) : MapData :=
  ⟨(List.finRange vs.names.length).map (row vs g),o.map (code vs),fs.map (List.map (code vs))⟩

private theorem row_mem {V E} (vs : VertexList V) (g : SparseGraph V E) (v : Fin vs.names.length) (b : Nat) :
    b∈row vs g v ↔ ∃ y, E vs.names[v.val] y ∧ code vs y=b := by
  let x := vs.names[v.val]
  let c := g.cubic x ((vs.mem x).mp (List.getElem_mem v.isLt))
  have ch := c.choose_spec.2
  constructor
  · intro mem
    obtain ⟨i,_,e⟩ := List.mem_map.mp mem
    exact ⟨c.choose i,g.symm ((ch _).mpr ⟨i,rfl⟩),e⟩
  · rintro ⟨y,e,rfl⟩
    obtain ⟨i,hi⟩ := (ch _).mp (g.symm e)
    exact List.mem_map.mpr ⟨i,List.mem_finRange i,congrArg (code vs) hi⟩

private theorem row_nd {V E} (vs : VertexList V) (g : SparseGraph V E) (v : Fin vs.names.length) :
    (row vs g v).Nodup := by
  let x := vs.names[v.val]
  let c := g.cubic x ((vs.mem x).mp (List.getElem_mem v.isLt))
  have bounds (i) : V (c.choose i) := (g.bounds (c.choose_spec.2 _ |>.mpr ⟨i,rfl⟩)).1
  apply List.pairwise_map.mpr
  exact (List.nodup_finRange _).imp (fun ne eq => ne (c.choose_spec.1 (inj vs (bounds _) (bounds _) eq)))

private theorem raw_adj {V E} (vs : VertexList V) (g : SparseGraph V E) o fs {a b : Nat} :
    (raw vs g o fs).adj a b ↔ ∃ u v, code vs u=a ∧ code vs v=b ∧ E u v := by
  constructor
  · intro adj
    by_cases lt : a < vs.names.length
    · have mem : b∈row vs g ⟨a,lt⟩ := by simpa [MapData.adj,raw,lt] using adj
      obtain ⟨v,e,hv⟩ := (row_mem vs g _ _).mp mem
      exact ⟨_,v,codename vs ⟨a,lt⟩,hv,e⟩
    · simp [MapData.adj,raw,lt] at adj
  · rintro ⟨u,v,rfl,rfl,e⟩
    have h := g.bounds e
    have lt := List.idxOf_lt_length_iff.mpr ((vs.mem u).mpr h.1)
    let j : Fin vs.names.length := ⟨code vs u,lt⟩
    have mem := (row_mem vs g j (code vs v)).mpr ⟨v,by simpa [j,code,List.getElem_idxOf] using e,rfl⟩
    change code vs v ∈ ((List.finRange vs.names.length).map _)[code vs u]?.getD []
    simpa [j,code,lt] using mem

private theorem natMapSides (f : α → β) (xs : List α) :
    sides (xs.map f) = (sides xs).map (Prod.map f f) := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [sides, ← List.zip_map]

private theorem rawSides {V E} (vs : VertexList V) (g : SparseGraph V E) o fs :
    ((raw vs g o fs).faces.flatMap sides) =
    ((o::fs).flatMap sides).map (Prod.map (code vs) (code vs)) := by
  change (((o::fs).map (List.map (code vs))).flatMap sides) = _
  rw [List.flatMap_map,List.map_flatMap]
  simp [natMapSides]

theorem raw_words {V E o fs} (vs : VertexList V) (g : SparseGraph V E) (F : SparseFaces V E o fs) :
    FaceMap.WordsOK (raw vs g o fs) := by
  let M := raw vs g o fs
  have size : M.ord = vs.names.length := by simp [M,raw,MapData.ord]
  have graph : M.rotationOK = true := by
    apply List.all_eq_true.mpr
    rintro ⟨r,a⟩ mem
    have idx := List.mk_mem_zipIdx_iff_getElem?.mp mem
    obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp idx
    have lt : a<vs.names.length := by change a<M.ord at bound; omega
    let i : Fin vs.names.length := ⟨a,lt⟩
    have rr : r=row vs g i := by simpa [M,raw,i,lt] using idx.symm
    rw [rr]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true (row_nd vs g i),List.all_eq_true.mpr ?_⟩
    intro b mb
    obtain ⟨v,e,rfl⟩ := (row_mem vs g i b).mp mb
    have h := g.bounds e
    have cb := List.idxOf_lt_length_iff.mpr ((vs.mem v).mpr h.2)
    have ca := codename vs i
    have ne : code vs v ≠ a := by
      intro eq
      have ve := inj vs h.2 h.1 (eq.trans ca.symm)
      exact g.loopless _ (ve ▸ e)
    have back := (raw_adj vs g o fs).mpr ⟨v,vs.names[i.val],rfl,ca,g.symm e⟩
    change (decide (code vs v < M.ord) && (code vs v != a) && ((M.rows[code vs v]? ).getD []).contains a) = true
    rw [size]
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true cb,by simpa using ne⟩,
      List.contains_iff_mem.mpr back⟩
  refine ⟨?_,graph,?_,?_⟩
  · intro r hr; obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr; simp [row]
  · rw [rawSides]
    apply (List.perm_ext_iff_of_nodup _ (FaceMap.graph_dart_nodup graph)).mpr
    · rintro ⟨a,b⟩
      rw [Dual.dart_iff,raw_adj]
      constructor
      · rintro mem
        obtain ⟨⟨u,v⟩,h,eq⟩ := List.mem_map.mp mem
        exact ⟨u,v,congrArg Prod.fst eq,congrArg Prod.snd eq,(F.edge u v).mp h⟩
      · rintro ⟨u,v,hu,hv,e⟩
        exact List.mem_map.mpr ⟨(u,v),(F.edge u v).mpr e,Prod.ext hu hv⟩
    · apply List.pairwise_map.mpr
      apply F.unique.imp_of_mem
      rintro ⟨u,v⟩ ⟨a,b⟩ h1 h2 ne eq
      have A := g.bounds ((F.edge _ _).mp h1)
      have B := g.bounds ((F.edge _ _).mp h2)
      exact ne (Prod.ext (inj vs A.1 B.1 (congrArg Prod.fst eq)) (inj vs A.2 B.2 (congrArg Prod.snd eq)))
  · intro f hf
    change f∈(o::fs).map (List.map (code vs)) at hf
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hf
    obtain ⟨nd,len,valid⟩ := F.simple _ hw
    refine ⟨List.pairwise_map.mpr (nd.imp_of_mem ?_),by simpa using len⟩
    intro a b ha hb ne eq
    exact ne (inj vs (valid _ ha) (valid _ hb) eq)


private theorem banned_iff (vs : VertexList V) (gone : List Nat) {u} (hu : V u) :
    u ∈ gone.filterMap (fun i => vs.names[i]?) ↔ code vs u ∈ gone := by
  constructor
  · intro h
    obtain ⟨i,hi,lookup⟩ := List.mem_filterMap.mp h
    obtain ⟨ok,eq⟩ := List.getElem?_eq_some_iff.mp lookup
    have key := codename vs ⟨i,ok⟩; change code vs vs.names[i]=i at key
    rwa [← eq,key]
  · intro h
    have small := List.idxOf_lt_length_iff.mpr ((vs.mem _).mpr hu)
    exact List.mem_filterMap.mpr ⟨code vs u,h, by
      unfold code; rw [List.getElem?_eq_getElem small,List.getElem_idxOf small]⟩

theorem raw_connected {V E} (vs : VertexList V) (g : SparseGraph V E) (o fs)
    (big : 4 ≤ vs.names.length) : (raw vs g o fs).ThreeConnected := by
  have size : (raw vs g o fs).ord = vs.names.length := by simp [MapData.ord,raw]
  refine ⟨size ▸ big,?_⟩
  intro gone len a b ha hb ga gb
  rw [size] at ha hb
  let A := vs.names[a]; let B := vs.names[b]
  have va : V A := (vs.mem _).mp (List.getElem_mem ha)
  have vb : V B := (vs.mem _).mp (List.getElem_mem hb)
  have ka : code vs A=a := codename vs ⟨a,ha⟩
  have kb : code vs B=b := codename vs ⟨b,hb⟩
  let bad := gone.filterMap (fun i => vs.names[i]?)
  have short : bad.length ≤ 2 := Nat.le_trans (List.length_filterMap_le _ _) len
  have path := g.conn bad short va vb (fun h => ga (ka ▸ (banned_iff vs gone va).mp h))
    (fun h => gb (kb ▸ (banned_iff vs gone vb).mp h))
  have lift {y} (p : PathAvoiding E bad A y) :
      PathAvoiding (raw vs g o fs).adj gone (code vs A) (code vs y) := by
    induction p with
    | here => exact .here (ka ▸ ga)
    | @step u v _ e ok ih =>
      exact ih.step ((raw_adj vs g o fs).mpr ⟨u,v,rfl,rfl,e⟩)
        (fun h => ok ((banned_iff vs gone (g.bounds e).2).mpr h))
  simpa [ka,kb] using lift path

/-- Direct realization of sparse labelled facial words on the original
definition, including three-connectivity and equality of all face lengths. -/
theorem realize {V E o fs} (vs : VertexList V) (g : SparseGraph V E) (F : SparseFaces V E o fs)
    {h : Nat} (big : 4≤vs.names.length)
    (chi : 2*vs.names.length+2*(1+fs.length)=3*vs.names.length+4)
    (outer : o.length=h) (polygons : ∀ f∈fs, f.length=5 ∨ f.length=6) :
    ∃ M, IsDiskFullerene M h ∧ M.ord=vs.names.length ∧ M.outer=o.map (code vs) ∧
      M.inner=fs.map (List.map (code vs)) ∧ M.hexagons=(fs.map List.length).count 6 := by
  let M := raw vs g o fs
  let W := raw_words vs g F
  have size : M.ord=vs.names.length := by simp [M,MapData.ord,raw]
  refine ⟨FaceMap.oriented W,FaceMap.realize W h ?_ (raw_connected vs g _ _ big) ?_ ?_,
    (FaceMap.oriented_ord W).trans size,rfl,rfl,?_⟩
  · rw [cubic_dart_count W.cubic]
    have len : M.faces.length=1+fs.length := by simp [M,MapData.faces,raw,Nat.add_comm]
    change 2*M.ord+2*M.faces.length=3*M.ord+4
    rw [size,len]
    exact chi
  · simpa [raw] using outer
  · simp only [raw,List.mem_map,forall_exists_index,and_imp]
    intro f u hu eq; subst f; simpa using polygons u hu
  · change (((fs.map _).map List.length).count 6) = _
    simp [List.map_map,Function.comp_def]

end DiskFullerene.Reindex
