import DiskFullerene.EndTriangles
import DiskFullerene.EndGeometry

namespace DiskFullerene.EndLabels
open EndGeometry Lower Dual EndEuler Separation

theorem length_le_by_matching {α β : Type} {xs : List α} {ys : List β} (nd : xs.Nodup)
    (R : α→β→Prop) (hit : ∀ x ∈ xs, ∃ y ∈ ys, R x y)
    (uniq : ∀ x ∈ xs, ∀ z ∈ xs, ∀ y, R x y → R z y → x=z) : xs.length≤ys.length := by
  classical
  let f (x : α) : Option β := if h : x∈xs then some (hit x h).choose else none
  have fdef (x) (h : x∈xs) : f x=some (hit x h).choose := by simp [f,h]
  have rare : (xs.map f).Nodup := by
    apply List.pairwise_map.mpr; apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt eq
    have a := List.getElem_mem (l:=xs) hi; have b := List.getElem_mem (l:=xs) hj
    rw [fdef _ a,fdef _ b] at eq
    have ha := (hit _ a).choose_spec.2; have hb := (hit _ b).choose_spec.2
    rw [Option.some.inj eq] at ha
    exact (List.pairwise_iff_getElem.mp nd i j hi hj lt) (uniq _ a _ b _ ha hb)
  have sub : xs.map f ⊆ ys.map some := by
    intro z hz; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact List.mem_map.mpr ⟨_,(hit _ hx).choose_spec.1,(fdef x hx).symm⟩
  simpa using rare.length_le_of_subset sub

def items {n} (A : Fin n→Bool) := (List.finRange n).filter A

@[simp] theorem selected {n} {A : Fin n→Bool} {f : Fin n} : f ∈ items A ↔ A f=true := by simp [items]

def label {n} (A : Fin n→Bool) (f : Fin n) := (items A).idxOf f

theorem decode_label {n} {A : Fin n→Bool} {f : Fin n} (hf : A f=true) : (items A)[label A f]?=some f :=
  List.getElem?_eq_some_iff.mpr ⟨List.idxOf_lt_length_iff.mpr (selected.mpr hf),List.getElem_idxOf _⟩

theorem label_decode {n} {A : Fin n→Bool} {i : Nat} {f : Fin n} (hi : (items A)[i]?=some f) :
    A f=true ∧ label A f=i := by
  obtain ⟨lt,rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact ⟨selected.mp (List.getElem_mem _),List.Nodup.idxOf_getElem ((List.nodup_finRange _).filter A) _ lt⟩

@[simp] theorem in_labels (v : Nat) : v ∈ labels ↔ v<5 := by simp [labels]; omega

noncomputable def relation {M : MapData} (G : IsDiskFullerene M h) (A : Face M→Bool) (i j : Nat) : Bool :=
  match (items A)[i]?, (items A)[j]? with
  | some f, some g => (dualRow G f).contains g
  | _,_ => false

noncomputable def graph {M : MapData} (G : IsDiskFullerene M h) (A : Face M→Bool) := encode (relation G A)

theorem edge_iff {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M→Bool) {i j : Nat} (hi : i<5) (hj : j<5) :
    adjacent (graph G A) i j=true ↔ ∃ f g, (items A)[i]?=some f ∧ (items A)[j]?=some g ∧ g∈dualRow G f := by
  have nl (x : Fin 5) : relation G A x.val x.val=false := by
    unfold relation; cases (items A)[x.val]? <;> simp [row_no_loop G hh]
  have sym (x y : Fin 5) : relation G A x.val y.val=relation G A y.val x.val := by
    unfold relation; cases (items A)[x.val]? <;> cases (items A)[y.val]? <;> simp [dual_adj_symmetric]
  rw [graph,encode_adjacent _ nl sym (⟨i,hi⟩ : Fin 5) (⟨j,hj⟩ : Fin 5)]
  unfold relation; cases (items A)[i]? <;> cases (items A)[j]? <;> simp

private theorem pair_table : pairs.all (fun p => match p with
  | [a,b] => decide (a<b ∧ b<5)
  | _ => false) = true := by decide

private theorem pair_shape {p : List Nat} (hp : p∈pairs) : ∃ a b, p=[a,b] ∧ a<b ∧ b<5 := by
  have t := List.all_eq_true.mp pair_table p hp
  split at t <;> simp_all <;> grind

private theorem edge_find {M} (G : IsDiskFullerene M h) {f g : Face M} (hfg : g ∈ dualRow G f) : ∃ e, Across (dual G) e f g := by
  obtain ⟨d,fd,gd⟩ := (mem_row_iff G _ _).mp hfg
  obtain ⟨e,ed⟩ := repr_dart G (incident_dart G fd)
  exact ⟨e,crossTable G ed (Or.inl ⟨fd,gd⟩)⟩

/-- Every edge of the five-index representation comes from a distinct
actual edge in the induced dual subgraph. -/
theorem edge_count {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M→Bool) :
    eCount (graph G A) ≤ num (sideEdge (dual G) A) := by
  simp only [eCount,num,List.countP_eq_length_filter]
  let R (p : List Nat) (e : Edge M) := ∃ a b f g, p=[a,b] ∧ a<b ∧ (items A)[a]?=some f ∧ (items A)[b]?=some g ∧ Across (dual G) e f g
  apply length_le_by_matching ((show pairs.Nodup by decide).filter _) R
  · intro p hp
    obtain ⟨m,test⟩ := List.mem_filter.mp hp
    obtain ⟨a,b,rfl,lo,hi⟩ := pair_shape m
    have edge : adjacent (graph G A) a b=true := by simpa [clique, Nat.ne_of_lt lo] using (List.all_eq_true.mp (List.all_eq_true.mp test a (by simp)) b (by simp))
    obtain ⟨f,g,df,dg,nb⟩ := (edge_iff G hh A (by omega) hi).mp edge
    obtain ⟨e,ac⟩ := edge_find G nb
    refine ⟨e, List.mem_filter.mpr ⟨List.mem_finRange _,?_⟩, a,b,f,g,rfl,lo,df,dg,ac⟩
    rcases ac with eq|eq <;> simp [sideEdge,eq,(label_decode df).1,(label_decode dg).1]
  · rintro p _ z _ e ⟨a,b,f,g,rfl,ab,df,dg,ac⟩ ⟨c,d,i,j,rfl,cd,di,dj,bc⟩
    have indeq {k l : Nat} {u v : Face M} (ku : (items A)[k]?=some u) (lv : (items A)[l]?=some v) (uv : u=v) : k=l := by
      subst v; exact (label_decode ku).2.symm.trans (label_decode lv).2
    rcases ac with eq|eq <;> rcases bc with ep|ep <;> have fact := Prod.mk.inj (eq.symm.trans ep) <;> grind

theorem small_label {n} {A : Fin n→Bool} (sz : num A≤5) {f : Fin n} (hf : A f=true) : label A f < 5 := by
  have lt := List.idxOf_lt_length_iff.mpr (selected.mpr hf)
  have size : (items A).length=num A := (List.countP_eq_length_filter ..).symm
  change (items A).idxOf f<5; omega

theorem active_count {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M→Bool) (sz : num A≤5)
    (nonisolated : ∀ f, A f=true → ∃ g∈dualRow G f, A g=true) :
    num A ≤ vCount (graph G A) := by
  unfold vCount num; simp only [List.countP_eq_length_filter]
  apply length_le_by_matching ((List.nodup_finRange _).filter A) (fun f i=>label A f=i)
  · intro f hf
    have ff := (List.mem_filter.mp hf).2
    obtain ⟨g,nb,gg⟩ := nonisolated f ff
    have fl := small_label sz ff; have gl := small_label sz gg
    have e := (edge_iff G hh A fl gl).mpr ⟨f,g,decode_label ff,decode_label gg,nb⟩
    have m : label A g ∈ innerNeighbors (graph G A) (label A f) := List.mem_filter.mpr ⟨(in_labels _).mpr gl,e⟩
    exact ⟨_,List.mem_filter.mpr ⟨(in_labels _).mpr fl,by simp only [Bool.not_eq_true',List.isEmpty_eq_false_iff]; intro nil; simp [nil] at m⟩,rfl⟩
  · intro f hf g hg i fi gi
    have eq := fi.trans gi.symm
    have fd := decode_label ((List.mem_filter.mp hf).2); have gd := decode_label ((List.mem_filter.mp hg).2)
    rw [eq] at fd; exact Option.some.inj (fd.symm.trans gd)

noncomputable def word {M : MapData} (A : Face M→Bool) (u : Fin M.ord) :=
  labels.filter fun i => ((items A)[i]?).any (fun f => (triangle u).contains f)

@[simp] theorem word_mem {M} {A : Face M→Bool} {u : Fin M.ord} {i : Nat} : i∈word A u ↔
    i<5 ∧ ∃ f, (items A)[i]?=some f ∧ f∈triangle u := by
  simp only [word,List.mem_filter,in_labels]; cases (items A)[i]? <;> simp

private theorem word_perm {M} (G : IsDiskFullerene M h) (A : Face M→Bool) (sz : num A≤5) (u : Fin M.ord)
    (mono : solid G A true u=true) : (word A u).Perm ((triangle u).map (label A)) := by
  have allIn := (solid_iff G A u).mp mono
  apply (List.perm_ext_iff_of_nodup ((show labels.Nodup by decide).filter _) ?_).mpr
  · intro i; change i ∈ word A u ↔ i∈(triangle u).map (label A); rw [word_mem,List.mem_map]; constructor
    · rintro ⟨_,f,df,uf⟩; exact ⟨f,uf,(label_decode df).2⟩
    · rintro ⟨f,uf,rfl⟩; exact ⟨small_label sz (allIn f uf),f,decode_label (allIn f uf),uf⟩
  · apply List.pairwise_map.mpr; apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt eq
    have fi := List.getElem_mem (l:=triangle u) hi; have gj := List.getElem_mem (l:=triangle u) hj
    have fd := decode_label (allIn _ fi); have gd := decode_label (allIn _ gj)
    rw [eq] at fd
    exact (List.pairwise_iff_getElem.mp ((List.nodup_finRange _).filter _) i j hi hj lt) (Option.some.inj (fd.symm.trans gd))

private theorem side_vertices {α} {r : List α} {a b : α} (m : (a,b)∈sides r) : a∈r ∧ b∈r := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp m
  rw [sides_size] at hi; rw [side_at _ _ hi] at eq
  exact ⟨(Prod.mk.inj eq).1 ▸ List.getElem_mem _,(Prod.mk.inj eq).2 ▸ List.getElem_mem _⟩

private theorem adjacent_triangle {M} (G : IsDiskFullerene M h) (hh : 3≤h) {f g : Face M} {u : Fin M.ord}
    (hf : f∈triangle u) (hg : g∈triangle u) (ne : f≠g) : g∈dualRow G f := by
  obtain ⟨a,b,C,_,_,_,fs⟩ := corners_at G hh ((mem_triangle _ _).mp hf)
  rcases (fs g).mp ((mem_triangle _ _).mp hg) with eq|rfl|rfl
  · exact False.elim (ne eq.symm)
  · exact (side_vertices C.step).1
  · exact (side_vertices C.step).2

private theorem word_admitted {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M→Bool) (sz : num A≤5) {u : Fin M.ord}
    (mono : solid G A true u=true) : word A u ∈ triples.filter (clique (graph G A)) := by
  have candidate : (subsets labels).all (fun q => q.length != 3 || triples.contains q) = true := by decide
  have rule := List.all_eq_true.mp candidate (word A u) (filter_subset _ labels)
  have degree := (word_perm G A sz u mono).length_eq
  simp only [List.length_map,triangle_three G hh] at degree
  apply List.mem_filter.mpr; refine ⟨by simpa [degree] using rule,?_⟩
  apply List.all_eq_true.mpr; intro i hi; apply List.all_eq_true.mpr; intro j hj
  by_cases eq : i=j
  · simp [eq]
  obtain ⟨il,f,df,ft⟩ := word_mem.mp hi; obtain ⟨jl,g,dg,gt⟩ := word_mem.mp hj
  have ne : f≠g := by intro same; subst g; exact eq ((label_decode df).2.symm.trans (label_decode dg).2)
  simp [(edge_iff G hh A il jl).mpr ⟨f,g,df,dg,adjacent_triangle G hh ft gt ne⟩]

noncomputable def isFace {M} (G : IsDiskFullerene M h) (A : Face M→Bool) (t : List Nat) : Bool :=
  (List.finRange M.ord).any (fun u => solid G A true u && t==word A u)

noncomputable def facial {M} (G : IsDiskFullerene M h) (A : Face M→Bool) := (triples.filter (clique (graph G A))).filter (isFace G A)

theorem facial_witness {M} {G : IsDiskFullerene M h} {A : Face M→Bool} {t : List Nat} (ht : t∈facial G A) :
    ∃ u, solid G A true u=true ∧ t=word A u := by
  simpa [isFace,List.any_eq_true] using (List.mem_filter.mp ht).2

/-- Cubic vertex incidence injects the actual monochromatic triangles
into the admitted triples of the small graph, with their true corners. -/
theorem face_count {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M→Bool) (sz : num A≤5) :
    num (solid G A true) ≤ (facial G A).length := by
  unfold num; rw [List.countP_eq_length_filter]
  apply length_le_by_matching ((List.nodup_finRange _).filter _) (fun u t=>t=word A u)
  · intro u hu; have mono := (List.mem_filter.mp hu).2
    exact ⟨_,List.mem_filter.mpr ⟨word_admitted G hh A sz mono,by simp only [isFace,List.any_eq_true]; exact ⟨u,List.mem_finRange _,by simp [mono]⟩⟩,rfl⟩
  · intro u hu v hv t ut vt
    have agree := ut.symm.trans vt
    have one {v w : Fin M.ord} (yes : solid G A true v=true) (eq : word A v=word A w) {f : Face M} (hit : f∈triangle v) : f∈triangle w := by
      have ff := (solid_iff G A v).mp yes f hit
      have l := decode_label ff
      have m : label A f∈word A v := word_mem.mpr ⟨small_label sz ff,f,l,hit⟩
      obtain ⟨_,j,dj,hj⟩ := word_mem.mp (eq ▸ m)
      exact Option.some.inj (dj.symm.trans l) ▸ hj
    exact same_triangle G hh (fun _=>⟨one (List.mem_filter.mp hu).2 agree,one (List.mem_filter.mp hv).2 agree.symm⟩)

/-- The finite Euler inequality of the ear lemma with every quantity
computed from the original sphere map. -/
theorem encode_euler {M} (G : IsDiskFullerene M h) (hh : 3≤h) {x y} (S : TriangleSide G (apex M) x y)
    (B : Bool) (sz : num (sectorCore S B)≤5) (nonempty : ∃ z,sectorCore S B z=true)
    (nonisolated : ∀ f, sectorCore S B f=true → ∃ g∈dualRow G f, sectorCore S B g=true) :
    eCount (graph G (sectorCore S B))+1 ≤ vCount (graph G (sectorCore S B)) + (facial G (sectorCore S B)).length := by
  have ed := edge_count G hh (sectorCore S B)
  have v := active_count G hh (sectorCore S B) sz nonisolated
  have f := face_count G hh (sectorCore S B) sz
  have euler := sector_core_bound hh S B nonempty
  omega
