import DiskFullerene.EdgeTable

namespace DiskFullerene.Dual

def apex (M : MapData) : Face M := ⟨0,by simp [MapData.faces]⟩

/-- Face on the left of a directed edge. The default at a non-edge does not
enter any of the statements below because every side is an actual dart. -/
noncomputable def owner {M : MapData} (G : IsDiskFullerene M h) (d : Dart) : Face M :=
  if hd : d ∈ M.darts then (dart_has_face G hd).choose else apex M

theorem owner_incident {M : MapData} (G : IsDiskFullerene M h) (hd : d ∈ M.darts) :
    incident M (owner G d) d := by
  simpa [owner,hd] using (dart_has_face G hd).choose_spec.1

theorem owner_eq {M : MapData} {i : Face M} (G : IsDiskFullerene M h) (hd : incident M i d) :
    owner G d = i := face_indices_unique G (owner_incident G (incident_dart G hd)) hd

/-- Neighbor faces in their cyclic order, obtained by crossing consecutive
sides of the actual facial boundary in the input rotation system. -/
noncomputable def dualRow {M : MapData} (G : IsDiskFullerene M h) (i : Face M) : List (Face M) :=
  (sides M.faces[i.val]).map fun d => owner G d.swap

theorem row_length {M : MapData} (G : IsDiskFullerene M h) (i : Face M) :
    (dualRow G i).length = M.faces[i.val].length := by simp [dualRow,sides_size]

theorem reverse_owner {M : MapData} (G : IsDiskFullerene M h) {i : Face M} {d : Dart}
    (hd : incident M i d) : incident M (owner G d.swap) d.swap :=
  owner_incident G (dart_reverse G (incident_dart G hd))

theorem row_nodup {M : MapData} (G : IsDiskFullerene M h) (simple : noRepeat M) (i : Face M) :
    (dualRow G i).Nodup := by
  have allnd := G.coverage.nodup_iff.mpr (dart_nodup G)
  have nd := (List.pairwise_flatMap.mp allnd).1 _ (List.getElem_mem i.isLt)
  apply List.pairwise_map.mpr
  apply List.pairwise_iff_getElem.mpr
  intro k l hk hl lt eq
  have m1 : incident M i _ := List.getElem_mem hk
  have m2 : incident M i _ := List.getElem_mem hl
  have rev := reverse_owner G m2
  have eqd := simple _ _ _ _ m1 (reverse_owner G m1) m2 (eq ▸ rev)
  exact (List.pairwise_iff_getElem.mp nd _ _ hk hl lt) eqd

theorem row_no_loop {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h) (i : Face M) :
    i ∉ dualRow G i := by
  intro m
  obtain ⟨d,hd,eq⟩ := List.mem_map.mp m
  have m' : incident M i d := hd
  exact opposite_faces_distinct G hh m' (reverse_owner G m') eq.symm

theorem mem_row_iff {M : MapData} (G : IsDiskFullerene M h) (i j : Face M) :
    j ∈ dualRow G i ↔ ∃ d, incident M i d ∧ incident M j d.swap := by
  constructor
  · intro h
    obtain ⟨d,hd,e⟩ := List.mem_map.mp h
    have hr := reverse_owner G (show incident M i d from hd)
    exact ⟨d,hd,e ▸ hr⟩
  · rintro ⟨d,hd,he⟩
    exact List.mem_map.mpr ⟨d,hd,owner_eq G he⟩

theorem dual_adj_symmetric {M : MapData} (G : IsDiskFullerene M h) (i j : Face M) :
    j ∈ dualRow G i ↔ i ∈ dualRow G j := by
  rw [mem_row_iff, mem_row_iff]
  constructor <;> rintro ⟨d,hd,he⟩ <;> exact ⟨d.swap,he,hd⟩

def IsBoundary {M : MapData} (G : IsDiskFullerene M h) (i : Face M) : Prop :=
  i ∈ dualRow G (apex M)

/-- Strict interior vertices of the dual disk, as distinct face indices of
the original cubic map. -/
noncomputable def diskInterior {M : MapData} (G : IsDiskFullerene M h) : List (Face M) :=
  (List.finRange M.faces.length).filter fun i =>
    !(apex M :: dualRow G (apex M)).contains i

private theorem partition_length {α} (p : α → Bool) (xs : List α) :
    (xs.filter p).length + (xs.filter (fun x => !(p x))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases hv : p a <;> simp [hv] <;> omega

private theorem complement_length {α} [BEq α] [LawfulBEq α] (xs ys : List α)
    (nx : xs.Nodup) (ny : ys.Nodup) (sub : ys ⊆ xs) :
    (xs.filter (fun x => !ys.contains x)).length + ys.length = xs.length := by
  let hit := xs.filter ys.contains
  have hit_nodup : hit.Nodup := nx.sublist List.filter_sublist
  have lr : hit ⊆ ys := fun _ h => by simpa using (List.mem_filter.mp h).2
  have rl : ys ⊆ hit := fun x h => List.mem_filter.mpr ⟨sub h,by simpa using h⟩
  have h1 := hit_nodup.length_le_of_subset lr
  have h2 := ny.length_le_of_subset rl
  have eq := partition_length ys.contains xs
  change hit.length + _ = _ at eq
  omega

private theorem face_count {M : MapData} (G : IsDiskFullerene M h) :
    M.faces.length = 1 + (h+6) + M.hexagons := by
  have e := (eulerCounts G).1
  have len (l : List Nat) (good : ∀ x ∈ l, x=5 ∨ x=6) : l.length = l.count 5 + l.count 6 := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have prev := ih (fun x hx => good _ (List.mem_cons_of_mem _ hx))
      rcases good a (by simp) with rfl|rfl <;> simp <;> omega
  have eq := len (M.inner.map List.length) (by
    intro x hx; obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
    exact G.polygons f hf)
  change (M.inner.map List.length).count 5 = _ at e
  simp [MapData.faces,MapData.hexagons] at *; omega

/-- Equations (1) and (2)'s dual-disk counts on the actual map. The
no-parallel-edge input is exactly what makes the h neighboring indices
distinct; all lengths are of lists constructed from the rotation system. -/
theorem dual_disk_counts {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h) (s : noRepeat M) :
    (dualRow G (apex M)).Nodup ∧ (dualRow G (apex M)).length = h ∧
      (diskInterior G).length = 6 + M.hexagons := by
  have boundary := row_nodup G s (apex M)
  have boundaryLen := row_length G (apex M)
  change _ = M.outer.length at boundaryLen
  rw [G.outerSize] at boundaryLen
  refine ⟨boundary,boundaryLen,?_⟩
  have nd : (apex M :: dualRow G (apex M)).Nodup := List.nodup_cons.mpr ⟨row_no_loop G hh _,boundary⟩
  have all := complement_length _ _ (List.nodup_finRange M.faces.length) nd
    (fun i _ => List.mem_finRange i)
  simp only [List.length_finRange,List.length_cons,boundaryLen] at all
  have n := face_count G
  change (diskInterior G).length + (h + 1) = M.faces.length at all
  exact Nat.add_right_cancel (all.trans (by omega) : (diskInterior G).length + (h+1) = (6 + M.hexagons) + (h+1))

/-- The actual set of interior faces, with no auxiliary simplicity input. -/
theorem interior_count {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h) :
    (diskInterior G).length = 6 + M.hexagons :=
  (dual_disk_counts G hh (noRepeatOnSphere G hh)).2.2

theorem inner_degree {M : MapData} (G : IsDiskFullerene M h) {i : Face M} (other : i ≠ apex M) :
    (dualRow G i).length = 5 ∨ (dualRow G i).length = 6 := by
  rw [row_length]
  obtain ⟨n,eq⟩ := Nat.exists_eq_succ_of_ne_zero (show i.val ≠ 0 from fun e => other (Fin.ext e))
  have bound : n < M.inner.length := by have := i.isLt; simp [MapData.faces,eq] at this; omega
  have e : M.faces[i.val] = M.inner[n] := by
    simp [MapData.faces,eq, List.getElem_cons_succ]
  rw [e]; exact G.polygons _ (List.getElem_mem bound)

private theorem corner_across {M : MapData} (G : IsDiskFullerene M h) {i : Face M}
    (a : incident M i (u,v)) (b : incident M i (v,w)) (turn : M.turn (u,v) = (v,w)) :
    owner G (w,v) ∈ dualRow G (owner G (v,u)) := by
  obtain ⟨z,_,t2,t3⟩ := cubic_corner G a turn
  have ina := reverse_owner G a
  have inb := reverse_owner G b
  have outb : incident M (owner G (w,v)) (v,z) := t2 ▸ incident_turn G inb
  obtain ⟨k,ik,_⟩ := dart_has_face G (dart_reverse G (incident_dart G outb))
  have ku : incident M k (v,u) := t3 ▸ incident_turn G ik
  have same : k = owner G (v,u) := face_indices_unique G ku ina
  exact (mem_row_iff ..).mpr ⟨(z,v),same ▸ ik, outb⟩

/-- Consecutive neighbors of any dual vertex are themselves adjacent: the
third edge at the intervening primal vertex separates these two faces. -/
theorem cyclic_link {M : MapData} (G : IsDiskFullerene M h) (i : Face M)
    {x y : Face M} (step : (x,y) ∈ sides (dualRow G i)) : y ∈ dualRow G x := by
  let ds := sides M.faces[i.val]
  obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp step
  rw [sides_size] at hn
  rw [side_at _ _ hn] at eq
  have hp : n < ds.length := by simpa [dualRow, ds] using hn
  let m := next ds.length n
  have hq : m < ds.length := next_bound hp
  have pair : (ds[n],ds[m]) ∈ sides ds := List.mem_iff_getElem.mpr
    ⟨n,by simpa [sides_size] using hp,side_at ds n hp⟩
  have ok := List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem i.isLt)
  have good := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 _ pair
  obtain ⟨u,v,ea⟩ : ∃ u v, ds[n] = (u,v) := ⟨_,_,rfl⟩
  obtain ⟨v',w,eb⟩ : ∃ v' w, ds[m] = (v',w) := ⟨_,_,rfl⟩
  have tt : M.turn (u,v) = (v',w) := by simpa [ea,eb] using good
  have eqv : v = v' := congrArg Prod.fst tt
  subst v'
  have ha : incident M i (u,v) := ea ▸ List.getElem_mem hp
  have hb : incident M i (v,w) := eb ▸ List.getElem_mem hq
  simp only [dualRow, List.length_map, List.getElem_map] at eq
  change (owner G ds[n].swap, owner G ds[m].swap) = _ at eq
  simp [ea, eb] at eq
  rcases eq with ⟨rfl,rfl⟩
  exact corner_across G ha hb tt

theorem boundary_cycle {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h) :
    (dualRow G (apex M)).Nodup ∧ (dualRow G (apex M)).length = h ∧
      ∀ x y, (x,y) ∈ sides (dualRow G (apex M)) → y ∈ dualRow G x :=
  ⟨row_nodup G (noRepeatOnSphere G hh) _, (dual_disk_counts G hh (noRepeatOnSphere G hh)).2.1,
    fun _ _ step => cyclic_link G _ step⟩

theorem mem_diskInterior {M : MapData} (G : IsDiskFullerene M h) (i : Face M) :
    i ∈ diskInterior G ↔ i ≠ apex M ∧ i ∉ dualRow G (apex M) := by
  simp [diskInterior,List.mem_finRange]

def HasChord {M : MapData} (G : IsDiskFullerene M h) : Prop :=
  let C := dualRow G (apex M)
  ∃ x ∈ C, ∃ y ∈ C, y ∈ dualRow G x ∧ (x,y) ∉ sides C ∧ (y,x) ∉ sides C

private def prev (n i : Nat) := if i=0 then n-1 else i-1

private theorem next_injective {n i j : Nat} (hi : i < n) (hj : j < n)
    (eq : next n i = next n j) : i = j := by
  unfold next at eq; split at eq <;> split at eq <;> omega

theorem cycle_at {α} {x : α} {C : List α} (nd : C.Nodup) (sz : 3 ≤ C.length)
    (vx : x ∈ C) :
    ∃ p ∈ C, ∃ q ∈ C, p ≠ q ∧ (p,x) ∈ sides C ∧ (x,q) ∈ sides C ∧
      ∀ y, (x,y) ∈ sides C ∨ (y,x) ∈ sides C → y = p ∨ y = q := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp vx
  let a := prev C.length i
  let b := next C.length i
  have ha : a < C.length := by unfold a prev; split <;> omega
  have hb : b < C.length := next_bound hi
  have rt : next C.length a = i := by
    unfold next a prev; split <;> split <;> omega
  have ne : a ≠ b := by
    unfold a b prev next; split <;> split <;> omega
  refine ⟨C[a],List.getElem_mem ha,C[b],List.getElem_mem hb, fun eq => ne (index_eq nd ha hb eq),?_,?_,?_⟩
  · exact List.mem_iff_getElem.mpr ⟨a,by simpa [sides_size] using ha, by rw [side_at C a ha]; simp [rt]⟩
  · exact List.mem_iff_getElem.mpr ⟨i,by simpa [sides_size] using hi,side_at C i hi⟩
  · intro y link
    rcases link with left | right
    · obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp left
      rw [sides_size] at hj
      rw [side_at C j hj] at eq
      have id := index_eq nd hj hi (Prod.mk.inj eq).1
      subst j; exact Or.inr (Prod.mk.inj eq).2.symm
    · obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp right
      rw [sides_size] at hj
      rw [side_at C j hj] at eq
      have id := index_eq nd (next_bound hj) hi (Prod.mk.inj eq).2
      have ja := next_injective hj ha (id.trans rt.symm)
      exact Or.inl ((Prod.mk.inj eq).1.symm.trans (by simp [ja]))

/-- Exact boundary fan count for every actual chordless dual disk (no
decomposition certificate). Every boundary vertex has two boundary neighbors,
the apex, and exactly its degree minus three strict interior neighbors. -/
theorem chordless_fan {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h)
    (noChord : ¬ HasChord G) (x : Face M) (hx : IsBoundary G x) :
    ((dualRow G x).filter (diskInterior G).contains).length + 3 = (dualRow G x).length := by
  let C := dualRow G (apex M)
  obtain ⟨nd,len,link⟩ := boundary_cycle G hh
  have z : 3 ≤ C.length := by change 3 ≤ (dualRow G (apex M)).length; omega
  obtain ⟨p,hp,q,hq,ne,px,xq,localSide⟩ := cycle_at nd z hx
  have napex := row_no_loop G hh (apex M)
  have ap : apex M ≠ p := fun e => napex (by simpa [e] using hp)
  have aq : apex M ≠ q := fun e => napex (by simpa [e] using hq)
  have trio : ([apex M, p, q] : List (Face M)).Nodup := by simp [ap,aq,ne]
  have sub : [apex M, p, q] ⊆ dualRow G x := by
    intro y hy
    simp at hy
    rcases hy with rfl | rfl | rfl
    · exact (dual_adj_symmetric G _ _).1 hx
    · exact (dual_adj_symmetric G _ _).1 (link _ _ px)
    · exact link _ _ xq
  have count := complement_length (dualRow G x) [apex M,p,q] (row_nodup G (noRepeatOnSphere G hh) x) trio sub
  have classif (y : Face M) (member : y ∈ dualRow G x) :
      y ∈ diskInterior G ↔ y ∉ [apex M, p,q] := by
    rw [mem_diskInterior]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨a,b⟩ (e|e|e)
      · exact a e
      · exact b (e ▸ hp)
      · exact b (e ▸ hq)
    · intro avoid
      refine ⟨fun e => avoid (Or.inl e), fun hy => ?_⟩
      have adj : (x,y) ∈ sides C ∨ (y,x) ∈ sides C := by
        by_cases f : (x,y) ∈ sides C
        · exact Or.inl f
        by_cases b : (y,x) ∈ sides C
        · exact Or.inr b
        exact False.elim (noChord ⟨x,hx,y,hy,member,f,b⟩)
      rcases localSide y adj with e|e
      · exact avoid (Or.inr (Or.inl e))
      · exact avoid (Or.inr (Or.inr e))
  have same : (dualRow G x).filter (diskInterior G).contains =
      (dualRow G x).filter (fun y => !([apex M,p,q] : List _).contains y) := by
    apply List.filter_congr
    intro y hy
    apply Bool.eq_iff_iff.mpr
    simpa using classif y hy
  simpa only [same, List.length_cons, List.length_nil] using count

end DiskFullerene.Dual
