import DiskFullerene.DualDisk
namespace DiskFullerene.Dual

/-- Across the incoming and outgoing sides of a face, the opposite faces
are consecutive in the dual rotation. -/
theorem across_turn {M : MapData} (G : IsDiskFullerene M h) {i : Face M} {d : Dart}
    (inc : incident M i d) :
    (owner G d.swap, owner G (M.turn d).swap) ∈ sides (dualRow G i) := by
  let ds := sides M.faces[i.val]
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp (show d ∈ ds from inc)
  let m := next ds.length k
  have hm : m < ds.length := next_bound hk
  have pair : (d,ds[m]) ∈ sides ds := List.mem_iff_getElem.mpr
    ⟨k, by simpa [sides_size] using hk, by rw [side_at ds k hk,he]⟩
  have ok := List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem i.isLt)
  have tg := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 _ pair
  have tt : M.turn d = ds[m] := by simpa using tg
  have hk' : k < (dualRow G i).length := by simpa [dualRow,ds] using hk
  apply List.mem_iff_getElem.mpr
  refine ⟨k,by simpa [sides_size] using hk',?_⟩
  rw [side_at _ _ hk']
  simp only [dualRow,List.length_map,List.getElem_map]
  change (owner G ds[k].swap,owner G ds[m].swap) = _
  simp [he,tt]

theorem turn_triangle {M : MapData} (G : IsDiskFullerene M h) {i : Face M}
    {x y : Face M} (step : (x,y) ∈ sides (dualRow G i)) :
    (y,i) ∈ sides (dualRow G x) ∧ (i,x) ∈ sides (dualRow G y) := by
  let ds := sides M.faces[i.val]
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp step
  rw [sides_size] at hk
  rw [side_at _ _ hk] at eq
  have hp : k < ds.length := by simpa [dualRow,ds] using hk
  let m := next ds.length k
  have hq : m < ds.length := next_bound hp
  have pair : (ds[k],ds[m]) ∈ sides ds := List.mem_iff_getElem.mpr
    ⟨k,by simpa [sides_size] using hp,side_at ds k hp⟩
  have ok := List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem i.isLt)
  have good := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 _ pair
  obtain ⟨u,v,ea⟩ : ∃ u v, ds[k] = (u,v) := ⟨_,_,rfl⟩
  obtain ⟨v',w,eb⟩ : ∃ v' w, ds[m] = (v',w) := ⟨_,_,rfl⟩
  have tt : M.turn (u,v) = (v',w) := by simpa [ea,eb] using good
  have eqv : v = v' := congrArg Prod.fst tt
  subst v'
  have ha : incident M i (u,v) := ea ▸ List.getElem_mem hp
  have hb : incident M i (v,w) := eb ▸ List.getElem_mem hq
  simp only [dualRow,List.length_map,List.getElem_map] at eq
  change (owner G ds[k].swap,owner G ds[m].swap) = _ at eq
  simp [ea,eb] at eq
  rcases eq with ⟨rfl,rfl⟩
  obtain ⟨z,_,t2,t3⟩ := cubic_corner G ha tt
  have ina := reverse_owner G ha
  have inb := reverse_owner G hb
  have outb : incident M (owner G (w,v)) (v,z) := t2 ▸ incident_turn G inb
  obtain ⟨l,il,_⟩ := dart_has_face G (dart_reverse G (incident_dart G outb))
  have lu : incident M l (v,u) := t3 ▸ incident_turn G il
  have same : l = owner G (v,u) := face_indices_unique G lu ina
  have za : incident M (owner G (v,u)) (z,v) := same ▸ il
  have h1 := across_turn G za
  have h2 := across_turn G inb
  change (owner G (z,v).swap,owner G (M.turn (z,v)).swap) ∈ _ at h1
  change (owner G (w,v).swap,owner G (M.turn (w,v)).swap) ∈ _ at h2
  simpa [t2,t3, owner_eq G ha, owner_eq G hb, owner_eq G outb,owner_eq G za] using And.intro h1 h2

def OnCycle {α} (C : List α) (x y : α) : Prop := (x,y) ∈ sides C ∨ (y,x) ∈ sides C

theorem OnCycle.symm {α} {C : List α} {x y : α} (e : OnCycle C x y) : OnCycle C y x := Or.symm e

private theorem closure {α} {C S : List α} (a : α) (seed : a ∈ C) (start : a ∈ S)
    (closed : ∀ u ∈ S, ∀ w, (u,w) ∈ sides C → w ∈ S) : C ⊆ S := by
  have move {k} (hk : k < C.length) (m : C[k] ∈ S) : C[next C.length k]'(next_bound hk) ∈ S :=
    closed _ m _ (List.mem_iff_getElem.mpr ⟨k,by simpa [sides_size] using hk,side_at C k hk⟩)
  have ascend {j k} (lo : k ≤ j) (hi : j < C.length) (h : C[k]'(by omega) ∈ S) : C[j] ∈ S := by
    induction j with
    | zero =>
      have hk : k = 0 := by omega
      simpa [hk] using h
    | succ j ih =>
      by_cases eq : k = j+1
      · subst k; exact h
      · have h0 := ih (by omega) (by omega)
        have h1 := move (k := j) (by omega) (h0 h)
        simpa [next,hi] using h1
  obtain ⟨k,hk,ek⟩ := List.mem_iff_getElem.mp seed
  have last := ascend (j := C.length-1) (by omega) (by omega) (ek ▸ start : C[k] ∈ S)
  have zero' := move (k := C.length-1) (by omega) last
  have z : next C.length (C.length-1) = 0 := by unfold next; split <;> omega
  simp only [z] at zero'
  intro u hu
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hu
  exact ascend (k := 0) (by omega) hj zero'

/-- A simple cyclic row containing the four sides of a quadrilateral can
have no further vertices. This is purely a statement about cyclic words. -/
theorem quadrilateral {α} {C : List α} (nd : C.Nodup) (sz : 3 ≤ C.length)
    {a b c d : α} (ac : a ≠ c) (bd : b ≠ d)
    (ab : OnCycle C a b) (bc : OnCycle C b c) (cd : OnCycle C c d) (da : OnCycle C d a)
    (aC : a ∈ C) : C.length ≤ 4 := by
  let S := [a,b,c,d]
  have closedAt (x y z : α) (hx : x ∈ C) (hy : y ∈ S) (hz : z ∈ S)
      (ne : y ≠ z) (xy : OnCycle C x y) (xz : OnCycle C x z) :
      ∀ w, (x,w) ∈ sides C → w ∈ S := by
    obtain ⟨p,_,q,_,pq,_,_,only⟩ := cycle_at nd sz hx
    have ey := only _ xy; have ez := only _ xz
    intro w hw
    have ew := only _ (Or.inl hw)
    grind
  have endpoint {x y : α} (link : OnCycle C x y) : x ∈ C := by
    rcases link with l | l
    all_goals obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp l; rw [sides_size] at hj; rw [side_at C j hj] at e
    · exact (Prod.mk.inj e).1 ▸ List.getElem_mem hj
    · exact (Prod.mk.inj e).2 ▸ List.getElem_mem (next_bound hj)
  have sub := closure a aC (S := S) (by simp [S]) (by
    intro u hu
    simp [S] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact closedAt _ _ _ aC (by simp [S]) (by simp [S]) bd ab da.symm
    · exact closedAt _ _ _ (endpoint bc) (by simp [S]) (by simp [S]) ac ab.symm bc
    · exact closedAt _ _ _ (endpoint cd) (by simp [S]) (by simp [S]) bd bc.symm cd
    · exact closedAt _ _ _ (endpoint da) (by simp [S]) (by simp [S]) ac da cd.symm)
  exact nd.length_le_of_subset sub

private theorem opposite_corner {M : MapData} (G : IsDiskFullerene M h) {i x y : Face M}
    (edge : OnCycle (dualRow G i) x y) : OnCycle (dualRow G x) i y := by
  rcases edge with xy | yx
  · exact Or.inr (turn_triangle G xy).1
  · exact Or.inl (turn_triangle G yx).2

/-- A run of three boundary neighbors in an interior link would close a
four-cycle in the middle vertex's link, whose actual length is five or six. -/
theorem no_three_on_boundary {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h)
    (noChord : ¬ HasChord G) {u a b c : Face M} (hu : u ∈ diskInterior G)
    (aC : IsBoundary G a) (bC : IsBoundary G b) (cC : IsBoundary G c)
    (ne : a ≠ c) (one : (a,b) ∈ sides (dualRow G u)) (two : (b,c) ∈ sides (dualRow G u)) : False := by
  have onC {x y : Face M} (xc : IsBoundary G x) (yc : IsBoundary G y) (link : y ∈ dualRow G x) :
      OnCycle (dualRow G (apex M)) x y := by
    by_cases f : (x,y) ∈ sides (dualRow G (apex M))
    · exact Or.inl f
    by_cases back : (y,x) ∈ sides (dualRow G (apex M))
    · exact Or.inr back
    exact False.elim (noChord ⟨x,xc,y,yc,link,f,back⟩)
  have edge1 := onC aC bC (cyclic_link G u one)
  have edge2 := onC bC cC (cyclic_link G u two)
  have t1 := opposite_corner G edge1.symm
  have t2 := opposite_corner G edge2
  have s1 := opposite_corner G (show OnCycle (dualRow G u) b a from Or.inr one)
  have s2 := opposite_corner G (show OnCycle (dualRow G u) b c from Or.inl two)
  have bu : apex M ≠ u := Ne.symm ((mem_diskInterior G u).1 hu).1
  have nb : b ≠ apex M := fun e => row_no_loop G hh _ (by simpa [e,IsBoundary] using bC)
  have deg := inner_degree G nb
  have four := quadrilateral (row_nodup G (noRepeatOnSphere G hh) b) (by omega)
    bu ne t1 s1.symm s2 t2.symm ((dual_adj_symmetric G _ _).1 bC)
  omega

private theorem small_indices {n : Nat} (hn : n=5 ∨ n=6) :
    ∀ d : Fin n, ∃ a b c : Fin n,
      next n a.val = b.val ∧ next n b.val = c.val ∧ a ≠ c ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d := by
  rcases hn with rfl|rfl <;> decide

private theorem any_two_eq {α} {a b : α} {xs : List α} (len : xs.length ≤ 1) (h : a ∈ xs) (k : b ∈ xs) :
    a = b := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
    have e : xs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
    subst xs; simpa using (List.mem_singleton.mp h).trans (List.mem_singleton.mp k).symm

private theorem three_of_sparse {α} (xs : List α) (p : α → Bool) (nd : xs.Nodup)
    (size : xs.length = 5 ∨ xs.length = 6) (small : (xs.filter p).length ≤ 1) :
    ∃ a b c, a ∈ xs ∧ b ∈ xs ∧ c ∈ xs ∧ a ≠ c ∧ p a = false ∧ p b = false ∧ p c = false ∧
      (a,b) ∈ sides xs ∧ (b,c) ∈ sides xs := by
  obtain ⟨d, unique⟩ : ∃ d : Fin xs.length, ∀ k : Fin xs.length, p xs[k.val] = true → k = d := by
    by_cases existsBad : ∃ j : Fin xs.length, p xs[j.val] = true
    · obtain ⟨j,hj⟩ := existsBad
      refine ⟨j,fun k kh => Fin.ext (index_eq nd k.isLt j.isLt ?_)⟩
      exact any_two_eq small (List.mem_filter.mpr ⟨List.getElem_mem _,kh⟩)
        (List.mem_filter.mpr ⟨List.getElem_mem _,hj⟩)
    · exact ⟨⟨0,by omega⟩,fun k hk => False.elim (existsBad ⟨k,hk⟩)⟩
  obtain ⟨i,j,k,ij,jk,ik,id,jd,kd⟩ := small_indices size d
  have good (x : Fin xs.length) (ne : x ≠ d) : p xs[x.val] = false := by
    exact Bool.eq_false_iff.mpr (fun h => ne (unique x h))
  have adj (x y : Fin xs.length) (he : next xs.length x.val = y.val) :
      (xs[x.val],xs[y.val]) ∈ sides xs := by
    exact List.mem_iff_getElem.mpr ⟨x.val,by simp [sides_size],
      by rw [side_at xs x.val x.isLt]; simp [he]⟩
  exact ⟨_,_,_,List.getElem_mem i.isLt,List.getElem_mem j.isLt,List.getElem_mem k.isLt,
    fun he => ik (Fin.ext (index_eq nd i.isLt k.isLt he)),good i id,good j jd,good k kd,
    adj i j ij, adj j k jk⟩

/-- Minimum degree two of the interior graph induced by an actual
chordless dual disk. -/
theorem interior_min_two {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h)
    (noChord : ¬ HasChord G) {u : Face M} (hu : u ∈ diskInterior G) :
    2 ≤ ((dualRow G u).filter (diskInterior G).contains).length := by
  by_cases small : ((dualRow G u).filter (diskInterior G).contains).length ≤ 1
  · have sep := (mem_diskInterior G u).1 hu
    obtain ⟨a,b,c,am,bm,cm,ne,ha,hb,hc,ab,bc⟩ :=
      three_of_sparse _ _ (row_nodup G (noRepeatOnSphere G hh) u) (inner_degree G sep.1) small
    have outer (v : Face M) (m : v ∈ dualRow G u) (hv : (diskInterior G).contains v = false) :
        IsBoundary G v := by
      by_cases eq : v = apex M
      · subst v; exact False.elim (sep.2 ((dual_adj_symmetric G _ _).1 m))
      by_cases rim : IsBoundary G v
      · exact rim
      have interior := (mem_diskInterior G v).2 ⟨eq,rim⟩
      simp [interior] at hv
    exact False.elim (no_three_on_boundary G hh noChord hu (outer _ am ha) (outer _ bm hb)
      (outer _ cm hc) ne ab bc)
  · omega

end DiskFullerene.Dual
