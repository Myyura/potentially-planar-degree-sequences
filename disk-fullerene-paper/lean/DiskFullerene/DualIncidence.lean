import DiskFullerene.Map
import DiskFullerene.Separation

namespace DiskFullerene

namespace Dual

abbrev Face (M : MapData) := Fin M.faces.length

def incident (M : MapData) (i : Face M) (d : Dart) : Prop :=
  d ∈ sides M.faces[i.val]

private theorem rowOK {M : MapData} (G : IsDiskFullerene M h)
    (m : (r,u) ∈ M.rows.zipIdx) :
    r.Nodup ∧ ∀ v ∈ r, v < M.ord ∧ v ≠ u ∧ M.adj v u := by
  have ok := List.all_eq_true.mp G.simpleRotation (r,u) m
  simpa [List.all_eq_true, Bool.and_assoc, MapData.adj] using ok

theorem dart_nodup {M : MapData} (G : IsDiskFullerene M h) : M.darts.Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · rintro ⟨r,u⟩ m
    have rows := (rowOK G m).1
    exact List.pairwise_map.mpr (rows.imp (fun ne he => ne (congrArg Prod.snd he)))
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt x hx y hy
    simp only [List.getElem_zipIdx, Nat.zero_add, List.mem_map] at hx hy
    rcases hx with ⟨_,_,rfl⟩; rcases hy with ⟨_,_,rfl⟩
    exact fun he => (Nat.ne_of_lt lt) (congrArg Prod.fst he)

theorem dart_iff {M : MapData} {u v : Nat} :
    (u,v) ∈ M.darts ↔ M.adj u v := by
  unfold MapData.darts MapData.adj
  constructor
  · intro md
    obtain ⟨⟨r,i⟩, hr, hd⟩ := List.mem_flatMap.mp md
    obtain ⟨w, mw, e⟩ := List.mem_map.mp hd
    cases e
    simp [List.mk_mem_zipIdx_iff_getElem?.mp hr, mw]
  · intro hv
    cases eq : M.rows[u]? with
    | none => simp [eq] at hv
    | some r =>
      exact List.mem_flatMap.mpr ⟨(r,u),List.mk_mem_zipIdx_iff_getElem?.mpr eq,
        List.mem_map.mpr ⟨v, by simpa [eq] using hv, rfl⟩⟩

theorem dart_reverse {M : MapData} (G : IsDiskFullerene M h)
    (e : (u,v) ∈ M.darts) : (v,u) ∈ M.darts := by
  obtain ⟨⟨r,i⟩, hr, hd⟩ := List.mem_flatMap.mp e
  obtain ⟨w,mw,eq⟩ := List.mem_map.mp hd
  cases eq
  exact dart_iff.mpr ((rowOK G hr).2 _ mw).2.2

theorem face_indices_unique {M : MapData} (G : IsDiskFullerene M h)
    {i j : Face M} (hd : incident M i d) (he : incident M j d) : i = j := by
  have nodup := G.coverage.nodup_iff.mpr (dart_nodup G)
  have cross := (List.pairwise_flatMap.mp nodup).2
  have p := List.pairwise_iff_getElem.mp cross
  apply Fin.ext
  by_cases h1 : i.val < j.val
  · exact False.elim ((p _ _ i.isLt j.isLt h1 _ hd _ he) rfl)
  by_cases h2 : j.val < i.val
  · exact False.elim ((p _ _ j.isLt i.isLt h2 _ he _ hd) rfl)
  omega

theorem dart_has_face {M : MapData} (G : IsDiskFullerene M h)
    (e : d ∈ M.darts) : ∃ i : Face M, incident M i d ∧ ∀ j, incident M j d → j = i := by
  obtain ⟨f,hf,hd⟩ := List.mem_flatMap.mp (G.coverage.mem_iff.mpr e)
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hf
  exact ⟨⟨i,hi⟩,hd,fun _ hj => face_indices_unique G hj hd⟩

def next (n i : Nat) := if i+1 < n then i+1 else 0

theorem next_bound (hi : i < n) : next n i < n := by unfold next; split <;> omega

theorem sides_size {α} (f : List α) : (sides f).length = f.length := by cases f <;> simp [sides]

theorem side_at {α} (f : List α) (i : Nat) (hi : i < f.length) :
    (sides f)[i]'(by simpa [sides_size] using hi) = (f[i], f[next f.length i]'(next_bound hi)) := by
  cases f with
  | nil => simp at hi
  | cons a l =>
    simp only [sides, List.getElem_zip, Prod.mk.injEq, true_and, List.length_cons]
    by_cases c : i < l.length
    · rw [List.getElem_append_left c]
      have eq : next (l.length+1) i = i+1 := by simp [next,c]
      simp [eq]
    · have eqi : i = l.length := by simp at hi; omega
      simp [eqi, next, List.getElem_append_right]

theorem index_eq {α} {f : List α} (unique : f.Nodup) {i j}
    (hi : i < f.length) (hj : j < f.length) (heq : f[i] = f[j]) : i = j := by
  have p := List.pairwise_iff_getElem.mp unique
  by_cases lt : i < j
  · exact False.elim ((p _ _ hi hj lt) heq)
  by_cases gt : j < i
  · exact False.elim ((p _ _ hj hi gt) heq.symm)
  omega

theorem face_has_no_reverse {α} {f : List α} (nd : f.Nodup) (size : 3 ≤ f.length)
    {u v : α} (a : (u,v) ∈ sides f) (b : (v,u) ∈ sides f) : False := by
  obtain ⟨i, hi, pi⟩ := List.mem_iff_getElem.mp a
  obtain ⟨j, hj, pj⟩ := List.mem_iff_getElem.mp b
  rw [sides_size] at hi hj
  rw [side_at f i hi] at pi
  rw [side_at f j hj] at pj
  have e1 := Prod.mk.inj pi
  have e2 := Prod.mk.inj pj
  have ij := index_eq nd hi (next_bound hj) (e1.1.trans e2.2.symm)
  have ji := index_eq nd hj (next_bound hi) (e2.1.trans e1.2.symm)
  simp only [next] at ij ji
  split at ij <;> split at ji <;> omega

theorem opposite_faces_distinct {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h)
    {i j : Face M} (a : incident M i (u,v)) (b : incident M j (v,u)) : i ≠ j := by
  intro eq
  subst j
  have hm := List.getElem_mem (l := M.faces) i.isLt
  have ok := List.all_eq_true.mp G.faceOrbits _ hm
  have nd : M.faces[i.val].Nodup := by simpa [MapData.faceOK] using (Bool.and_eq_true_iff.mp ok).1
  have sz : 3 ≤ M.faces[i.val].length := by
    rcases List.mem_cons.mp hm with e | m
    · rw [e,G.outerSize]; exact hh
    · have := G.polygons _ m; omega
  exact face_has_no_reverse nd sz a b

theorem incident_dart {M : MapData} {i : Face M} (G : IsDiskFullerene M h)
    (e : incident M i d) : d ∈ M.darts :=
  G.coverage.mem_iff.mp (List.mem_flatMap.mpr ⟨_,List.getElem_mem i.isLt,e⟩)

theorem incident_turn {M : MapData} {i : Face M} (G : IsDiskFullerene M h)
    (e : incident M i d) : incident M i (M.turn d) := by
  let L := sides M.faces[i.val]
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp (show d ∈ L from e)
  let n := next L.length k
  have hn : n < L.length := next_bound hk
  have m : (d, L[n]) ∈ sides L := List.mem_iff_getElem.mpr
    ⟨k,by simpa [sides_size] using hk, by rw [side_at L k hk, he]⟩
  have ok := List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem i.isLt)
  have eq := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 _ m
  have eq' : M.turn d = L[n] := by simpa using eq
  rw [eq']
  exact List.getElem_mem hn

theorem dart_endpoints {M : MapData} (G : IsDiskFullerene M h) (m : (u,v) ∈ M.darts) :
    u < M.ord ∧ v < M.ord ∧ u ≠ v := by
  obtain ⟨⟨r,i⟩, hr, hd⟩ := List.mem_flatMap.mp m
  obtain ⟨w,mw,eq⟩ := List.mem_map.mp hd
  cases eq
  have h := (rowOK G hr).2 _ mw
  exact ⟨(List.mem_zipIdx' hr).1, h.1, Ne.symm h.2.1⟩

def Cross (M : MapData) (d : Dart) (i j : Face M) : Prop :=
  (incident M i d ∧ incident M j d.swap) ∨ (incident M j d ∧ incident M i d.swap)

def Step (M : MapData) (keep : Dart → Prop) (i j : Face M) : Prop :=
  ∃ d, keep d ∧ Cross M d i j

private theorem three_turns {M : MapData} (eq : M.rows[v]?.getD [] = [a,b,c])
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    M.turn (a,v) = (v,b) ∧ M.turn (b,v) = (v,c) ∧ M.turn (c,v) = (v,a) := by
  simp [MapData.turn, eq, List.idxOf_cons, ab, ac, bc]

theorem rooted_rotation {M : MapData} (G : IsDiskFullerene M h) (vp : M.adj v p) :
    ∃ q r, q ≠ p ∧ r ≠ p ∧
      (∀ w, M.adj v w ↔ w = p ∨ w = q ∨ w = r) ∧
      M.turn (p,v) = (v,q) ∧ M.turn (q,v) = (v,r) ∧ M.turn (r,v) = (v,p) := by
  have hpos := (dart_endpoints G (dart_iff.mpr vp)).1
  let row := M.rows[v]'hpos
  have eqr : M.rows[v]?.getD [] = row := by rw [List.getElem?_eq_getElem hpos]; rfl
  have n := G.cubic row (List.getElem_mem hpos)
  have nd := (rowOK G (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hpos))).1
  change row.Nodup at nd
  obtain ⟨a,b,c,he⟩ : ∃ a b c, row = [a,b,c] :=
    ⟨_, _, _, List.eq_getElem_of_length_eq_three row n⟩
  rw [he] at nd eqr
  simp at nd
  have ab := nd.1.1; have ac := nd.1.2; have bc := nd.2
  obtain ⟨t1,t2,t3⟩ := three_turns eqr ab ac bc
  change p ∈ M.rows[v]?.getD [] at vp
  simp [eqr] at vp
  rcases vp with rfl | rfl | rfl
  · exact ⟨_,_, Ne.symm ab, Ne.symm ac, by simp [MapData.adj,eqr], t1,t2,t3⟩
  · exact ⟨_,_, Ne.symm bc, ab,
      by intro w; simp [MapData.adj,eqr]; grind, t2,t3,t1⟩
  · exact ⟨_,_, ac, bc,
      by intro w; simp [MapData.adj,eqr]; grind, t3,t1,t2⟩

/-- The third distinct neighbor and the next two turns close a cubic vertex
whenever the first turn is prescribed. -/
theorem cubic_corner {M : MapData} {i : Face M} (G : IsDiskFullerene M h) (d : incident M i (u,v))
    (first : M.turn (u,v) = (v,w)) :
    ∃ z, z ≠ u ∧ M.turn (w,v) = (v,z) ∧ M.turn (z,v) = (v,u) := by
  obtain ⟨q,r,_,ru,_,t1,t2,t3⟩ := rooted_rotation G
    (dart_iff.mp (dart_reverse G (incident_dart G d)))
  have eq : q = w := congrArg Prod.snd (t1.symm.trans first)
  exact ⟨r,ru,eq ▸ t2,t3⟩

/-- Across a primal edge based at v, the two faces can also be joined
through the other two edges at v. Each chosen dart is oriented away from v. -/
theorem vertex_bypass {M : MapData} (G : IsDiskFullerene M h) (i j : Face M)
    (src : incident M i (v,p)) (dst : incident M j (p,v)) :
    Separation.Walk (Step M (fun d => d.1 = v ∧ d.2 ≠ p)) i j := by
  obtain ⟨q,r,qp,rp,row,t1,t2,t3⟩ := rooted_rotation G (dart_iff.mp (incident_dart G src))
  obtain ⟨k,ek,_⟩ := dart_has_face G (dart_reverse G (dart_iff.mpr ((row q).2 (by simp))))
  have mid : incident M k (v,r) := t2 ▸ incident_turn G ek
  have first : incident M i (r,v) := by
    obtain ⟨l,el,_⟩ := dart_has_face G (dart_reverse G (dart_iff.mpr ((row r).2 (by simp))))
    have eq : l=i := face_indices_unique G (t3 ▸ incident_turn G el) src
    exact eq ▸ el
  have last : incident M j (v,q) := t1 ▸ incident_turn G dst
  exact (Separation.Walk.step .refl ⟨(v,r),⟨rfl,rp⟩,Or.inr ⟨mid,first⟩⟩).step
    ⟨(v,q),⟨rfl,qp⟩,Or.inr ⟨last,ek⟩⟩

theorem around_vertex {M : MapData} (G : IsDiskFullerene M h) {i j : Face M}
    (start : incident M i (v,p)) (finish : incident M j (v,s)) :
    Separation.Walk (Step M (fun _ => True)) i j := by
  have vp := dart_iff.mp (incident_dart G start)
  obtain ⟨q,r,_,_,row,t1,t2,_⟩ := rooted_rotation G vp
  obtain ⟨k,ik,_⟩ := dart_has_face G (dart_reverse G (dart_iff.mpr vp))
  have via : Separation.Walk (Step M (fun _ => True)) i k :=
    .step .refl ⟨(v,p),trivial,Or.inl ⟨start,ik⟩⟩
  have kq : incident M k (v,q) := t1 ▸ incident_turn G ik
  rcases (row s).1 (dart_iff.mp (incident_dart G finish)) with eq | eq | eq
  · subst s
    have e := face_indices_unique G start finish
    exact e ▸ Separation.Walk.refl
  · subst s
    have e := face_indices_unique G kq finish
    exact e ▸ via
  · subst s
    obtain ⟨l,ill,_⟩ := dart_has_face G (dart_reverse G (incident_dart G kq))
    have lr : incident M l (v,r) := t2 ▸ incident_turn G ill
    have eql := face_indices_unique G lr finish
    exact eql ▸ (via.step ⟨(v,q),trivial,Or.inl ⟨kq,ill⟩⟩)

private theorem along_primal {M : MapData} (G : IsDiskFullerene M h)
    (P : PathAvoiding M.adj [] a b) {i j : Face M} (start : incident M i (a,p))
    (finish : incident M j (b,q)) : Separation.Walk (Step M (fun _ => True)) i j := by
  induction P generalizing j q with
  | here => exact around_vertex G start finish
  | @step v w path vw _ ih =>
    obtain ⟨k,ek,_⟩ := dart_has_face G (dart_iff.mpr vw)
    have half := ih ek
    have turn := incident_turn G ek
    exact half.trans (around_vertex G turn finish)

theorem face_dart {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h) (i : Face M) :
    ∃ u v, incident M i (u,v) := by
  have hf := List.getElem_mem (l := M.faces) i.isLt
  have sz : 0 < M.faces[i.val].length := by
    rcases List.mem_cons.mp hf with eq | hin
    · rw [eq,G.outerSize]; omega
    · have := G.polygons _ hin; omega
  let d := (sides M.faces[i.val])[0]'(by simpa [sides_size] using sz)
  exact ⟨d.1, d.2, List.getElem_mem _⟩

/-- Every two actual face indices are joined across primal edges, using
only connectedness of the primal graph and its cyclic three-neighbor rows. -/
theorem dual_connected {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h) (i j : Face M) :
    Separation.Walk (Step M (fun _ => True)) i j := by
  obtain ⟨a,p,ha⟩ := face_dart G hh i
  obtain ⟨b,q,hb⟩ := face_dart G hh j
  apply along_primal G (start := ha) (finish := hb)
  exact G.connectivity.2 [] (by decide) a b
    (dart_endpoints G (incident_dart G ha)).1 (dart_endpoints G (incident_dart G hb)).1
    (by simp) (by simp)

/-- Two fixed faces share at most one oriented side. -/
def noRepeat (M : MapData) : Prop :=
  ∀ (i j : Face M) (a b : Dart), incident M i a → incident M j a.swap →
    incident M i b → incident M j b.swap → a = b

end Dual
end DiskFullerene
