import DiskFullerene.DualIncidence
import DiskFullerene.EdgeConnectivity
import DiskFullerene.Separation

/-! The same edge labels are used for the primal and the dual. Keep one
dart per edge by orienting from the smaller to the larger vertex label. -/
namespace DiskFullerene.Dual

def edges (M : MapData) : List Dart := M.darts.filter fun d => d.1 < d.2

abbrev Edge (M : MapData) := Fin (edges M).length
def endpoints {M} (e : Edge M) : Dart := (edges M)[e.val]

theorem ordered {M} (e : Edge M) : (endpoints e).1 < (endpoints e).2 := by
  have h := List.mem_filter.mp (List.getElem_mem (l := edges M) e.isLt)
  exact of_decide_eq_true h.2

theorem endpoints_mem {M} (e : Edge M) : endpoints e ∈ M.darts :=
  (List.mem_filter.mp (List.getElem_mem (l := edges M) e.isLt)).1

theorem dart_info {M : MapData} (G : IsDiskFullerene M h) {d : Dart} (hd : d ∈ M.darts) :
    d.1 < M.ord ∧ d.2 < M.ord ∧ d.1 ≠ d.2 := by
  exact dart_endpoints G hd

theorem table_euler {M : MapData} (G : IsDiskFullerene M h) :
    M.ord + M.faces.length = (edges M).length+2 := by
  let up : Dart → Bool := fun d => d.1 < d.2
  let down := M.darts.filter (fun d => !up d)
  have nd := dart_nodup G
  have p : ((edges M).map Prod.swap).Perm down := by
    apply (List.perm_ext_iff_of_nodup _ _).mpr
    · rintro ⟨a,b⟩
      constructor
      · intro mem
        obtain ⟨⟨x,y⟩,hxy,eq⟩ := List.mem_map.mp mem
        cases eq
        have ⟨hd,lt⟩ := List.mem_filter.mp hxy
        change decide (x < y) = true at lt
        apply List.mem_filter.mpr
        have hlt := of_decide_eq_true lt
        exact ⟨dart_reverse G hd,by simp [up]; omega⟩
      · intro mem
        obtain ⟨hd,hp⟩ := List.mem_filter.mp mem
        have diff := (dart_info G hd).2.2
        have hle : ¬ a < b := by simpa [up] using hp
        exact List.mem_map.mpr ⟨(b,a),List.mem_filter.mpr
          ⟨dart_reverse G hd,by simp; omega⟩,rfl⟩
    · exact List.pairwise_map.mpr ((List.filter_sublist.nodup nd).imp
        (fun hab he => hab (by simpa using congrArg (fun d : Dart => d.swap) he)))
    · exact List.filter_sublist.nodup nd
  have size := (List.filter_append_perm up M.darts).length_eq
  change ((edges M) ++ down).length = M.darts.length at size
  have n := p.length_eq
  simp only [List.length_map] at n
  simp only [List.length_append] at size
  have spherical := G.sphere
  omega

def primal {M : MapData} (G : IsDiskFullerene M h) (e : Edge M) :
    Fin M.ord × Fin M.ord :=
  let info := dart_info G (endpoints_mem e)
  (⟨(endpoints e).1, info.1⟩, ⟨(endpoints e).2, info.2.1⟩)

noncomputable def leftFace {M : MapData} (G : IsDiskFullerene M h)
    (d : Dart) (hd : d ∈ M.darts) : Face M := (dart_has_face G hd).choose

theorem left_incident {M : MapData} (G : IsDiskFullerene M h) {d} (hd : d ∈ M.darts) :
    incident M (leftFace G d hd) d := (dart_has_face G hd).choose_spec.1

noncomputable def dual {M : MapData} (G : IsDiskFullerene M h) (e : Edge M) : Face M × Face M :=
  let hd := endpoints_mem e
  (leftFace G (endpoints e) hd, leftFace G (endpoints e).swap (dart_reverse G hd))

theorem left_ne_right {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h) (e : Edge M) :
    (dual G e).1 ≠ (dual G e).2 :=
  opposite_faces_distinct G hh (left_incident G (endpoints_mem e))
    (left_incident G (dart_reverse G (endpoints_mem e)))

theorem repr_dart {M : MapData} (G : IsDiskFullerene M h) {d : Dart} (hd : d ∈ M.darts) :
    ∃ e : Edge M, endpoints e = d ∨ endpoints e = d.swap := by
  let choose (a : Dart) (mem : a ∈ edges M) : Edge M :=
    ⟨(edges M).idxOf a,List.idxOf_lt_length_iff.mpr mem⟩
  have spec (a : Dart) (mem) : endpoints (choose a mem) = a := List.getElem_idxOf _
  by_cases small : d.1 < d.2
  · have m : d ∈ edges M := List.mem_filter.mpr ⟨hd,decide_eq_true small⟩
    exact ⟨choose d m,Or.inl (spec d m)⟩
  · have info := (dart_info G hd).2.2
    have m : d.swap ∈ edges M := List.mem_filter.mpr ⟨dart_reverse G hd,by simp; omega⟩
    exact ⟨choose _ m,Or.inr (spec _ m)⟩

theorem repr_unique {M : MapData} (G : IsDiskFullerene M h) {i j : Edge M}
    (eq : endpoints i = endpoints j) : i=j := by
  have nd : (edges M).Nodup := List.filter_sublist.nodup (dart_nodup G)
  have h := congrArg (fun d => (edges M).idxOf d) eq
  change (edges M).idxOf ((edges M)[i.val]) = (edges M).idxOf ((edges M)[j.val]) at h
  exact Fin.ext (show i.val = j.val from
    (nd.idxOf_getElem i.val i.isLt).symm.trans (h.trans (nd.idxOf_getElem j.val j.isLt)))


theorem crossTable {M : MapData} (G : IsDiskFullerene M h) {e : Edge M} {i j : Face M}
    {d : Dart} (eq : endpoints e = d ∨ endpoints e = d.swap) (cross : Cross M d i j) :
    Separation.Across (dual G) e i j := by
  have l := left_incident G (endpoints_mem e)
  have r := left_incident G (dart_reverse G (endpoints_mem e))
  change incident M (dual G e).1 (endpoints e) at l
  change incident M (dual G e).2 (endpoints e).swap at r
  rcases eq with h|h <;> rw [h] at l r
  · rcases cross with ⟨a,b⟩|⟨a,b⟩
    · exact .inl (Prod.ext (face_indices_unique G l a) (face_indices_unique G r b))
    · exact .inr (Prod.ext (face_indices_unique G l a) (face_indices_unique G r b))
  · simp only [Prod.swap_swap] at r
    rcases cross with ⟨a,b⟩|⟨a,b⟩
    · exact .inr (Prod.ext (face_indices_unique G l b) (face_indices_unique G r a))
    · exact .inl (Prod.ext (face_indices_unique G l b) (face_indices_unique G r a))

theorem liftDual {M : MapData} (G : IsDiskFullerene M h) {D : Dart → Prop} {K : Edge M → Prop}
    (good : ∀ d e, endpoints e = d ∨ endpoints e = d.swap → D d → K e)
    {i j : Face M} (p : Separation.Walk (Step M D) i j) :
    Separation.Walk (Separation.Adj (dual G) K) i j := by
  induction p with
  | refl => exact .refl
  | step _ hop ih =>
    obtain ⟨d,hk,c⟩ := hop
    have present : d ∈ M.darts := by
      rcases c with ⟨a,_⟩ | ⟨a,_⟩ <;> exact incident_dart G a
    obtain ⟨e,eq⟩ := repr_dart G present
    exact ih.step ⟨e,good d e eq hk,crossTable G eq c⟩

private theorem flipWalk {E V} {ends : E → V × V} {K : E → Prop} {i j}
    (p : Separation.Walk (Separation.Adj ends K) i j) : Separation.Walk (Separation.Adj ends K) j i :=
  p.symm (fun _ _ ⟨e,h,a⟩ => ⟨e,h,a.symm⟩)

private theorem liftBypass {M : MapData} (G : IsDiskFullerene M h) {e : Edge M}
    (v : Fin M.ord) (p : Nat) (vp : v.val ≠ p)
    (boundary : endpoints e = (v.val,p) ∨ endpoints e = (p,v.val))
    (i j : Face M) (a : incident M i (v.val,p)) (b : incident M j (p,v.val)) :
    Separation.Walk (Separation.Adj (dual G) (fun t => t ≠ e ∧ Separation.incident (primal G) t v)) i j := by
  apply liftDual G _ (vertex_bypass G i j a b)
  intro d t orient hd
  change d.1 = v.val ∧ d.2 ≠ p at hd
  constructor
  · intro eq
    subst t
    rcases orient with ho|ho <;> rcases boundary with he|he <;> rw [he] at ho <;>
      cases d <;> simp [Prod.mk.injEq] at * <;> grind
  · rcases orient with ho|ho
    · exact .inl (Fin.ext ((congrArg Prod.fst ho).trans hd.1))
    · exact .inr (Fin.ext ((congrArg Prod.snd ho).trans hd.1))

theorem vertexBypassTable {M : MapData} (G : IsDiskFullerene M h) :
    Separation.FaceBypass (dual G) (primal G) := by
  intro v e hv
  have ord := ordered e
  have a := left_incident G (endpoints_mem e)
  have b := left_incident G (dart_reverse G (endpoints_mem e))
  rcases hv with rfl|rfl
  · exact liftBypass G (primal G e).1 (endpoints e).2 (by exact Nat.ne_of_lt ord)
      (Or.inl rfl) _ _ a b
  · exact flipWalk (liftBypass G (primal G e).2 (endpoints e).1 (Ne.symm (Nat.ne_of_lt ord))
      (Or.inr rfl) _ _ b a)

theorem primalResilient {M : MapData} (G : IsDiskFullerene M h)
    (a b : Edge M) (u v : Fin M.ord) :
    Separation.Walk (Separation.Adj (primal G) (fun d => ¬(d=a ∨ d=b))) u v := by
  let R := fun x y => M.adj x y ∧ ¬ IsEdge (endpoints a) x y ∧ ¬ IsEdge (endpoints b) x y
  have p : PathAvoiding R [] u.val v.val := twoEdgeConnected G.connectivity _ _
    (Nat.ne_of_lt (ordered a)) (Nat.ne_of_lt (ordered b)) _ _ u.isLt v.isLt
  suffices transfer : ∀ {z} (walk : PathAvoiding R [] u.val z) (hz : z<M.ord),
      Separation.Walk (Separation.Adj (primal G) (fun d => ¬(d=a ∨ d=b))) u ⟨z,hz⟩ from transfer p v.isLt
  intro z walk
  induction walk with
  | here => intro _; exact .refl
  | @step x y _ e _ ih =>
    intro hy
    obtain ⟨adj,nda,ndb⟩ := e
    have dart := dart_iff.mpr adj
    have hx := (dart_endpoints G dart).1
    obtain ⟨k,eq⟩ := repr_dart G dart
    apply (ih hx).step
    refine ⟨k,?_,?_⟩
    · rintro (rfl|rfl)
      · exact nda eq
      · exact ndb eq
    · rcases eq with he|he
      · exact .inl (Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he)))
      · exact .inr (Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he)))

/-- Distinct primal edges cannot have the same two faces. This is the
simple-dual step needed to count distinct neighbours of the outside face. -/
theorem noRepeatOnSphere {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h) : noRepeat M := by
  intro i j a b ia ja ib jb
  obtain ⟨u,hu⟩ := repr_dart G (incident_dart G ia)
  obtain ⟨v,hv⟩ := repr_dart G (incident_dart G ib)
  have au := crossTable G hu (Or.inl ⟨ia,ja⟩ : Cross M a i j)
  have av := crossTable G hv (Or.inl ⟨ib,jb⟩ : Cross M b i j)
  have uv : u=v := by
    by_cases eq : u=v
    · exact eq
    · exfalso
      apply Separation.parallel_of_sphere (by have := G.connectivity.1; omega)
        (show 0<M.faces.length by simp [MapData.faces]) (table_euler G)
        (fun x y => liftDual G (fun _ _ _ _ => trivial) (dual_connected G hh x y))
        (vertexBypassTable G) eq _ (primalResilient G u v)
      intro z
      rcases au with h|h <;> rcases av with k|k <;> simp [Separation.incident,h,k,or_comm]
  subst v
  rcases hu with e|e <;> rcases hv with f|f <;> rw [e] at f
  · exact f
  · exact False.elim ((opposite_faces_distinct G hh ia (f ▸ ib)) rfl)
  · rw [← f] at ib
    exact False.elim ((opposite_faces_distinct G hh ia ib) rfl)
  · simpa using congrArg (fun t : Dart => t.swap) f

end DiskFullerene.Dual
