import DiskFullerene.DualIso
import DiskFullerene.EndSix
import DiskFullerene.TerminalRuns

namespace DiskFullerene.Dual
open EndSix EndLabels Separation

private theorem share_edge {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u : Fin M.ord} {a b : Face M}
    (au : a∈triangle u) (bu : b∈triangle u) (ne : a≠b) : b∈dualRow G a := by
  obtain ⟨e,hit,_⟩ := common_edge_at G hh ne au bu
  have base : (dual G e).2 ∈ dualRow G (dual G e).1 := (mem_row_iff _ _ _).mpr
    ⟨endpoints e,left_incident G (endpoints_mem e),left_incident G (dart_reverse G (endpoints_mem e))⟩
  rcases hit with eq|eq <;> rw [eq] at base
  · exact base
  · exact (dual_adj_symmetric G ..).mp base

private theorem path_last {E gone a b} (P : PathAvoiding E gone a b) : b∉gone := by
  cases P with | here h => exact h | step _ _ h => exact h

/-- Deleting the three vertices of a dual face leaves a connected graph.
A primal path avoiding its cubic vertex lifts across surviving incident
faces. Two adjacent vertices of this path cannot share only deleted faces,
as the common dual edge would then have three distinct primal endpoints. -/
theorem facial_connected {M} (G : IsDiskFullerene M h) (hh : 3≤h) (t : Fin M.ord) :
    ∀ a∉triangle t, ∀ b∉triangle t, OutsideWalk G (triangle t) a b := by
  let K := triangle t
  have through (v : Fin M.ord) {a b : Face M} (av : a∈triangle v) (bv : b∈triangle v)
      (na : a∉K) (nb : b∉K) : OutsideWalk G K a b := by
    by_cases same : a=b
    · subst b; exact .refl
    · exact .step .refl ⟨na,nb,share_edge G hh av bv same⟩
  have shared {u v : Fin M.ord} (ut : u≠t) (vt : v≠t) (uv : M.adj u.val v.val) :
      ∃ f, f∉K ∧ f∈triangle u ∧ f∈triangle v := by
    obtain ⟨ne,a,b,ab,au,av,bu,bv⟩ := (adj_iff_shared_edge G hh u v).mp uv
    by_cases na : a∈K
    · by_cases nb : b∈K
      · obtain ⟨e,ce,te⟩ := common_edge_at G hh ab na nb
        obtain ⟨f,cf,uf⟩ := common_edge_at G hh ab au bu
        obtain ⟨g,cg,vg⟩ := common_edge_at G hh ab av bv
        obtain rfl := uniqueAcross G hh ce cf; obtain rfl := uniqueAcross G hh ce cg
        grind
      · exact ⟨b,nb,bu,bv⟩
    · exact ⟨a,na,au,av⟩
  have lift {u v : Nat} (path : PathAvoiding M.adj [t.val] u v) : ∀ (hu : u<M.ord) (hv : v<M.ord)
      (a b : Face M), a∈triangle (⟨u,hu⟩ : Fin M.ord) → b∈triangle (⟨v,hv⟩ : Fin M.ord) →
      a∉K → b∉K → OutsideWalk G K a b := by
    induction path with
    | here _ => intro hu _ a b au bv na nb; exact through ⟨_,hu⟩ au bv na nb
    | @step v w path edge no ih =>
      intro hu hw a b au bw na nb
      have bounds := dart_endpoints G (dart_iff.mpr edge)
      have outv := path_last path
      have vt : (⟨v,bounds.1⟩ : Fin M.ord)≠t := fun e => outv (List.mem_singleton.mpr (congrArg Fin.val e))
      have wt : (⟨w,hw⟩ : Fin M.ord)≠t := fun e => no (List.mem_singleton.mpr (congrArg Fin.val e))
      obtain ⟨f,nf,fv,fw⟩ := shared vt wt edge
      exact (ih hu bounds.1 a f au fv na nf).trans (through ⟨w,hw⟩ fw bw nf nb)
  intro a na b nb
  have representative (f : Face M) (nf : f∉K) : ∃ u : Fin M.ord, u≠t ∧ f∈triangle u := by
    obtain ⟨u,v,hit⟩ := face_dart G hh f
    have bound := (dart_endpoints G (incident_dart G hit)).1
    have m : f∈triangle (⟨u,bound⟩ : Fin M.ord) := (mem_triangle _ _).mpr (sideEnds hit).1
    exact ⟨⟨u,bound⟩,fun eq=>nf (show f∈triangle t from eq ▸ m),m⟩
  obtain ⟨u,nu,au⟩ := representative a na; obtain ⟨v,nv,bv⟩ := representative b nb
  have ux : u.val≠t.val := fun e=>nu (Fin.ext e)
  have vx : v.val≠t.val := fun e=>nv (Fin.ext e)
  exact lift (G.connectivity.2 [t.val] (by simp) _ _ u.isLt v.isLt (by simp [ux]) (by simp [vx])) u.isLt v.isLt a b au bv na nb

private theorem degree_three {M} (G : IsDiskFullerene M h) (hh : 3≤h) (v : Face M) : 3≤(dualRow G v).length := by
  by_cases eq : v=apex M
  · subst v; rw [row_length]; change 3≤M.outer.length; rw [G.outerSize]; exact hh
  · have := inner_degree G eq; omega

private theorem corner_mem {M} (G : IsDiskFullerene M h) (c : Face M) (p q : Fin M.faces[c.val].length)
    (step : q.val=p.val+1 ∨ (p.val+1=M.faces[c.val].length ∧ q.val=0)) :
    (atSide G c p,atSide G c q)∈sides (dualRow G c) := by
  let R := dualRow G c
  have hp : p.val<R.length := by simp [R,row_length]
  have nx : next R.length p.val=q.val := by
    have len : R.length=M.faces[c.val].length := row_length G c
    unfold next; split <;> omega
  have mem := List.getElem_mem (l:=sides R) (n:=p.val) (by simpa [sides_size] using hp)
  rw [side_at R p.val hp] at mem
  simpa only [R,atSide_eq,nx] using mem

private theorem index_for {M} (G : IsDiskFullerene M h) {c x : Face M} (hit : x∈dualRow G c) :
    ∃ i, atSide G c i=x := by
  obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp hit
  exact ⟨⟨n,by rwa [←row_length G c]⟩,(atSide_eq G c _).trans eq⟩

/-- A three-clique with connected complement is an actual dual face. -/
theorem recognize_facial {M} (G : IsDiskFullerene M h) (hh : 3≤h) (K : List (Face M))
    (size : K.length=3) (nd : K.Nodup)
    (clique : ∀ a∈K, ∀ b∈K, a≠b → b∈dualRow G a)
    (conn : ∀ x∉K, ∀ y∉K, OutsideWalk G K x y) :
    ∃ u : Fin M.ord, ∀ f, f∈K ↔ f∈triangle u := by
  have exposed (c) (inside : c∈K) : ∃ z∈dualRow G c, z∉K := by
    apply Classical.byContradiction; intro closed
    have row : dualRow G c ⊆ K.erase c := by
      intro z hz
      apply (List.mem_erase_of_ne (show z≠c from fun eq => row_no_loop G hh c (eq ▸ hz))).mpr
      exact Classical.byContradiction (fun nz=>closed ⟨z,hz,nz⟩)
    have len := (row_nodup G (noRepeatOnSphere G hh) c).length_le_of_subset row
    rw [List.length_erase_of_mem inside,size] at len
    have := degree_three G hh c; omega
  obtain ⟨c,a,b,rfl⟩ : ∃ c a b, K=[c,a,b] := by
    cases K with | nil => simp at size | cons c R =>
      cases R with | nil => simp at size | cons a R =>
        cases R with | nil => simp at size | cons b R =>
          have empty : R=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at size; omega)
          exact ⟨c,a,b,by rw [empty]⟩
  have distinct : c≠a ∧ c≠b ∧ a≠b := by simpa [and_assoc] using nd
  let K := [c,a,b]
  have kc : c∈K := by simp [K]
  have ka : a∈K := by simp [K]
  have kb : b∈K := by simp [K]
  obtain ⟨i,iv⟩ := index_for G (clique c kc a ka distinct.1)
  obtain ⟨k,kv⟩ := index_for G (clique c kc b kb distinct.2.1)
  have ne : i≠k := fun eq => distinct.2.2 (iv.symm.trans ((congrArg (atSide G c) eq).trans kv))
  have mk {p q : Fin M.faces[c.val].length} (lt : p<q) (hp : atSide G c p∈K) (hq : atSide G c q∈K)
      (edge : atSide G c q∈dualRow G (atSide G c p)) :
      (atSide G c p,atSide G c q)∈sides (dualRow G c) ∨ (atSide G c q,atSide G c p)∈sides (dualRow G c) := by
    rcases openRim G hh K exposed conn c kc p q lt hp hq edge with f|⟨zero,last⟩
    · exact Or.inl (corner_mem G c p q (Or.inl f))
    · exact Or.inr (corner_mem G c q p (Or.inr ⟨last,zero⟩))
  have corner : (a,b)∈sides (dualRow G c) ∨ (b,a)∈sides (dualRow G c) := by
    by_cases lt : i<k
    · simpa [iv,kv] using mk lt (iv ▸ ka) (kv ▸ kb) (by rw [iv,kv]; exact clique a ka b kb distinct.2.2)
    · have rev : k<i := by omega
      have d := mk rev (kv ▸ kb) (iv ▸ ka) (by rw [iv,kv]; exact clique b kb a ka distinct.2.2.symm)
      simpa [iv,kv,or_comm] using d
  have result {x y : Face M} (hxy : (x,y)∈sides (dualRow G c)) (kx : x∈K) (ky : y∈K) :
      ∃ u : Fin M.ord, ∀ f, f∈K ↔ f∈triangle u := by
    obtain ⟨_,u,_,_,_,fs⟩ := cornerEdge G hxy
    have sub : triangle u⊆K := by
      intro f mf; rcases fs f ((mem_triangle _ _).mp mf) with e|e|e <;> grind
    refine ⟨u,fun f=>⟨?_,fun h=>sub h⟩⟩
    intro kf; apply Classical.byContradiction; intro no
    have smaller : triangle u ⊆ K.erase f := by
      intro x mx; exact (List.mem_erase_of_ne (show x≠f from fun eq=>no (eq ▸ mx))).mpr (sub mx)
    have nodup : (triangle u).Nodup := (List.nodup_finRange _).filter _
    have h := nodup.length_le_of_subset smaller
    rw [triangle_three G hh,List.length_erase_of_mem kf] at h
    simp [K] at h
  exact corner.elim (fun e=>result e ka kb) (fun e=>result e kb ka)

/-- An isomorphism of two dual one-skeleta; no cyclic orders or triangle
correspondence are included. -/
structure SkeletonIso {M N} {h k} (A : IsDiskFullerene M h) (B : IsDiskFullerene N k) where
  f : Face M → Face N
  g : Face N → Face M
  left : ∀ x, g (f x)=x
  right : ∀ x, f (g x)=x
  edge : ∀ x y, y∈dualRow A x ↔ f y∈dualRow B (f x)

namespace SkeletonIso
variable {M N : MapData} {A : IsDiskFullerene M h} {B : IsDiskFullerene N k}

def inverse (S : SkeletonIso A B) : SkeletonIso B A where
  f := S.g
  g := S.f
  left := S.right
  right := S.left
  edge x y := by simpa only [S.right] using (S.edge (S.g x) (S.g y)).symm

private theorem image_mem (S : SkeletonIso A B) (K : List (Face M)) (x : Face M) :
    S.f x∈K.map S.f ↔ x∈K := by
  constructor
  · intro m; obtain ⟨y,yK,eq⟩ := List.mem_map.mp m
    have same : y=x := by simpa only [S.left] using congrArg S.g eq
    exact same ▸ yK
  · exact List.mem_map_of_mem

private theorem image_walk (S : SkeletonIso A B) (K : List (Face M)) {x y : Face M}
    (p : OutsideWalk A K x y) : OutsideWalk B (K.map S.f) (S.f x) (S.f y) := by
  induction p with
  | refl => exact .refl
  | step _ e ih => exact ih.step ⟨fun m=>e.1 ((S.image_mem K _).mp m),fun m=>e.2.1 ((S.image_mem K _).mp m),(S.edge _ _).mp e.2.2⟩

/-- Facets can be recovered from the one-skeleton, irrespective of possible
separating three-cycles. -/
theorem preserves_faces (S : SkeletonIso A B) (hh : 3≤h) (hk : 3≤k) (u : Fin M.ord) :
    ∃ v : Fin N.ord, ∀ i, i∈triangle u ↔ S.f i∈triangle v := by
  let K := triangle u
  let L := K.map S.f
  have size : L.length=3 := by simp [L,K,triangle_three A hh]
  have nd : K.Nodup := (List.nodup_finRange _).filter _
  have ndL : L.Nodup := List.pairwise_map.mpr (nd.imp (fun ne eq => ne (by simpa only [S.left] using congrArg S.g eq)))
  have clique (a) (ha : a∈L) (b) (hb : b∈L) (ab : a≠b) : b∈dualRow B a := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha; obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    exact (S.edge _ _).mp (share_edge A hh hx hy (fun eq => ab (congrArg _ eq)))
  have connected (a) (ha : a∉L) (b) (hb : b∉L) : OutsideWalk B L a b := by
    have off (w) (nw : w∉L) : S.g w∉K := fun mw => nw (S.right w ▸ (S.image_mem K _).mpr mw)
    simpa only [S.right] using S.image_walk K (facial_connected A hh u _ (off a ha) _ (off b hb))
  obtain ⟨v,classify⟩ := recognize_facial B hk L size ndL clique connected
  exact ⟨v,fun i=>(S.image_mem K i).symm.trans (classify (S.f i))⟩

def triangulation (S : SkeletonIso A B) (hh : 3≤h) (hk : 3≤k) : TriangulationIso M N where
  f := S.f
  g := S.g
  left := S.left
  right := S.right
  maps := S.preserves_faces hh hk
  covers v := by
    obtain ⟨u,eq⟩ := S.inverse.preserves_faces hk hh v
    exact ⟨u,fun i=>by simpa only [inverse,S.left] using (eq (S.f i)).symm⟩

theorem primal (S : SkeletonIso A B) (hh : 3≤h) (hk : 3≤k) : GraphIso M N :=
  (S.triangulation hh hk).primal_iso A B hh hk

end SkeletonIso

end DiskFullerene.Dual
