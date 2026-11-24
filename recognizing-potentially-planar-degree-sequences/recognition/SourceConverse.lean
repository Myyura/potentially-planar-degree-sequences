import SourceMap
import SparseBoundary.TruncationData

/-! In a graph without a K₅ minor, the three intermediate vertices of a
path cube separate its distant positions. This proves the source's confinement
property without choosing an embedding or comparing possible rotations. -/
namespace Recognition.SourceConverse
open SparseBoundary SparseBoundary.Graph SparseBoundary.Truncation Recognition.Reduction

/-- The source obstruction uses only the five-clique half of Wagner planarity. -/
def K5Free (G : Graph n) : Prop := ¬ ∃ bags, G.minorTest clique5 bags = true

def Linked (G : Graph n) (A B : List (Fin n)) := ∃ a ∈ A, ∃ b ∈ B, G.adj a b = true

private theorem linked_symm (G : Graph n) {A B : List (Fin n)} (h : Linked G A B) : Linked G B A := by
  obtain ⟨a,ha,b,hb,hab⟩ := h
  exact ⟨b,hb,a,ha,(G.adj_comm b a).trans hab⟩

private theorem separator_minor (G : Graph n) (A B : List (Fin n)) (s : Fin 3 → Fin n)
    (ac : G.connected A) (bc : G.connected B) (ab : ∀ v ∈ A, v ∉ B)
    (as_ : ∀ i, s i ∉ A) (bs : ∀ i, s i ∉ B) (inj : Function.Injective s)
    (AB : Linked G A B) (AS : ∀ i, Linked G A [s i]) (BS : ∀ i, Linked G B [s i])
    (SS : ∀ i j, i≠j → G.adj (s i) (s j)) :
    ∃ bags, G.minorTest clique5 bags = true := by
  let bag : Fin 5 → List (Fin n) := Fin.cases A (Fin.cases B (fun i => [s i]))
  refine ⟨bag,model_iff.mpr ⟨?_,?_,?_⟩⟩
  · exact Fin.cases ac (Fin.cases bc (fun _ => rfl))
  · intro i j ne v hi hj
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact ne rfl
      | succ j =>
        cases j using Fin.cases with
        | zero => exact ab _ hi hj
        | succ j => exact as_ j (List.mem_singleton.mp hj ▸ hi)
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact ab _ hj hi
        | succ j =>
          cases j using Fin.cases with
          | zero => exact ne rfl
          | succ j => exact bs j (List.mem_singleton.mp hj ▸ hi)
      | succ i =>
        obtain rfl := List.mem_singleton.mp hi
        cases j using Fin.cases with
        | zero => exact as_ i hj
        | succ j =>
          cases j using Fin.cases with
          | zero => exact bs i hj
          | succ j => exact ne (congrArg (fun t : Fin 3 => t.succ.succ) (inj (List.mem_singleton.mp hj)))
  · intro i j req
    have ne : i ≠ j := by simpa [clique5] using req
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => contradiction
      | succ j => exact Fin.cases (motive := fun j => Linked G A (bag j.succ)) AB AS j
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact linked_symm _ AB
        | succ j =>
          cases j using Fin.cases with
          | zero => contradiction
          | succ j => exact BS j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact linked_symm _ (AS i)
        | succ j =>
          cases j using Fin.cases with
          | zero => exact linked_symm _ (BS i)
          | succ j =>
            exact ⟨s i,by simp [bag],s j,by simp [bag],SS i j (fun eq => ne (eq ▸ rfl))⟩

def HasCube (G : Graph n) (q : Nat) := ∀ x y : Fin n, x.val < q → y.val < q →
  x ≠ y → x.val ≤ y.val+3 → y.val ≤ x.val+3 → G.adj x y = true

private def interval (n a : Nat) : (k : Nat) → a+k ≤ n → List (Fin n)
  | 0, _ => []
  | k+1, h => ⟨a,by omega⟩ :: interval n (a+1) k (by omega)

private theorem interval_mem (a k : Nat) (bound : a+k ≤ n) (z : Fin n) :
    z ∈ interval n a k bound ↔ a ≤ z.val ∧ z.val < a+k := by
  induction k generalizing a with
  | zero => simp [interval]
  | succ k ih =>
    simp only [interval,List.mem_cons,ih,Fin.ext_iff]; omega

private theorem interval_connected (G : Graph n) (q a k : Nat) (hc : HasCube G q)
    (bound : a+k+1 ≤ n) (inside : a+k+1 ≤ q) :
    G.connected (interval n a (k+1) (by omega)) = true := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    let x : Fin n := ⟨a,by omega⟩
    let y : Fin n := ⟨a+1,by omega⟩
    let tail := interval n (a+2) k (by omega)
    have edge : G.adj x y := hc x y (by dsimp [x]; omega) (by dsimp [y]; omega)
      (by intro eq; have := congrArg Fin.val eq; dsimp [x,y] at this; omega)
      (by dsimp [x,y]; omega) (by dsimp [x,y]; omega)
    change ((y::tail).any (G.adj x) && G.connected (y::tail)) = true
    exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨y,by simp,edge⟩,
      ih (a+1) (by omega) (by omega)⟩

/-- Any connected bag that starts at x, uses only external vertices thereafter,
and reaches y closes a K₅ minor across the three intervening skeleton positions. -/
theorem gap_minor (G : Graph n) (q : Nat) (hc : HasCube G q) (x y : Fin n)
    (gap : x.val+4 ≤ y.val) (inside : y.val < q) (A : List (Fin n))
    (con : G.connected A) (hx : x ∈ A) (apart : ∀ v ∈ A, v=x ∨ q ≤ v.val)
    (reach : ∃ v ∈ A, G.adj v y = true) : ¬ K5Free G := by
  let p := x.val+4
  let k := y.val-p
  have bound : p+k+1 ≤ n := by dsimp [p,k]; have := y.isLt; omega
  let B := interval n p (k+1) (by omega)
  let s := fun i : Fin 3 => (⟨x.val+1+i.val,by have := i.isLt; have := y.isLt; omega⟩ : Fin n)
  have sp (i : Fin 3) : x.val < (s i).val ∧ (s i).val < p := by
    dsimp [s,p]; have := i.isLt; omega
  have bm (z : Fin n) : z ∈ B ↔ p ≤ z.val ∧ z.val ≤ y.val := by
    rw [show B = interval n p (k+1) (by omega) from rfl,interval_mem]; dsimp [k,p]; omega
  let start : Fin n := ⟨p,by omega⟩
  have startmem : start ∈ B := (bm _).mpr ⟨Nat.le_refl _,gap⟩
  have sa (i : Fin 3) : Linked G A [s i] := by
    have h := sp i
    exact ⟨x,hx,s i,by simp,hc _ _ (by omega) (by dsimp [p] at *; omega)
      (fun e => (Nat.ne_of_lt h.1) (congrArg Fin.val e))
      (by omega) (by dsimp [p] at *; omega)⟩
  have sb (i : Fin 3) : Linked G B [s i] := by
    have h := sp i
    have startval : start.val = p := rfl
    exact ⟨start,startmem,s i,by simp,hc _ _ (by dsimp [p] at *; omega) (by dsimp [p] at *; omega)
      (fun e => (Nat.ne_of_lt h.2) ((congrArg Fin.val e).symm.trans startval))
      (by dsimp [p] at *; omega) (by omega)⟩
  obtain ⟨v,hv,hy⟩ := reach
  have minor := separator_minor G A B s con (interval_connected G q p k hc bound (by dsimp [p,k]; omega))
    (fun z hz hz' => by have := apart z hz; have := (bm z).mp hz'; dsimp [p] at *; grind)
    (fun i h => by have := apart (s i) h; have := sp i; dsimp [p] at *; grind)
    (fun i h => by have := (bm _).mp h; have := sp i; omega)
    (fun i j eq => Fin.ext (by have := congrArg Fin.val eq; dsimp [s] at this; omega))
    ⟨v,hv,y,(bm _).mpr ⟨gap,Nat.le_refl _⟩,hy⟩ sa sb
    (fun i j ne => by
      have := sp i; have := sp j; dsimp [p] at *
      apply hc <;> try omega
      intro eq
      apply ne; apply Fin.ext
      have := congrArg Fin.val eq; dsimp [s] at this; omega)
  exact fun free => free minor

theorem no_chord (G : Graph n) (q : Nat) (hc : HasCube G q) (hp : K5Free G) (x y : Fin n)
    (gap : x.val+4 ≤ y.val) (hi : y.val < q) : ¬ G.adj x y = true := fun edge =>
  gap_minor G q hc x y gap hi [x] rfl (by simp)
    (fun _ h => .inl (List.mem_singleton.mp h)) ⟨x,by simp,edge⟩ hp

private theorem join_connected (G : Graph n) (x : Fin n) (A : List (Fin n))
    (con : G.connected A) (h : ∃ v ∈ A, G.adj x v) : G.connected (x::A) := by
  cases A with
  | nil => simp at h
  | cons y ys => exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr h,con⟩

theorem outside_one_root (G : Graph n) (q : Nat) (hc : HasCube G q) (hp : K5Free G)
    (x y : Fin n) (gap : x.val+4 ≤ y.val) (hi : y.val<q) (A : List (Fin n))
    (con : G.connected A) (outside : ∀ v ∈ A, q ≤ v.val)
    (left : ∃ v ∈ A, G.adj x v) (right : ∃ v ∈ A, G.adj v y) : False := by
  obtain ⟨v,hv,hy⟩ := right
  exact gap_minor G q hc x y gap hi (x::A) (join_connected G x A con left) (by simp)
    (fun v h => (List.mem_cons.mp h).imp_right (outside v)) ⟨v,List.mem_cons_of_mem _ hv,hy⟩ hp


/-- Naturals name original positions; out-of-range labels never denote edges. -/
def natAdj (G : Graph n) (u v : Nat) : Bool :=
  if h : u<n ∧ v<n then G.adj ⟨u,h.1⟩ ⟨v,h.2⟩ else false

@[simp] theorem natAdj_fin (G : Graph n) (u v : Fin n) : natAdj G u.val v.val = G.adj u v := by
  simp [natAdj,u.isLt,v.isLt]

private theorem natAdj_swap (G : Graph n) (u v : Nat) : natAdj G u v = natAdj G v u := by
  by_cases h : u < n <;> by_cases k : v < n <;> simp [natAdj,h,k] <;> exact G.adj_comm ..

def Contains (I : Instance) (G : Graph n) := ∀ e ∈ prescribed I, natAdj G e.left e.right = true

private theorem cube_contains (I : Instance) (G : Graph n) (h : Contains I G) :
    HasCube G (skeletonOrder I) := by
  have asc (u v : Fin n) (hu : u.val < v.val) (hv : v.val < skeletonOrder I) (hl : v.val ≤ u.val+3) :
      G.adj u v := by
    let d := v.val-u.val
    have pos : d=1 ∨ d=2 ∨ d=3 := by dsimp [d]; omega
    have bound : u.val < skeletonOrder I-d := by dsimp [d]; omega
    let e : Edge := ⟨u.val,u.val+d,2*(d-1)+(u.val/d)%2⟩
    have he : e ∈ prescribed I := by
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨d, by simpa using pos,
        List.mem_map.mpr ⟨u.val,List.mem_range.mpr bound,rfl⟩⟩
    have eq : u.val+d=v.val := by dsimp [d]; omega
    have E := h e he
    simpa [e,eq] using E
  intro u v hu hv ne h₁ h₂
  by_cases lt : u.val < v.val
  · exact asc _ _ lt hv h₂
  · rw [adj_comm]; exact asc _ _ (by have := Fin.val_ne_of_ne ne; omega) hu h₁

private theorem cap_attached (I : Instance) (G : Graph n) (h : Contains I G) (r : Fin I.bins) :
    natAdj G (4*r.val) (SourceMap.capName I r) := by
  let e : Edge := ⟨4*r.val,SourceMap.capName I r,8⟩
  exact h e (List.mem_append_right _ (List.mem_map.mpr ⟨r.val,List.mem_range.mpr r.isLt,rfl⟩))

private abbrev order (I : Instance) := (sourceTable I).length

private def root (I : Instance) (r : Fin I.bins) : Fin (order I) :=
  ⟨4*r.val, by unfold order; rw [source_order]; unfold skeletonOrder; have := r.isLt; omega⟩

private theorem lt_root (I : Instance) (r : Fin I.bins) : (root I r).val < skeletonOrder I := by
  unfold root skeletonOrder; have := r.isLt; simp; omega

private theorem only_one (I : Instance) (G : Graph (order I)) (hc : Contains I G) (hp : K5Free G)
    (A : List (Fin (order I))) (con : G.connected A) (outside : ∀ v ∈ A, skeletonOrder I ≤ v.val)
    {r s : Fin I.bins} (R : ∃ v ∈ A, G.adj (root I r) v)
    (S : ∃ v ∈ A, G.adj (root I s) v) : r = s := by
  have contra (r s : Fin I.bins) (lt : r.val<s.val)
      (L : ∃ v ∈ A, G.adj (root I r) v) (T : ∃ v ∈ A, G.adj (root I s) v) : False := by
    obtain ⟨v,hv,he⟩ := T
    exact outside_one_root G _ (cube_contains I G hc) hp _ _ (by change 4*r.val+4≤4*s.val; omega)
      (lt_root I s) A con outside L ⟨v,hv,(G.adj_comm ..).trans he⟩
  apply Fin.ext
  by_cases h : r.val<s.val
  · exact False.elim (contra r s h R S)
  · by_cases h' : s.val<r.val
    · exact False.elim (contra s r h' S R)
    · omega

private def rootAdj (I : Instance) (G : Graph (order I)) (r : Fin I.bins) (v : Nat) :=
  natAdj G (root I r).val v

private theorem root_cap (I : Instance) (G : Graph (order I)) (hc : Contains I G) (hp : K5Free G)
    (r s : Fin I.bins) : rootAdj I G r (SourceMap.capName I s) = true ↔ r=s := by
  have hh : SourceMap.capName I s < order I := by
    unfold SourceMap.capName order; rw [source_order]; have := s.isLt; omega
  let z : Fin (order I) := ⟨_,hh⟩
  have own : G.adj (root I s) z := by
    have h := cap_attached I G hc s
    change natAdj G (root I s).val z.val = true at h
    simpa using h
  constructor
  · intro h
    apply only_one I G hc hp [z] rfl
    · intro v hv; obtain rfl := List.mem_singleton.mp hv
      dsimp [z,SourceMap.capName]; omega
    · refine ⟨z,by simp,?_⟩
      change natAdj G (root I r).val z.val = true at h
      simpa using h
    · exact ⟨z,by simp,own⟩
  · rintro rfl; exact cap_attached I G hc r

private theorem val_range (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last,List.map_append,List.range_succ]
    simpa [List.map_map,Function.comp_def] using congrArg (· ++ [n]) ih

theorem degree_count (G : Graph n) (x : Fin n) :
    ((List.range n).filter (natAdj G x.val)).length = G.degree x := by
  rw [← val_range, List.filter_map]
  simp [Function.comp_def,degree]

private theorem cap_interval (I : Instance) :
    (List.finRange I.bins).map (SourceMap.capName I) = List.range' (skeletonOrder I+I.weights.sum) I.bins := by
  rw [List.range'_eq_map_range,← val_range,List.map_map]
  rfl

private theorem cap_count (I : Instance) (G : Graph (order I)) (hc : Contains I G) (hp : K5Free G)
    (r : Fin I.bins) :
    ((List.range' (skeletonOrder I+I.weights.sum) I.bins).filter (rootAdj I G r)).length = 1 := by
  rw [← cap_interval,List.filter_map,List.length_map]
  have p : ((List.finRange I.bins).filter (rootAdj I G r ∘ SourceMap.capName I)).Perm [r] := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (by simp)).mpr
    intro s
    simp [Function.comp_def, root_cap I G hc hp r s,eq_comm]
  exact p.length_eq

private theorem skeleton_count (I : Instance) (G : Graph (order I)) (hv : Valid I)
    (hc : Contains I G) (hp : K5Free G) (r : Fin I.bins) :
    ((List.range (skeletonOrder I)).filter (rootAdj I G r)).length =
      min 3 (4*r.val)+min 3 (4*I.bins+2-4*r.val) := by
  let k := skeletonOrder I-4
  let x := root I r
  have hm := hv.1
  have k4 : k+4=skeletonOrder I := by unfold k skeletonOrder; omega
  have k3 : k+3=4*I.bins+2 := by unfold k skeletonOrder; omega
  have hx : x.val < k+4 := k4 ▸ lt_root I r
  have cube := cube_contains I G hc
  have p : ((List.range (skeletonOrder I)).filter (rootAdj I G r)).Perm ((SourceMap.cube k).neighbors x.val) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) (SourceMap.cube_neighbors_distinct _ _ hx)).mpr
    intro v
    rw [List.mem_filter,List.mem_range, SourceMap.cube_edge _ _ _ hx,k4]
    constructor
    · rintro ⟨hq,adj⟩
      have ord := source_order I
      let y : Fin (order I) := ⟨v,by dsimp [order]; omega⟩
      change natAdj G x.val y.val = true at adj
      rw [natAdj_fin] at adj
      have ne : x.val ≠ v := by
        intro eq
        have eq' : x=y := Fin.ext eq
        rw [eq',adj_self] at adj
        contradiction
      refine ⟨hq,ne,?_,?_⟩
      · apply Classical.byContradiction; intro far
        exact no_chord G _ cube hp y x (by change v+4 ≤ x.val; omega) (lt_root I r) ((G.adj_comm ..).trans adj)
      · apply Classical.byContradiction; intro far
        exact no_chord G _ cube hp x y (by change x.val+4 ≤ v; omega) hq adj
    · rintro ⟨hq,ne,h₁,h₂⟩
      let y : Fin (order I) := ⟨v,by dsimp [order]; rw [source_order]; omega⟩
      refine ⟨hq,?_⟩
      change natAdj G x.val y.val = true
      rw [natAdj_fin]
      exact cube x y (lt_root I r) hq (fun he => ne (congrArg Fin.val he)) h₁ h₂
  rw [p.length_eq,SourceMap.cube_degree _ _ hx,k3]; rfl

theorem item_quota (I : Instance) (G : Graph (order I)) (hv : Valid I) (hc : Contains I G)
    (hp : K5Free G) (deg : G.Realizes (sourceTable I)) (r : Fin I.bins) :
    ((List.range' (skeletonOrder I) I.weights.sum).filter (rootAdj I G r)).length = I.capacity := by
  have htot := degree_count G (root I r)
  change ((List.range (order I)).filter (rootAdj I G r)).length = _ at htot
  have range_eq : List.range (order I) = List.range (skeletonOrder I) ++
      List.range' (skeletonOrder I) I.weights.sum ++ List.range' (skeletonOrder I+I.weights.sum) I.bins := by
    simp [order,source_order,List.range_add,List.range'_eq_map_range,List.append_assoc]
  rw [range_eq,List.filter_append,List.filter_append] at htot
  simp only [List.length_append] at htot
  rw [skeleton_count I G hv hc hp,cap_count I G hc hp] at htot
  replace htot := htot.trans (deg (root I r))
  have hdeg := SourceMap.root_target I hv r
  rw [List.getElem?_eq_getElem (show 4*r.val < (sourceTable I).length from (root I r).isLt)] at hdeg
  have := Option.some.inj hdeg
  change _ = (sourceTable I)[4*r.val]'(root I r).isLt at htot
  omega


private def blocks (a : Nat) : List Nat → List (Nat × Nat)
  | [] => []
  | w::ws => (a,w)::blocks (a+w) ws

private theorem block_sizes (ws : List Nat) (a : Nat) : (blocks a ws).map Prod.snd = ws := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih => simp [blocks,ih]

private theorem block_ranges (ws : List Nat) (a : Nat) :
    (blocks a ws).flatMap (fun p => List.range' p.1 p.2) = List.range' a ws.sum := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih => simp [blocks,ih]

private theorem block_info (ws : List Nat) (a : Nat) (p : Nat × Nat) (h : p ∈ blocks a ws) :
    a ≤ p.1 ∧ p.1+p.2 ≤ a+ws.sum ∧ p.2 ∈ ws ∧
    ∀ v, p.1 ≤ v → v+1 < p.1+p.2 →
      ∃ e ∈ itemEdges a ws, e.left = v ∧ e.right = v+1 := by
  induction ws generalizing a with
  | nil => simp [blocks] at h
  | cons w ws ih =>
    rcases List.mem_cons.mp h with rfl|tail
    · refine ⟨Nat.le_refl _,by simp,by simp,?_⟩
      intro v lo hi
      let j := v-a
      have eq : a+j=v := by dsimp [j]; omega
      have mem : j ∈ List.range (w-1) := List.mem_range.mpr (by dsimp [j]; change v+1<a+w at hi; omega)
      exact ⟨_,List.mem_append_left _ (List.mem_map.mpr ⟨j,mem,rfl⟩),eq,congrArg (·+1) eq⟩
    · obtain ⟨lo,hi,mem,edges⟩ := ih _ tail
      refine ⟨by omega,by simp; omega,List.mem_cons_of_mem _ mem,?_⟩
      intro v vl vu
      obtain ⟨e,he,el,er⟩ := edges v vl vu
      exact ⟨e,List.mem_append_right _ he,el,er⟩

private theorem connected_path (G : Graph n) (a k : Nat) (bound : a+k+1 ≤ n)
    (edges : ∀ v, a ≤ v → v+1 < a+k+1 → natAdj G v (v+1)) :
    G.connected (interval n a (k+1) (by omega)) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    let x : Fin n := ⟨a,by omega⟩
    let y : Fin n := ⟨a+1,by omega⟩
    let tail := interval n (a+2) k (by omega)
    have edge := edges a (Nat.le_refl _) (by omega)
    change natAdj G x.val y.val = true at edge
    rw [natAdj_fin] at edge
    change ((y::tail).any (G.adj x) && G.connected (y::tail)) = true
    exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨y,by simp,edge⟩,
      ih (a+1) (by omega) (fun v lo hi => edges v (by omega) (by omega))⟩

private noncomputable def seen (I : Instance) (G : Graph (order I)) (x : Nat) : Option (Fin I.bins) := by
  classical
  exact if h : ∃ r, rootAdj I G r x then some h.choose else none

private theorem seen_sound (I : Instance) (G : Graph (order I)) (x : Nat) (r : Fin I.bins)
    (h : seen I G x = some r) : rootAdj I G r x := by
  unfold seen at h
  split at h
  · rename_i H; exact Option.some.inj h ▸ H.choose_spec
  · contradiction

private theorem seen_complete (I : Instance) (G : Graph (order I)) (hc : Contains I G) (hp : K5Free G)
    (x : Nat) (lo : skeletonOrder I ≤ x) (hi : x < order I) (r : Fin I.bins) (h : rootAdj I G r x) :
    seen I G x = some r := by
  let v : Fin (order I) := ⟨x,hi⟩
  unfold seen
  split
  · rename_i H
    apply congrArg some
    have K := H.choose_spec
    change natAdj G (root I H.choose).val v.val = true at K
    change natAdj G (root I r).val v.val = true at h
    exact only_one I G hc hp [v] rfl (fun _ h => List.mem_singleton.mp h ▸ lo)
      ⟨v,by simp,by simpa using K⟩ ⟨v,by simp,by simpa using h⟩
  · rename_i H; exact False.elim (H ⟨r,h⟩)

private theorem block_unique (I : Instance) (G : Graph (order I)) (hv : Valid I) (hc : Contains I G)
    (hp : K5Free G) {p : Nat×Nat} (hblock : p ∈ blocks (skeletonOrder I) I.weights)
    {r s : Fin I.bins} (hr : some r ∈ (List.range' p.1 p.2).map (seen I G))
    (hs : some s ∈ (List.range' p.1 p.2).map (seen I G)) : r=s := by
  obtain ⟨min,max,w,edges⟩ := block_info _ _ _ hblock
  have endIn : p.1+p.2 ≤ order I := by unfold order; rw [source_order]; omega
  let A := interval (order I) p.1 p.2 endIn
  have positive : 0<p.2 := by have := (hv.2.2.2 _ w).1; omega
  have len : p.2 = (p.2-1)+1 := by omega
  have cc : G.connected A := by
    have := connected_path G p.1 (p.2-1) (by omega) (fun v vl vu => by
      obtain ⟨e,he,el,er⟩ := edges v vl (by omega)
      have he' : e ∈ prescribed I := List.mem_append_left _ (List.mem_append_right _ he)
      simpa [el,er] using hc e he')
    simpa only [← len] using this
  have outside : ∀ v ∈ A, skeletonOrder I ≤ v.val := fun v h =>
    Nat.le_trans min ((interval_mem _ _ _ _).mp h).1
  have touch (r : Fin I.bins) (hr : some r ∈ (List.range' p.1 p.2).map (seen I G)) :
      ∃ v ∈ A, G.adj (root I r) v := by
    obtain ⟨x,hx,seenx⟩ := List.mem_map.mp hr
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hx
    let v : Fin (order I) := ⟨p.1+1*j,by omega⟩
    refine ⟨v,(interval_mem _ _ _ _).mpr (by dsimp [v]; omega),?_⟩
    have K := seen_sound _ _ _ _ seenx
    change natAdj G (root I r).val v.val = true at K
    simpa using K
  exact only_one I G hc hp A cc outside (touch _ hr) (touch _ hs)

private noncomputable def record (I : Instance) (G : Graph (order I)) (hm : 0<I.bins)
    (p : Nat×Nat) : PathRecord I.bins := by
  classical
  let hits := (List.range' p.1 p.2).map (seen I G)
  exact (if h : ∃ r, some r ∈ hits then h.choose else ⟨0,hm⟩,hits)

private theorem observed_count {m : Nat} (xs : List Nat) (f : Nat → Option (Fin m)) (r : Fin m)
    (P : Nat → Bool) (H : ∀ x ∈ xs, f x = some r ↔ P x = true) :
    ((xs.map f).filterMap id).count r = (xs.filter P).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have K := ih (fun x h => H x (List.mem_cons_of_mem _ h))
    simp at K
    have A := H a (by simp)
    cases h : f a with
    | none => have ha : P a = false := by cases h' : P a <;> simp_all
              simp [h,ha,K]
    | some v =>
      by_cases hv : v=r
      · have ha := A.mp (h.trans (congrArg some hv))
        simp [h,hv,ha,K]
      · have ha : P a = false := by cases h' : P a <;> simp_all
        simp [h,hv,ha,K]

/-- End-to-end converse for the labelled source graph. The input hypotheses
are its degree list, its concrete prescribed edges, and exclusion of a five-clique minor. -/
theorem source_converse_k5free (I : Instance) (hv : Valid I) (G : Graph (sourceTable I).length)
    (deg : G.Realizes (sourceTable I)) (contains : Contains I G) (hp : K5Free G) : ThreePartition I := by
  let bs := blocks (skeletonOrder I) I.weights
  let rows := bs.map (record I G hv.1)
  apply decode_partition I hv rows
  · simpa [rows,bs,record,Function.comp_def] using block_sizes I.weights (skeletonOrder I)
  · intro a ha r hr
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp ha
    change some r ∈ (List.range' p.1 p.2).map (seen I G) at hr
    unfold record
    dsimp only
    split
    · rename_i H
      exact block_unique I G hv contains hp hp' hr H.choose_spec
    · rename_i H; exact False.elim (H ⟨r,hr⟩)
  · intro r
    have E : rows.flatMap Prod.snd = (List.range' (skeletonOrder I) I.weights.sum).map (seen I G) := by
      calc
        _ = bs.flatMap (fun p => (List.range' p.1 p.2).map (seen I G)) := by
          simp [rows, List.flatMap_map,record]
        _ = (bs.flatMap (fun p => List.range' p.1 p.2)).map (seen I G) := by rw [List.map_flatMap]
        _ = _ := by rw [block_ranges]
    rw [observed,E,observed_count _ _ r (rootAdj I G r)]
    · exact item_quota I G hv contains hp deg r
    · intro x hx
      obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hx
      exact ⟨seen_sound _ _ _ _,seen_complete _ _ contains hp _ (by omega) (by unfold order; rw [source_order]; omega) r⟩

theorem source_converse (I : Instance) (hv : Valid I) (G : Graph (sourceTable I).length)
    (deg : G.Realizes (sourceTable I)) (contains : Contains I G) (hp : G.Planar) : ThreePartition I :=
  source_converse_k5free I hv G deg contains hp.1

end Recognition.SourceConverse
