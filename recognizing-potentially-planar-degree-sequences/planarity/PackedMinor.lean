import LeanPool.K5MinorFreeChoosability.Wagner.WagnerA
import SparseBoundary.GraphSubdivision
/-! Adapter between finite packed graphs and the branch-set minor predicates
in the combinatorial proof of Wagner's theorem. -/
namespace Recognition.Wagner
open SparseBoundary LeanPool.K5MinorFreeChoosability

def toSimple {n : Nat} (G : Graph n) : SimpleGraph (Fin n) where
  Adj i j := G.adj i j = true
  symm := ⟨fun i j h => (G.adj_comm i j) ▸ h⟩
  loopless := ⟨fun x h => by simp at h⟩

@[simp] theorem toSimple_adj {n : Nat} (G : Graph n) (x y : Fin n) :
    (toSimple G).Adj x y ↔ G.adj x y = true := Iff.rfl

private theorem add_vertex {n : Nat} (G : Graph n) {xs : List (Fin n)} {v w : Fin n}
    (hxs : G.connected xs) (hv : v ∈ xs) (adj : G.adj v w) : G.connected (w::xs) := by
  cases xs with
  | nil => contradiction
  | cons a xs =>
    exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨v,hv,(G.adj_comm v w) ▸ adj⟩,hxs⟩

private theorem growPath {n : Nat} (G : Graph n) {S : Finset (Fin n)} {r w : Fin n}
    (p : RIn (toSimple G) (S : Set (Fin n)) r w) (xs : List (Fin n))
    (connected : G.connected xs) (seed : r ∈ xs) (inside : ∀ v ∈ xs, v ∈ S) :
    ∃ ys, G.connected ys ∧ w ∈ ys ∧ xs ⊆ ys ∧ ∀ v ∈ ys, v ∈ S := by
  induction p with
  | refl => exact ⟨xs,connected,seed,fun _ h => h,inside⟩
  | @tail a b _ edge ih =>
    obtain ⟨ys,conn,ha,inc,valid⟩ := ih
    refine ⟨b::ys,add_vertex G conn ha edge.1,by simp,fun _ h => List.mem_cons_of_mem _ (inc h),?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl|h
    · exact edge.2.2
    · exact valid _ h

/-- Recover a reverse connected-construction order for each upstream
finite branch set. Repeated names are permitted by the packed certificate. -/
theorem bag_list {n : Nat} (G : Graph n) (S : Finset (Fin n))
    (hs : ConnSet (toSimple G) (S : Set (Fin n))) :
    ∃ xs, G.connected xs ∧ ∀ v, v ∈ xs ↔ v ∈ S := by
  obtain ⟨r,hr⟩ := hs.1
  have grow (todo : List (Fin n)) (valid : ∀ z ∈ todo, z ∈ S) :
      ∃ xs, G.connected xs ∧ r ∈ xs ∧ todo ⊆ xs ∧ ∀ v ∈ xs, v ∈ S := by
    induction todo with
    | nil => exact ⟨[r],rfl,by simp,by simp,by simpa using hr⟩
    | cons a todo ih =>
      obtain ⟨xs,conn,seed,done,inside⟩ := ih (fun z hz => valid z (List.mem_cons_of_mem _ hz))
      have path := hs.2 r hr a (valid _ (by simp))
      obtain ⟨ys,conn',ha,inc,inside'⟩ := growPath G path xs conn seed inside
      refine ⟨ys,conn',inc seed,?_,inside'⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl|hv
      · exact ha
      · exact inc (done hv)
  obtain ⟨xs,conn,_,inc,inside⟩ := grow S.toList (by simp)
  exact ⟨xs,conn,fun x => ⟨inside x,fun h => inc (by simpa using h)⟩⟩

/-- Translate any finite minor model after assigning packed labels to the
vertices of the pattern graph. -/
theorem packed_model {n k : Nat} {W : Type} (G : Graph n) (H : SimpleGraph W)
    (R : Fin k → Fin k → Bool) (name : Fin k → W) (inj : Function.Injective name)
    (required : ∀ i j, R i j → H.Adj (name i) (name j)) (M : MinorModel (toSimple G) H) :
    ∃ bags, G.minorTest R bags = true := by
  classical
  let witness := fun i => bag_list G (M.branch (name i)) (M.connSet _)
  let bags := fun i => (witness i).choose
  have conn i : G.connected (bags i) := (witness i).choose_spec.1
  have mem i x : x ∈ bags i ↔ x ∈ M.branch (name i) := (witness i).choose_spec.2 x
  refine ⟨bags, List.all_eq_true.mpr (fun i _ => Bool.and_eq_true_iff.mpr ⟨conn i,?_⟩)⟩
  apply List.all_eq_true.mpr
  intro j _
  apply Bool.and_eq_true_iff.mpr
  constructor
  · by_cases h : i=j
    · simp [h]
    · apply Bool.or_eq_true_iff.mpr
      right
      apply List.all_eq_true.mpr
      intro a ha
      have dis := Finset.disjoint_left.mp (M.branch_disjoint _ _ (inj.ne h)) ((mem _ _).mp ha)
      simpa using (fun hb => dis ((mem _ _).mp hb) : a ∉ bags j)
  · by_cases h : R i j
    · obtain ⟨a,ha,b,hb,hab⟩ := M.branch_adjacent _ _ (required i j h)
      apply Bool.or_eq_true_iff.mpr
      right
      exact List.any_eq_true.mpr ⟨a,(mem _ _).mpr ha,List.any_eq_true.mpr ⟨b,(mem _ _).mpr hb,hab⟩⟩
    · simp [h]

private def side (i : Fin 6) : Fin 3 ⊕ Fin 3 :=
  if h : i.val < 3 then Sum.inl ⟨i.val,h⟩ else Sum.inr ⟨i.val-3,by omega⟩

private theorem side_inj : Function.Injective side := by
  intro i j h
  apply Fin.ext
  unfold side at h
  split at h <;> split at h <;> simp [Fin.ext_iff] at h <;> omega

private theorem side_adjacency (i j : Fin 6) : Graph.biclique33 i j = true ↔ K33.Adj (side i) (side j) := by
  simp only [side,Graph.biclique33]
  split <;> split <;> simp_all [K33,completeBipartiteGraph]

theorem clique_minor_free {n : Nat} (G : Graph n) (p : G.Planar) : CliqueMinorFree (toSimple G) 5 := by
  rintro ⟨M⟩
  exact p.1 (packed_model G _ Graph.clique5 id Function.injective_id
    (fun i j h => by simpa [Graph.clique5] using h) M.toMinorModel)

theorem k33_minor_free {n : Nat} (G : Graph n) (p : G.Planar) : K33MinorFree (toSimple G) := by
  rintro ⟨M⟩
  exact p.2 (packed_model G K33 Graph.biclique33 side side_inj
    (fun i j => (side_adjacency i j).mp) M)

/-- Reverse conversion takes the underlying finite set of each packed bag. -/
private theorem conn_of_list {n : Nat} (G : Graph n) (xs : List (Fin n)) (h : G.connected xs) :
    ConnSet (toSimple G) (xs.toFinset : Set (Fin n)) := by
  match xs with
  | [] => contradiction
  | [a] => simpa using connSet_singleton (toSimple G) a
  | a::b::xs =>
    obtain ⟨link,rest⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨x,hx,e⟩ := List.any_eq_true.mp link
    have ih := conn_of_list G (b::xs) rest
    have add := ih.insert_adj (b := x) (by simpa using hx) (a := a) (show (toSimple G).Adj a x from e)
    simpa using add

private theorem abstract_model {n k : Nat} {W : Type} (G : Graph n) (H : SimpleGraph W)
    (R : Fin k → Fin k → Bool) (label : W → Fin k) (inj : Function.Injective label)
    (required : ∀ i j, H.Adj i j → R (label i) (label j) = true)
    (bags : Fin k → List (Fin n)) (given : G.minorTest R bags) :
    Nonempty (MinorModel (toSimple G) H) := by
  classical
  obtain ⟨conn,dis,link⟩ := Graph.bag_data given
  let br (u) := (bags (label u)).toFinset
  have hc u : ConnSet (toSimple G) (br u : Set (Fin n)) := conn_of_list G _ (conn _)
  refine ⟨{
    branch := br
    branch_nonempty := fun i => (hc i).1
    branch_connected := fun i => (connSet_iff_induce_connected _ _).mp (hc i)
    branch_disjoint := ?_
    branch_adjacent := ?_ }⟩
  · intro a b ne
    apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    exact dis _ _ (inj.ne ne) x (List.mem_toFinset.mp hx₁) (List.mem_toFinset.mp hx₂)
  · intro a b h
    obtain ⟨u,hu,v,hv,e⟩ := link _ _ (required a b h)
    exact ⟨u,List.mem_toFinset.mpr hu,v,List.mem_toFinset.mpr hv,e⟩

private def sideLabel : Fin 3 ⊕ Fin 3 → Fin 6
  | Sum.inl i => ⟨i.val, by omega⟩
  | Sum.inr i => ⟨i.val+3, by omega⟩

private theorem label_side : ∀ x, side (sideLabel x) = x := by decide

theorem planar_iff_rotation {n : Nat} (G : Graph n) :
    G.Planar ↔ IsPlanar (toSimple G) := by
  constructor
  · intro p
    exact isPlanar_of_k5MinorFree_of_k33MinorFree _ (clique_minor_free G p) (k33_minor_free G p)
  · intro h
    obtain ⟨c₅,c₃₃⟩ := (isPlanar_iff_k5MinorFree_and_k33MinorFree _).mp h
    constructor
    · rintro ⟨b,hb⟩
      obtain ⟨M⟩ := abstract_model G (⊤ : SimpleGraph (Fin 5)) Graph.clique5 id
        Function.injective_id (fun i j h => by simpa [Graph.clique5] using h) b hb
      exact c₅ ⟨M.toCliqueMinorModel⟩
    · rintro ⟨b,hb⟩
      have inj : Function.Injective sideLabel := fun a b e => by simpa [label_side] using congrArg side e
      exact c₃₃ (abstract_model G K33 Graph.biclique33 sideLabel inj (fun i j edge =>
        (side_adjacency _ _).mpr (by simpa [label_side] using edge)) b hb)

end Recognition.Wagner
