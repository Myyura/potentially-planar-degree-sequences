import SparseBoundary.Cut

namespace SparseBoundary.Graph

private theorem simple_bag (G : Graph n) (s : List (Fin n)) (hc : G.connected s=true) :
    ∃ b, b.Nodup ∧ G.connected b=true ∧ ∀ x, x∈b ↔ x∈s := by
  match s with
  | [] => simp [connected] at hc
  | [x] => exact ⟨[x],by simp,rfl,fun _ => Iff.rfl⟩
  | x::y::s =>
    obtain ⟨he,hs⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨b,hn,hb,hm⟩ := simple_bag G (y::s) hs
    by_cases hx : x∈b
    · refine ⟨b,hn,hb,?_⟩
      intro z; rw [List.mem_cons]; constructor
      · exact fun h => .inr ((hm _).mp h)
      · rintro (rfl|he)
        · exact hx
        · exact (hm _).mpr he
    · refine ⟨x::b,by simp [hx,hn],?_,by intro z; simp only [List.mem_cons,hm]⟩
      obtain ⟨w,hw,hedge⟩ := List.any_eq_true.mp he
      have hw' := (hm _).mpr hw
      cases b with
      | nil => simp at hw'
      | cons z b => exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨w,hw',hedge⟩,hb⟩

private theorem internal_connected (G : Graph n) (s : List (Fin n)) (hc : G.connected s=true) :
    2*s.length ≤ G.arcs s s+2 := by
  match s with
  | [] => simp
  | [v] => simp [arcs,neighboursIn]
  | v::w::s =>
    obtain ⟨he,hs⟩ := Bool.and_eq_true_iff.mp hc
    have ih := internal_connected G (w::s) hs
    obtain ⟨x,hx,hadj⟩ := List.any_eq_true.mp he
    have hp : 0<G.arcs [v] (w::s) := by
      have hmem : x∈(w::s).filter (G.adj v) := List.mem_filter.mpr ⟨hx,hadj⟩
      simpa [arcs,neighboursIn] using List.length_pos_of_mem hmem
    change 2*(([v]++(w::s)).length) ≤ G.arcs ([v]++(w::s)) ([v]++(w::s))+2
    simp only [List.length_append,List.length_singleton,arcs_append_left,arcs_append_right,
      G.arcs_symm (w::s) [v]]
    omega

private theorem map_sum_le (s : List α) (f g : α → Nat) (h : ∀ x ∈ s, f x ≤ g x) :
    (s.map f).sum ≤ (s.map g).sum := by
  induction s with
  | nil => exact Nat.le_refl _
  | cons x s ih =>
    exact Nat.add_le_add (h _ (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-- A connected bag meeting k distinct adjacent vertices outside it spends
    at least 2(|B|-1)+k degree incidences. -/
theorem branch_degree_bound {G : Graph n} {B T : List (Fin n)}
    (hc : G.connected B=true) (hn : (B++T).Nodup)
    (touch : ∀ y∈T, ∃ x∈B, G.adj y x=true) :
    2*B.length + T.length ≤ (B.map G.degree).sum+2 := by
  have cores := internal_connected G B hc
  have deg : G.arcs B (B++T) ≤ (B.map G.degree).sum := by
    apply map_sum_le
    intro x _
    apply List.Nodup.length_le_of_subset (hn.filter _)
    intro y hy; exact List.mem_filter.mpr ⟨List.mem_finRange _,(List.mem_filter.mp hy).2⟩
  have hb : T.length ≤ G.arcs T B := by
    have le := map_sum_le T (fun _ => 1) (fun y => G.neighboursIn y B) (by
      intro y hy
      obtain ⟨x,hx,he⟩ := touch y hy
      exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hx,he⟩))
    simpa [List.map_const',List.sum_replicate_nat,arcs] using le
  rw [arcs_append_right,G.arcs_symm B T] at deg
  omega

private theorem choose_targets {G : Graph n} {R : Fin k → Fin k → Bool} {bags}
    (hm : G.minorTest R bags=true) (i : Fin k) (T : List (Fin k)) (ht : T.Nodup)
    (no : i∉T) (required : ∀ j∈T, R i j=true) :
    ∃ B V, B.Nodup ∧ G.connected B=true ∧ (∀ x,x∈B ↔ x∈bags i) ∧
      (B++V).Nodup ∧ V.length=T.length ∧ ∀ y∈V, ∃ x∈B, G.adj y x=true := by
  classical
  have row (a : Fin k) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hm a (List.mem_finRange a))
  have cell (a b : Fin k) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (row a).2 b (List.mem_finRange b))
  have dis {a b : Fin k} (h : a≠b) {x} (hx : x∈bags a) : x∉bags b := by
    have e : disjoint (bags a) (bags b)=true := by simpa [h] using (cell a b).1
    simpa using List.all_eq_true.mp e x hx
  obtain ⟨B,hn,hc,hB⟩ := simple_bag G (bags i) (row i).1
  have pick (j : Fin k) (hj : j∈T) : ∃ y∈bags j, ∃ x∈B, G.adj y x=true := by
    have hl : G.links (bags i) (bags j)=true := by simpa [required j hj] using (cell i j).2
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hl
    obtain ⟨y,hy,hadj⟩ := List.any_eq_true.mp he
    exact ⟨y,hy,x,(hB _).mpr hx,(G.adj_comm _ _).trans hadj⟩
  let f (j : Fin k) := if hj : j∈T then (pick j hj).choose else (B.head (by
    intro e; rw [e] at hc; contradiction))
  have spec (j) (hj : j∈T) : f j∈bags j ∧ ∃ x∈B, G.adj (f j) x=true := by
    simpa [f,hj] using (pick j hj).choose_spec
  refine ⟨B,T.map f,hn,hc,hB,?_,by simp,?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨hn,?_,?_⟩
    · apply List.pairwise_map.mpr
      apply ht.imp_of_mem
      intro a b ha hb hab he
      exact dis hab (spec a ha).1 (he ▸ (spec b hb).1)
    · intro x hx y hy eq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
      exact dis (a:=i) (b:=j) (fun hij => no (hij.symm ▸ hj)) ((hB _).mp hx) (eq ▸ (spec j hj).1)
  · intro y hy; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy; exact (spec j hj).2

/-- For a forbidden-minor model, every branch set with three different
    neighboring sets contains a vertex of the original graph of degree at
    least three. The labels are unrestricted. -/
theorem high_in_bag {G : Graph n} {R : Fin k → Fin k → Bool} {bags}
    (hm : G.minorTest R bags=true) (i : Fin k) (T : List (Fin k)) (hn : T.Nodup)
    (no : i∉T) (required : ∀ j∈T,R i j=true) (ht : 3≤T.length) :
    ∃ x∈bags i, 3≤G.degree x := by
  obtain ⟨B,V,_,hc,hB,hn,len,touch⟩ := choose_targets hm i T hn no required
  have bound := branch_degree_bound hc hn touch
  apply Classical.byContradiction
  intro h
  have upper := map_sum_le B G.degree (fun _ => 2) (by
    intro x hx; have he : ¬ 3≤G.degree x := fun hh => h ⟨x,(hB x).mp hx,hh⟩; omega)
  simp [List.map_const',List.sum_replicate_nat] at upper
  omega

private theorem disjoint_model {G : Graph n} {R : Fin k → Fin k → Bool} {s}
    (hm : G.minorTest R s=true) {i j} (hne : i≠j) (v) (hi : v∈s i) (hj : v∈s j) : False := by
  have row := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hm i (List.mem_finRange i))).2
  have hh := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp row j (List.mem_finRange j))).1
  have hd : disjoint (s i) (s j)=true := by simpa [hne] using hh
  have e := List.all_eq_true.mp hd v hi
  simp [hj] at e

private theorem count_model {G : Graph n} {R : Fin k → Fin k → Bool} {s}
    (hm : G.minorTest R s=true) (P : Fin n → Bool) (found : ∀ i, ∃ x∈s i,P x=true) :
    k ≤ ((List.finRange n).filter P).length := by
  classical
  let f (i : Fin k) := (found i).choose
  have inside i : f i ∈ s i ∧ P (f i)=true := (found i).choose_spec
  have hn : ((List.finRange k).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange k).imp
    intro i j ne (eq : f i = f j)
    exact disjoint_model hm ne _ (inside i).1 (eq ▸ (inside j).1)
  have le := hn.length_le_of_subset (l₂ := (List.finRange n).filter P) (by
    rintro _ hh
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hh
    exact List.mem_filter.mpr ⟨List.mem_finRange _,(inside i).2⟩)
  simpa using le

private def neighborsOf (R : Fin k → Fin k → Bool) (i : Fin k) := (List.finRange k).filter (R i)

private theorem high_count {G : Graph n} {R : Fin k → Fin k → Bool} {s}
    (hm : G.minorTest R s=true) (irr : ∀ i,R i i=false) (min : ∀ i, 3 ≤ (neighborsOf R i).length) :
    k ≤ ((List.finRange n).filter (fun x => decide (3≤G.degree x))).length := by
  apply count_model hm
  intro i
  have got := high_in_bag hm i (neighborsOf R i) ((List.nodup_finRange k).filter _)
    (by simp [neighborsOf,irr]) (fun j hj => (List.mem_filter.mp hj).2) (min i)
  simpa using got

/-- With at most four vertices of degree at least three, every realization
    is planar, independently of the degree-sum boundary. -/
theorem planar_of_few_high (G : Graph n)
    (few : ((List.finRange n).filter (fun x => decide (3≤G.degree x))).length ≤ 4) : G.Planar := by
  constructor
  · rintro ⟨s,h⟩
    have le := high_count h (by decide) (by decide)
    omega
  · rintro ⟨s,h⟩
    have le := high_count h (by decide) (by decide)
    omega

/-- At most five high vertices, of which at most four have degree at
    least four, rule out both forbidden minors. -/
theorem planar_of_five_with_three (G : Graph n)
    (few : ((List.finRange n).filter (fun x => decide (3≤G.degree x))).length ≤ 5)
    (four : ((List.finRange n).filter (fun x => decide (4≤G.degree x))).length ≤ 4) : G.Planar := by
  let P := fun x => decide (3≤G.degree x)
  constructor
  · rintro ⟨s,hm⟩
    have per (i : Fin 5) : ∃ x∈s i, 3≤G.degree x := by
      apply high_in_bag hm i (neighborsOf clique5 i) ((List.nodup_finRange 5).filter _)
        (by simp [neighborsOf,clique5]) (fun j hj => (List.mem_filter.mp hj).2)
      revert i; decide
    let f (i : Fin 5) := (per i).choose
    have spec i : f i∈s i ∧ 3≤G.degree (f i) := (per i).choose_spec
    have inj {i j} (h : f i=f j) : i=j := Classical.byContradiction fun ne =>
      disjoint_model hm ne _ (spec i).1 (h ▸ (spec j).1)
    let L := (List.finRange 5).map f
    have hn : L.Nodup := List.pairwise_map.mpr ((List.nodup_finRange 5).imp fun ne h => ne (inj h))
    have subset : L ⊆ (List.finRange n).filter P := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact List.mem_filter.mpr ⟨List.mem_finRange _,by simpa [P] using (spec i).2⟩
    have allhigh (x) (hx : 3≤G.degree x) : x∈L := by
      apply Classical.byContradiction; intro no
      have H : (x::L).Nodup := List.nodup_cons.mpr ⟨no,hn⟩
      have le := H.length_le_of_subset (l₂ := (List.finRange n).filter P) (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl|hy
        · exact List.mem_filter.mpr ⟨List.mem_finRange _,by simpa [P] using hx⟩
        · exact subset hy)
      simp [L,P] at le
      omega
    have alone i x (hx : x∈s i) (hg : 3≤G.degree x) : x=f i := by
      obtain ⟨j,_,eq⟩ := List.mem_map.mp (allhigh x hg)
      have same : i=j := Classical.byContradiction fun ne => disjoint_model hm ne x hx (eq ▸ (spec j).1)
      exact same ▸ eq.symm
    have allfour (i : Fin 5) : 4≤G.degree (f i) := by
      let T := neighborsOf clique5 i
      have len : T.length=4 := (by decide : ∀ z, (neighborsOf clique5 z).length=4) i
      obtain ⟨B,V,hn,hc,hB,hnV,lenV,touch⟩ := choose_targets hm i T ((List.nodup_finRange 5).filter _)
        (by simp [T,neighborsOf,clique5]) (fun j hj => (List.mem_filter.mp hj).2)
      have bound := branch_degree_bound hc hnV touch
      have fi : f i ∈ B := (hB _).mpr (spec i).1
      have perm := List.perm_cons_erase fi
      have hi := (perm.map G.degree).sum_nat
      have hlen := perm.length_eq
      have upper := map_sum_le (B.erase (f i)) G.degree (fun _ => 2) (by
        intro x hx
        have low : ¬ 3≤G.degree x := fun hg =>
          hn.not_mem_erase (alone i x ((hB _).mp (List.mem_of_mem_erase hx)) hg ▸ hx)
        omega)
      simp only [List.map_cons,List.sum_cons] at hi
      simp only [List.length_cons] at hlen
      simp [List.map_const',List.sum_replicate_nat] at upper
      omega
    have le := count_model hm (fun x => decide (4≤G.degree x)) (fun i =>
      ⟨f i,(spec i).1,by simpa using allfour i⟩)
    omega
  · rintro ⟨s,h⟩
    have le := high_count h (by decide) (by decide)
    omega

end SparseBoundary.Graph

namespace SparseBoundary

/-- The small-core positive classification applies to actual degree lists
    with arbitrarily many leaves and degree-two vertices. -/
theorem planaric_of_small_core {d : List Nat} (hg : Graphic d)
    (few : (d.filter (fun a => decide (3≤a))).length ≤ 5)
    (four : (d.filter (fun a => decide (4≤a))).length ≤ 4) : Planaric d := by
  obtain ⟨G,hd⟩ := hg
  have cut (j) : ((List.finRange d.length).filter (fun x => decide (j≤G.degree x))).length =
       (d.filter (fun a => decide (j≤a))).length := by
    conv => rhs; rw [← Graph.degrees_of_realization hd, List.filter_map, List.length_map]
    rfl
  exact ⟨G,hd,Graph.planar_of_five_with_three G (by rwa [cut]) (by rwa [cut])⟩

end SparseBoundary
