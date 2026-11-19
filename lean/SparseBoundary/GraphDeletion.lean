import SparseBoundary.GraphEncoding

namespace SparseBoundary.Graph

private theorem adj_partial {n m : Nat} (G : Graph n) (f : Fin m → Fin n) (x : Fin m) :
    (G.restrict f).adj x = fun y => G.adj (f x) (f y) := funext (restrict_adj G f x)

private theorem restrict_conn {n m : Nat} (G : Graph n) (f : Fin m → Fin n)
    (l : List (Fin m)) : (G.restrict f).connected l = G.connected (l.map f) := by
  match l with
  | [] | [_] => rfl
  | a :: b :: t =>
    simp only [connected, List.map_cons, List.any_cons, List.any_map,
      adj_partial, restrict_conn G f (b :: t), Function.comp_def]

private theorem map_disjoint {n m : Nat} {f : Fin m → Fin n}
    (hf : ∀ x y, f x = f y → x = y) (s t : List (Fin m)) :
    disjoint (s.map f) (t.map f) = disjoint s t := by
  apply Bool.eq_iff_iff.mpr
  simp only [disjoint, List.all_eq_true, List.mem_map, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map]
  constructor
  · intro h x hx hxt
    exact h (f x) ⟨x,hx,rfl⟩ ⟨x,hxt,rfl⟩
  · rintro h _ ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    exact h x hx (hf y x he ▸ hy)

private theorem restrict_links {n m : Nat} (G : Graph n) (f : Fin m → Fin n)
    (s t : List (Fin m)) :
    links (G.restrict f) s t = links G (s.map f) (t.map f) := by
  simp [links, List.any_map, Function.comp_def, adj_partial]

private theorem model_map {n m k : Nat} (G : Graph n) (f : Fin m → Fin n)
    (hf : ∀ x y, f x = f y → x = y) (R : Fin k → Fin k → Bool)
    (bags : Fin k → List (Fin m)) :
    minorTest (G.restrict f) R bags = minorTest G R (fun i => (bags i).map f) := by
  simp only [minorTest, restrict_conn, restrict_links, map_disjoint hf]

theorem planar_restrict {n m : Nat} {G : Graph n} (hp : G.Planar)
    (f : Fin m → Fin n) (hf : ∀ x y, f x = f y → x = y) :
    (G.restrict f).Planar := by
  constructor
  · rintro ⟨bags, h⟩
    exact hp.1 ⟨_, (model_map G f hf clique5 bags) ▸ h⟩
  · rintro ⟨bags, h⟩
    exact hp.2 ⟨_, (model_map G f hf biclique33 bags) ▸ h⟩

/-- Deletion of the last labelled vertex, including the exact loss of
    degree at each surviving vertex. -/
theorem degree_delete_last {n : Nat} (G : Graph (n+1)) (i : Fin n) :
    G.degree i.castSucc = (G.restrict Fin.castSucc).degree i +
        (if G.adj i.castSucc (Fin.last n) then 1 else 0) := by
  simp only [degree]
  rw [List.finRange_succ_last]
  rw [List.filter_append]
  simp only [List.filter_map, List.length_append, List.length_map, adj_partial,
    Function.comp_def]
  cases h : G.adj i.castSucc (Fin.last n) <;> simp [h]

/-- A vertex attaining the order-minus-one bound sees all other vertices. -/
theorem root_universal {n : Nat} {G : Graph (n+1)} (h : G.degree 0 = n)
    (x : Fin n) : G.adj 0 x.succ = true := by
  simp only [degree, List.finRange_succ, List.filter_cons, adj_self,
    Bool.false_eq_true, ite_false, List.filter_map, List.length_map] at h
  apply List.length_filter_eq_length_iff.mp (h.trans List.length_finRange.symm) x
  exact List.mem_finRange x

/-- Once a leaf has a prescribed neighbour its other incidences vanish. -/
theorem leaf_only_root {n : Nat} {G : Graph (n+1)} (v : Fin (n+1))
    (hd : G.degree v = 1) (hv : G.adj v 0 = true)
    (x : Fin n) : G.adj v x.succ = false := by
  simp only [degree, List.finRange_succ, List.filter_cons, hv, ite_true,
    List.length_cons, List.filter_map, List.length_map] at hd
  have hempty : (List.finRange n).filter (G.adj v ∘ Fin.succ) = [] :=
    List.length_eq_zero_iff.mp (by omega)
  have hh := List.filter_eq_nil_iff.mp hempty x (List.mem_finRange x)
  change ¬G.adj v x.succ = true at hh
  cases he : G.adj v x.succ <;> simp_all

theorem planaric_on_labels {d : List Nat} {n : Nat} (hn : d.length = n) :
    Planaric d ↔ ∃ G : Graph n, G.Planar ∧ ∀ i : Fin n,
      G.degree i = d[i.val]'(by omega) := by
  subst n
  exact ⟨fun ⟨G,hd,hp⟩ => ⟨G,hp,hd⟩, fun ⟨G,hp,hd⟩ => ⟨G,hd,hp⟩⟩

/-- Removing a leaf from a profile with a universal first vertex. Any
    realizing graph has the required leaf edge, and induced subgraphs
    preserve Wagner planarity. -/
theorem remove_forced_leaf (t : List Nat) :
    Planaric ((t.length + 1) :: (t ++ [1])) → Planaric (t.length :: t) := by
  intro h
  obtain ⟨G,hp,hd⟩ := (planaric_on_labels (n := t.length + 2) (by simp)).mp h
  apply (planaric_on_labels (n := t.length + 1) (by simp)).mpr
  refine ⟨G.restrict Fin.castSucc, planar_restrict hp _ (fun x y e => Fin.ext (congrArg (fun z : Fin (t.length+2) => z.val) e)), ?_⟩
  have hd0 := hd 0
  simp at hd0
  have hlast := hd (Fin.last (t.length+1))
  simp [List.getElem_append_right (Nat.le_refl _)] at hlast
  have hlink : G.adj 0 (Fin.last (t.length+1)) = true :=
    root_universal hd0 (Fin.last t.length)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have he := degree_delete_last G (0 : Fin (t.length+1))
    change G.degree 0 = _ + (if G.adj 0 _ then 1 else 0) at he
    simp [hlink] at he
    simpa using (show (G.restrict Fin.castSucc).degree 0 = t.length by omega)
  · have hz := leaf_only_root _ hlast ((adj_comm G _ _) ▸ hlink) j.castSucc
    have he := degree_delete_last G j.succ
    have hn : G.adj j.succ.castSucc (Fin.last (t.length+1)) = false :=
      (adj_comm G _ _).trans hz
    rw [hn] at he
    have hh := hd j.succ.castSucc
    simpa [List.getElem_append_left j.isLt] using (he.symm.trans hh)

/-- Simultaneous removal of any number of leaves forced onto the
    universal first vertex. -/
theorem strip_forced_leaves (t : List Nat) (l : Nat) :
    Planaric ((t.length+l) :: (t ++ List.replicate l 1)) → Planaric (t.length :: t) := by
  induction l with
  | zero => simp
  | succ l ih =>
    intro h
    apply ih
    have hdel := remove_forced_leaf (t ++ List.replicate l 1)
    simp only [List.length_append,List.length_replicate,List.append_assoc] at hdel
    apply hdel
    simpa only [List.replicate_succ',Nat.add_succ] using h

end SparseBoundary.Graph
