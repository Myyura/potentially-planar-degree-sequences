import SparseBoundary.GraphUnion

/-! The cyclic allocation in the three-connectivity promise. -/
namespace Recognition.Connectivity
open SparseBoundary SparseBoundary.Graph

private def word {b : Nat} (hb : 0 < b) (start k : Nat) : List (Fin b) :=
  (List.range' start k).map fun x => ⟨x % b, Nat.mod_lt _ hb⟩

private theorem word_append {b : Nat} (hb : 0 < b) (start p q : Nat) :
    word hb start p ++ word hb (start+p) q = word hb start (p+q) := by
  unfold word
  rw [← List.map_append,List.range'_append_1]

private theorem word_nodup {b : Nat} (hb : 0<b) (start k : Nat) (hk : k≤b) :
    (word hb start k).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  simp [word] at hi hj
  have he := congrArg Fin.val eq
  simp [word] at he
  obtain ⟨x,y,e⟩ := Nat.mod_eq_mod_iff.mp he
  have e' : i + x*b = j + y*b := by omega
  have m := Nat.mod_eq_mod_iff.mpr ⟨x,y,e'⟩
  rwa [Nat.mod_eq_of_lt (by omega : i<b), Nat.mod_eq_of_lt (by omega : j<b)] at m

private theorem full_turn {b : Nat} (hb : 0<b) (q : Nat) :
    word hb (q*b) b = List.finRange b := by
  apply List.ext_getElem
  · simp [word]
  · intro i hi _
    apply Fin.ext
    simp [word] at hi
    simp [word, Nat.mod_eq_of_lt hi]

private def makeRows {b : Nat} (hb : 0<b) (start : Nat) : List Nat → List (List (Fin b))
  | [] => []
  | d::ds => word hb start d :: makeRows hb (start+d) ds

private theorem rows_sizes {b : Nat} (hb : 0<b) (start : Nat) (ds : List Nat) :
    (makeRows hb start ds).map List.length = ds := by
  induction ds generalizing start with
  | nil => rfl
  | cons d ds ih => simp [makeRows,word,ih]

private theorem rows_flatten {b : Nat} (hb : 0<b) (start : Nat) (ds : List Nat) :
    (makeRows hb start ds).flatten = word hb start ds.sum := by
  induction ds generalizing start with
  | nil => rfl
  | cons d ds ih => simp [makeRows, ih, word_append]

private theorem rows_nodup {b : Nat} (hb : 0<b) (ds : List Nat) (start : Nat)
    (bound : ∀ d ∈ ds, d ≤ b) : ∀ r ∈ makeRows hb start ds, r.Nodup := by
  induction ds generalizing start with
  | nil => simp [makeRows]
  | cons d ds ih =>
    intro r hr
    rcases List.mem_cons.mp hr with h|h
    · exact h ▸ word_nodup hb start d (bound d (by simp))
    · exact ih (start+d) (fun e he => bound _ (by simp [he])) r h

/-- Rows are labelled old vertices and columns are new vertices. Every row is
simple and has its requested size. Each column occurs in exactly three rows. -/
theorem cyclic_allocation (b : Nat) (hb : 0<b) (ds : List Nat)
    (bound : ∀ d ∈ ds, d≤b) (total : ds.sum = 3*b) :
    ∃ rows : List (List (Fin b)), rows.map List.length = ds ∧
      (∀ r ∈ rows, r.Nodup) ∧ ∀ j, (rows.filter (fun r => r.contains j)).length = 3 := by
  let rows := makeRows hb 0 ds
  have nd := rows_nodup hb ds 0 bound
  refine ⟨rows,rows_sizes ..,nd,?_⟩
  intro j
  have one := (List.nodup_finRange b).count_of_mem (List.mem_finRange j)
  have turns : rows.flatten = List.finRange b ++ List.finRange b ++ List.finRange b := by
    rw [show rows.flatten = word hb 0 ds.sum from rows_flatten ..,total,
      show 3*b = (b+b)+b by omega, ← word_append, ← word_append]
    simp only [Nat.zero_add]
    rw [show word hb 0 b = List.finRange b by simpa using full_turn hb 0]
    rw [show word hb b b = List.finRange b by simpa using full_turn hb 1,
        show word hb (b+b) b = List.finRange b by simpa [Nat.two_mul] using full_turn hb 2]
  have count := congrArg (List.count j) turns
  simp only [List.count_append,one] at count
  change rows.flatten.count j = 3 at count
  rw [← count]
  suffices aux : ∀ rs : List (List (Fin b)), (∀ r ∈ rs, r.Nodup) →
      (rs.filter (fun r => r.contains j)).length = rs.flatten.count j from aux rows nd
  intro rs
  induction rs with
  | nil => simp
  | cons r rs ih =>
    intro hn
    have htail := ih (fun v hv => hn _ (by simp [hv]))
    have h := hn r (by simp)
    by_cases mem : j∈r
    · simp [mem, h.count_of_mem mem,← htail, Nat.add_comm]
    · simpa [mem,List.count_eq_zero.mpr mem] using htail

/-- Connectivity after deleting a list of at most two vertices. Endpoints
and every intermediate vertex of the walk survive the deletion. -/
inductive Survives {α : Type} (E : α → α → Prop) (gone : List α) : α → α → Prop
  | stay (ok : a ∉ gone) : Survives E gone a a
  | step : Survives E gone a b → E b c → c ∉ gone → Survives E gone a c

def Robust {α : Type} (E : α → α → Prop) :=
  ∀ gone : List α, gone.length ≤ 2 → ∀ a b, a ∉ gone → b ∉ gone → Survives E gone a b

private theorem join {E : α → α → Prop} {gone : List α}
    (p : Survives E gone a b) (q : Survives E gone b c) : Survives E gone a c := by
  induction q with
  | stay => exact p
  | step _ e h ih => exact .step ih e h

private theorem reverse {E : α → α → Prop} (sym : ∀ a b, E a b → E b a) {gone : List α}
    (p : Survives E gone a b) (ha : a ∉ gone) : Survives E gone b a := by
  induction p with
  | stay => exact .stay ha
  | @step u v p e ok ih =>
    have hu : u ∉ gone := by cases p with | stay h => exact h | step _ _ h => exact h
    exact join (.step (.stay ok) (sym _ _ e) hu) ih

def incidence (E : α → α → Prop) (rows : α → List β) : Sum α β → Sum α β → Prop
  | .inl x,.inl y => E x y
  | .inl x,.inr j | .inr j,.inl x => j ∈ rows x
  | .inr _,.inr _ => False

private def oldVertex : Sum α β → Option α
  | .inl x => some x
  | .inr _ => none

private theorem old_survives {xs : List (Sum α β)} (x : α) :
    x ∈ xs.filterMap oldVertex ↔ Sum.inl x ∈ xs := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨v,h,e⟩
    cases v with
    | inl u => cases e; exact h
    | inr => cases e
  · exact fun h => ⟨.inl x,h,rfl⟩

theorem robust_extension {E : α → α → Prop} (sym : ∀ a b, E a b → E b a)
    (old : Robust E) (rows : α → List β)
    (three : ∀ j, ∃ ns : List α, ns.Nodup ∧ ns.length = 3 ∧ ∀ x ∈ ns, j ∈ rows x) :
    Robust (incidence E rows) := by
  intro gone short a b ha hb
  let del := gone.filterMap oldVertex
  have few : del.length ≤ 2 := Nat.le_trans (List.length_filterMap_le _ _) short
  have anchor (v : Sum α β) (ok : v ∉ gone) :
      ∃ x : α, x ∉ del ∧ Survives (incidence E rows) gone v (.inl x) := by
    cases v with
    | inl x => exact ⟨x,fun h => ok ((old_survives x).mp h),.stay ok⟩
    | inr j =>
      obtain ⟨ns,nd,len,linked⟩ := three j
      have existsOld : ∃ x∈ns, x ∉ del := by
        apply Classical.byContradiction
        intro h
        have sub : ns ⊆ del := fun x hx => Classical.byContradiction (fun hd => h ⟨x,hx,hd⟩)
        have := nd.length_le_of_subset sub
        omega
      obtain ⟨x,hx,alive⟩ := existsOld
      exact ⟨x,alive,.step (.stay ok) (linked x hx) (fun h => alive ((old_survives x).mpr h))⟩
  obtain ⟨x,hx,p⟩ := anchor a ha
  obtain ⟨y,hy,q⟩ := anchor b hb
  have path := old del few x y hx hy
  have lift : Survives (incidence E rows) gone (.inl x) (.inl y) := by
    clear q hy
    induction path with
    | stay ok => exact .stay (fun h => ok ((old_survives _).mpr h))
    | step _ edge ok ih => exact .step ih edge (fun h => ok ((old_survives _).mpr h))
  have sym' : ∀ a b, incidence E rows a b → incidence E rows b a := by
    intro u v
    cases u <;> cases v <;> first | exact sym _ _ | exact id
  exact join (join p lift) (reverse sym' q hb)

private theorem row_table (b : Nat) (hb : 0<b) (d : Fin n → Nat)
    (bound : ∀ i, d i ≤ b) (total : (List.ofFn d).sum = 3*b) :
    ∃ rs : Fin n → List (Fin b),
      (∀ i, (rs i).length = d i ∧ (rs i).Nodup) ∧
      ∀ j, ((List.finRange n).filter (fun i => (rs i).contains j)).length = 3 := by
  obtain ⟨rows,sz,nd,col⟩ := cyclic_allocation b hb (List.ofFn d)
    (fun v h => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h; exact bound i) total
  have len : rows.length = n := by simpa using congrArg List.length sz
  let rs (i : Fin n) := rows[i.val]'(by omega)
  refine ⟨rs,fun i => ⟨?_,nd _ (List.getElem_mem _)⟩,fun j => ?_⟩
  · have h := congrArg (fun s : List Nat => s[i.val]?) sz
    simpa [rs,List.getElem?_map,List.getElem?_eq_getElem (by omega : i.val < rows.length),
      List.getElem?_eq_getElem (by simp : i.val < (List.ofFn d).length)] using h
  · have same : (List.finRange n).map rs = rows := by
      apply List.ext_getElem
      · simp [len]
      · intros; simp [rs]
    have h := col j
    rw [← same,List.filter_map,List.length_map] at h
    exact h

private def combinedRel (G : Graph n) (rs : Fin n → List (Fin b)) :
    Fin (n+b) → Fin (n+b) → Bool :=
  Fin.addCases (fun i => Fin.addCases (G.adj i) (rs i).contains)
    (fun j => Fin.addCases (fun i => (rs i).contains j) (fun _ => false))

private def extended (G : Graph n) (rs : Fin n → List (Fin b)) := ofRelation (combinedRel G rs)

private theorem ext_adj (G : Graph n) (rs : Fin n → List (Fin b)) (u v : Fin (n+b)) :
    (extended G rs).adj u v = combinedRel G rs u v := by
  apply adj_ofRelation
  · intro u v
    refine Fin.addCases ?_ ?_ u <;> intro x <;> refine Fin.addCases ?_ ?_ v <;> intro y <;>
      simp [combinedRel,G.adj_comm]
  · intro u
    refine Fin.addCases ?_ ?_ u <;> intro x <;> simp [combinedRel]

private theorem extended_degrees (G : Graph n) (rs : Fin n → List (Fin b))
    (nd : ∀ i, (rs i).Nodup) :
    (∀ i, (extended G rs).degree (i.castAdd b) = G.degree i + (rs i).length) ∧
    (∀ j, (extended G rs).degree (j.natAdd n) =
      ((List.finRange n).filter (fun i => (rs i).contains j)).length) := by
  constructor
  · intro i
    have p : ((List.finRange b).filter (rs i).contains).Perm (rs i) := by
      apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange b).filter _) (nd i)).mpr
      simp
    unfold degree
    rw [union_range n b]
    simp only [List.filter_append,List.length_append,List.filter_map,List.length_map]
    change _ + _ = _ + _
    have plen := p.length_eq
    change ((List.finRange b).filter (fun j => (rs i).contains j)).length = _ at plen
    simpa [Function.comp_def,ext_adj,combinedRel] using congrArg (G.degree i + ·) plen
  · intro j
    unfold degree
    rw [union_range n b]
    simp [Function.comp_def, List.filter_map,ext_adj,combinedRel]

theorem robust_relabel {α β : Type} {E : α → α → Prop} {E' : β → β → Prop}
    (f : α → β) (g : β → α) (fg : ∀ y, f (g y) = y) (gf : ∀ x, g (f x) = x)
    (edge : ∀ x y, E x y → E' (f x) (f y)) (h : Robust E) : Robust E' := by
  intro gone short a b ha hb
  have ok (x : β) (hx : x ∉ gone) : g x ∉ gone.map g := by
    intro contra
    obtain ⟨y,hy,e⟩ := List.mem_map.mp contra
    have same : y=x := by simpa only [fg] using congrArg f e
    exact hx (same ▸ hy)
  have path := h (gone.map g) (by simpa using short) _ _ (ok a ha) (ok b hb)
  have down (x : α) (hx : x ∉ gone.map g) : f x ∉ gone := by
    intro mem
    exact hx (List.mem_map.mpr ⟨f x,mem,gf _⟩)
  have lift {x y : α} (p : Survives E (gone.map g) x y) :
      Survives E' gone (f x) (f y) := by
    induction p with
    | stay hw => exact .stay (down _ hw)
    | step _ he hw ih => exact .step ih (edge _ _ he) (down _ hw)
  simpa only [fg] using lift path

/-- A labelled realization of all demands, retaining all old adjacencies and
connectivity upon deletion of any two vertices. With n≥4 the connectivity
predicate is precisely three-connectivity. -/
theorem extend_graph (G : Graph n) (old : Robust (fun x y => G.adj x y = true))
    (b : Nat) (hb : 0<b) (d : Fin n → Nat) (bound : ∀ i, d i≤b)
    (total : (List.ofFn d).sum=3*b) :
    ∃ H : Graph (n+b), Robust (fun x y => H.adj x y = true) ∧
      (∀ i k : Fin n, H.adj (i.castAdd b) (k.castAdd b) = G.adj i k) ∧
      (∀ i : Fin n, H.degree (i.castAdd b) = G.degree i + d i) ∧
      (∀ j : Fin b, H.degree (j.natAdd n) = 3) := by
  obtain ⟨rs,rows,cols⟩ := row_table b hb d bound total
  have deg := extended_degrees G rs (fun i => (rows i).2)
  refine ⟨extended G rs,?_,fun i k => by simp [ext_adj,combinedRel],
    fun i => (deg.1 i).trans (by rw [(rows i).1]),fun j => (deg.2 j).trans (cols j)⟩
  have base := robust_extension (E := fun x y => G.adj x y = true)
    (fun x y h => (G.adj_comm x y) ▸ h) old rs (fun j =>
      ⟨(List.finRange n).filter (fun i => (rs i).contains j),
       (List.nodup_finRange n).filter _, cols j,
       fun i hi => List.contains_iff_mem.mp (List.mem_filter.mp hi).2⟩)
  apply robust_relabel (Sum.elim (Fin.castAdd b) (Fin.natAdd n))
    (Fin.addCases Sum.inl Sum.inr) _ _ _ base
  · intro y
    refine Fin.addCases ?_ ?_ y <;> intro i <;> simp
  · intro x
    cases x <;> simp
  · intro x y
    cases x <;> cases y <;> simp [incidence,ext_adj,combinedRel]

end Recognition.Connectivity
