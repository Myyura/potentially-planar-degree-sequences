import MinorWidth

/-! Find a low-width ordering without searching all permutations. The
future vertices touching the processed prefix depend only on its set. -/
namespace Recognition.LayoutSearch
open Finset StateIso MinorWidth

def boundary (A : Colored n) (S : Finset (Fin n)) :=
  univ.filter fun y => y∉S ∧ ∃ x∈S,A.edge x y=true ∨ A.edge y x=true

def initial (p : Equiv.Perm (Fin n)) (j : Fin n) := univ.filter fun x => p.symm x≤j

def Narrow (A : Colored n) (w : Nat) (p : Equiv.Perm (Fin n)) :=
  ∀ j,(boundary A (initial p j)).card≤w

/-- Order the hierarchy in reverse lexicographic order. Future boundary
vertices are ancestors of the last key in the processed prefix. -/
theorem narrow_hierarchy (A : Colored n) (D : Hierarchy A w) :
    ∃ p : Equiv.Perm (Fin n),Narrow A w p := by
  let key (i : Fin n) := OrderDual.toDual (D.home i)
  let p := Tuple.sort key
  have ordered {i j : Fin n} (le : i≤j) : D.home (p j) ≤ D.home (p i) := Tuple.monotone_sort key le
  refine ⟨p,fun j => (card_le_card (t := spine D.home (D.home (p j))) ?_).trans (D.cap _)⟩
  intro y hy
  obtain ⟨_,out,x,hx,adj⟩ := mem_filter.mp hy
  have a : p.symm x≤j := (mem_filter.mp hx).2
  have b : j<p.symm y := lt_of_not_ge (fun bad => out (mem_filter.mpr ⟨mem_univ _,bad⟩))
  have byj : D.home y ≤ D.home (p j) := by simpa using ordered b.le
  have jbx : D.home (p j) ≤ D.home x := by simpa using ordered a
  have cmp : D.home y <+: D.home x ∨ D.home x <+: D.home y := by
    rcases adj with h|h
    · exact (D.adjacent x y h).symm
    · exact D.adjacent y x h
  apply mem_filter.mpr ⟨mem_univ _,?_⟩
  apply (ancestor_prefix ..).mp
  rcases cmp with h|h
  · exact Outline.convex ((ancestor_prefix ..).mpr List.prefix_rfl) ((ancestor_prefix ..).mpr h) (List.not_lt.mp (not_lt.mpr byj)) (List.not_lt.mp (not_lt.mpr jbx))
  · have e := le_antisymm (byj.trans jbx) (le_of_not_gt (List.not_lt.mpr (Outline.isAncestor_le ((ancestor_prefix ..).mpr h))))
    have z := le_antisymm byj (e ▸ jbx)
    rw [z]; exact (ancestor_prefix ..).mpr List.prefix_rfl

/-- Orient each cut backwards to obtain nested later-neighbor bags. -/
def layout (A : Colored n) (p : Equiv.Perm (Fin n)) (h : Narrow A w p) : BagHom.Layout (relabel A p) w where
  later i := (boundary A (initial p i)).map p.symm.toEmbedding
  cap i := by simpa using h i
  edge i j e ne := by
    by_cases ord : i≤j
    · rw [ite_eq_left ord]
      exact mem_map.mpr ⟨p j,mem_filter.mpr ⟨mem_univ _,by simpa [initial] using (not_le.mpr (lt_of_le_of_ne ord ne)),p i,by simp [initial],Or.inl e⟩,p.symm_apply_apply _⟩
    · rw [ite_eq_right ord]
      exact mem_map.mpr ⟨p i,mem_filter.mpr ⟨mem_univ _,by simpa [initial] using ord,p j,by simp [initial],Or.inr e⟩,p.symm_apply_apply _⟩
  nested r i hi j hj ij := by
    obtain ⟨x,hx,locX⟩ := mem_map.mp hi
    obtain ⟨y,hy,locY⟩ := mem_map.mp hj
    obtain ⟨_,outside⟩ := mem_filter.mp hx
    have rLt : r<i := lt_of_not_ge (fun no => outside.1 (mem_filter.mpr ⟨mem_univ _,locX ▸ no⟩))
    obtain ⟨_,_,a,ha,adj⟩ := mem_filter.mp hy
    exact mem_map.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,
      fun no => ij.not_ge (locY ▸ (mem_filter.mp no).2),a,
      mem_filter.mpr ⟨mem_univ _,((mem_filter.mp ha).2).trans rLt.le⟩,adj⟩,locY⟩

inductive Route (A : Colored n) (w : Nat) : List (Fin n) → Prop
  | nil : Route A w []
  | extend {xs} (prior : Route A w xs) (x : Fin n) (fresh : x∉xs)
      (width : (boundary A (insert x xs.toFinset)).card≤w) : Route A w (xs++[x])

def subsets (n : Nat) : List (Finset (Fin n)) :=
  (List.finRange n).sublists.map List.toFinset

def grow (A : Colored n) (w : Nat) (xs : List (Fin n)) :=
  ((List.finRange n).filter fun x => decide (x∉xs ∧ (boundary A (insert x xs.toFinset)).card≤w)).map
    (fun x => xs++[x])

def keep (n : Nat) (cs : List (List (Fin n))) :=
  (subsets n).filterMap fun S => cs.find? (fun xs => xs.toFinset==S)

def pool (A : Colored n) (w : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | k+1 => keep n ((pool A w k).flatMap (grow A w))

private theorem all_subsets (S : Finset (Fin n)) : S∈subsets n := by
  let l := (List.finRange n).filter (fun x => decide (x∈S))
  have same : l.toFinset=S := by ext x; simp [l]
  exact List.mem_map.mpr ⟨l,List.mem_sublists.mpr (List.filter_sublist),same⟩

theorem pool_size (A : Colored n) (w k : Nat) : (pool A w k).length≤2^n := by
  cases k with
  | zero => exact Nat.one_le_two_pow
  | succ k => exact (List.length_filterMap_le ..).trans (by simp [subsets])

private theorem make_mem (A : Colored n) (w) (xs ys) : ys∈grow A w xs ↔
    ∃ x,x∉xs ∧ (boundary A (insert x xs.toFinset)).card≤w ∧ xs++[x]=ys := by
  simp [grow,List.mem_map,and_assoc]

private theorem pack_get {cs : List (List (Fin n))} {xs} (h : xs∈cs) :
    ∃ ys∈keep n cs,ys.toFinset=xs.toFinset := by
  have yes : (cs.find? (fun y => y.toFinset==xs.toFinset)).isSome := by
    rw [List.isSome_find?,List.any_eq_true]; exact ⟨xs,h,by simp⟩
  obtain ⟨ys,hy⟩ := Option.isSome_iff_exists.mp yes
  exact ⟨ys,List.mem_filterMap.mpr ⟨_,all_subsets _,hy⟩,
    beq_iff_eq.mp (List.find?_some (p := fun y : List (Fin n) => y.toFinset==xs.toFinset) hy)⟩

theorem pool_sound (A : Colored n) (w k : Nat) {xs} (h : xs∈pool A w k) :
    Route A w xs ∧ xs.length=k := by
  induction k generalizing xs with
  | zero => obtain rfl := List.mem_singleton.mp h; exact ⟨.nil,rfl⟩
  | succ k ih =>
    obtain ⟨_,_,find⟩ := List.mem_filterMap.mp h
    obtain ⟨ys,hy,g⟩ := List.mem_flatMap.mp (List.mem_of_find?_eq_some find)
    obtain ⟨x,no,bound,rfl⟩ := (make_mem A w ys xs).mp g
    obtain ⟨route,l⟩ := ih hy
    exact ⟨.extend route x no bound,by simp [l]⟩

theorem pool_complete {A : Colored n} {xs} (h : Route A w xs) :
    ∃ ys∈pool A w xs.length,ys.toFinset=xs.toFinset := by
  induction h with
  | nil => exact ⟨[],List.mem_singleton_self _,rfl⟩
  | @extend xs prior x no bound ih =>
    obtain ⟨ys,mem,seteq⟩ := ih
    have notIn : x∉ys := by simpa [←List.mem_toFinset,seteq] using no
    have step := (make_mem A w ys (ys++[x])).mpr ⟨x,notIn,seteq.symm ▸ bound,rfl⟩
    obtain ⟨zs,mz,z⟩ := pack_get (List.mem_flatMap.mpr ⟨ys,mem,step⟩)
    exact ⟨zs,by simpa [pool] using mz,by simpa [seteq] using z⟩


private theorem take_names (p : Equiv.Perm (Fin n)) (k : Nat) (x : Fin n) :
    x∈(List.ofFn p).take k ↔ (p.symm x).val<k := by
  constructor
  · intro h
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
    have bound : i<n := by simp only [List.length_take,List.length_ofFn] at hi; omega
    have same : p ⟨i,bound⟩=x := by simpa using eq
    rw [←same]; simpa using (List.length_take_le ..).trans_lt' hi
  · intro h
    refine List.mem_iff_getElem.mpr ⟨(p.symm x).val,?_,?_⟩
    · simpa using h
    · simp

private theorem initial_eq (p : Equiv.Perm (Fin n)) (j : Fin n) :
    ((List.ofFn p).take (j.val+1)).toFinset=initial p j := by
  ext x
  simp only [List.mem_toFinset,take_names,initial,mem_filter,mem_univ,true_and]
  change _ < j.val+1 ↔ _ ≤ j.val
  omega

private theorem route_of_narrow (p : Equiv.Perm (Fin n)) (good : Narrow A w p) (k : Nat) (hk : k≤n) :
    Route A w ((List.ofFn p).take k) := by
  induction k with
  | zero => simpa using (Route.nil : Route A w [])
  | succ k ih =>
    have klt : k<(List.ofFn p).length := by simpa using hk
    have split := List.take_succ_eq_append_getElem klt
    rw [split]
    apply Route.extend (ih (by omega))
    · simp [take_names]
    · have eq := congrArg List.toFinset split
      simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,insert_empty_eq,
        union_singleton] at eq
      rw [←eq,initial_eq p ⟨k,by omega⟩]; exact good _

private theorem route_nodup {xs : List (Fin n)} (h : Route A w xs) : xs.Nodup := by
  induction h with
  | nil => simp
  | extend prior x fresh width ih => simpa [List.nodup_append,ih] using (fun a (ha : a∈_) eq => fresh (eq ▸ ha) : ∀a∈_,¬a=x)

private theorem route_bound {xs : List (Fin n)} (h : Route A w xs) (k : Nat) (hk : k≤xs.length) :
    (boundary A (xs.take k).toFinset).card≤w := by
  induction h with
  | nil => simp [boundary]
  | @extend xs prior x fresh width ih =>
    by_cases old : k≤xs.length
    · rw [List.take_append_of_le_length old]; exact ih old
    · have eq : k=(xs++[x]).length := by simp at hk ⊢; omega
      rw [eq,List.take_length]; simpa using width

def ordered (A : Colored n) (w : Nat) := (pool A w n).head?

/-- The represented permutation is executable by forward lookups; its
inverse is used only in the correctness proof. -/
def index (xs : List (Fin n)) (i : Fin n) := xs[i.val]?.getD i

theorem ordered_sound {A : Colored n} (hit : ordered A w=some xs) :
    ∃ p : Equiv.Perm (Fin n), (∀ i,index xs i=p i) ∧ Narrow A w p := by
  obtain ⟨route,len⟩ := pool_sound A w n (List.mem_of_head? hit)
  let v (i : Fin n) := xs.get ⟨i.val,by rw [len]; exact i.isLt⟩
  have inj : Function.Injective v := by
    intro i j eq
    exact Fin.ext (congrArg (fun j : Fin xs.length => j.val) ((route_nodup route).injective_get eq))
  let p := Equiv.ofBijective v (Finite.injective_iff_bijective.mp inj)
  have idx (i) : index xs i=p i := by
    have lt : i.val<xs.length := by rw [len]; exact i.isLt
    simp [index,List.getElem?_eq_getElem lt,p,v]
  have order : List.ofFn p=xs := by
    apply List.ext_getElem
    · simp [len]
    · intro i a b; simp [p,v]
  refine ⟨p,idx,fun j => ?_⟩
  rw [←initial_eq,order]
  exact route_bound route _ (by have h:=j.isLt;omega)

theorem ordered_complete {A : Colored n} (D : Hierarchy A w) : (ordered A w).isSome := by
  obtain ⟨p,h⟩ := narrow_hierarchy A D
  have route : Route A w (List.ofFn p) := by simpa only [List.take_of_length_le (by simp : (List.ofFn p).length≤n)] using route_of_narrow p h n le_rfl
  obtain ⟨ys,mem,_⟩ := pool_complete route
  have ne : pool A w n≠[] := List.ne_nil_of_mem (by simpa using mem : ys∈_)
  simpa [ordered] using ne

end Recognition.LayoutSearch
