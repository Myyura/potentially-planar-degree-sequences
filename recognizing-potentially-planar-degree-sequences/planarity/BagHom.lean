import StateIso
import Frontier

/-! Finite variable elimination for homomorphism counting. Intermediate factors are tabulated
by their remaining variables. A row lookup follows the target value of each variable. -/
namespace Recognition.BagHom
open Finset Function StateIso

abbrev Assignment (n m : Nat) := Fin n → Fin m

structure Factor (n m : Nat) where
  scope : Finset (Fin n)
  eval : Assignment n m → Nat
  locality : ∀ f g, (∀i ∈ scope, f i=g i) → eval f=eval g

private def names (S : Finset (Fin n)) := (List.finRange n).filter (fun v => v∈S)

private inductive Rows where
  | value (v : Nat)
  | branches (choices : Array Rows)
deriving Inhabited

private def materialize (vs : List (Fin n)) (p : Assignment n m → Nat) (f : Assignment n m) : Rows :=
  match vs with
  | [] => .value (p f)
  | i :: is => .branches ((List.finRange m).map (fun x => materialize is p (update f i x))).toArray

private def lookup (vs : List (Fin n)) (t : Rows) (g : Assignment n m) : Nat :=
  match vs,t with
  | [], .value v => v
  | i :: is, .branches ts => lookup is (ts[(g i).val]?.getD default) g
  | _, _ => 0

private theorem lookup_materialize (vs : List (Fin n)) (p : Assignment n m → Nat) (f g : Assignment n m) :
    lookup vs (materialize vs p f) g = p (fun i => if i∈vs then g i else f i) := by
  induction vs generalizing f with
  | nil => simp [lookup,materialize]
  | cons i is ih =>
    have atIndex : (((List.finRange m).map (fun x => materialize is p (update f i x))).toArray)[(g i).val]? =
        some (materialize is p (update f i (g i))) := by
      rw [List.getElem?_toArray,List.getElem?_map,List.getElem?_eq_getElem (by simp)]
      simp
    simp only [lookup,materialize,atIndex,Option.getD_some,ih]
    congr 1
    funext j
    by_cases a : j=i <;> by_cases b : j∈is <;> simp_all [Function.update_of_ne]

def cached (F : Factor n m) (fill : Fin m) : Factor n m :=
  let vs := names F.scope
  let t := materialize vs F.eval (fun _ => fill)
  { scope := F.scope, eval := lookup vs t, locality := by
      intro f g same
      simp only [t,lookup_materialize]
      apply F.locality
      intro i hi
      simp [vs,names,hi,same i hi] }

theorem cached_eval (F : Factor n m) (fill : Fin m) (g : Assignment n m) :
    (cached F fill).eval g = F.eval g := by
  change lookup _ (materialize _ _ _) _ = _
  rw [lookup_materialize]
  exact F.locality _ _ (by intro i hi; simp [names,hi])

def weight (fs : List (Factor n m)) (f : Assignment n m) := (fs.map (fun t => t.eval f)).prod

def scope : List (Factor n m) → Finset (Fin n)
  | [] => ∅
  | t::ts => t.scope ∪ scope ts

private theorem contains_scope {fs : List (Factor n m)} {t} (member : t∈fs) : t.scope ⊆ scope fs := by
  induction fs with
  | nil => contradiction
  | cons a rest ih =>
    rcases List.mem_cons.mp member with eq|mem
    · subst t; exact Finset.subset_union_left
    · exact (ih mem).trans Finset.subset_union_right

private theorem weight_local (fs : List (Factor n m)) (f g : Assignment n m)
    (eq : ∀ i ∈ scope fs, f i=g i) : weight fs f=weight fs g := by
  unfold weight
  congr 1
  exact List.map_congr_left (fun t ht => t.locality _ _ (fun i hi => eq i (contains_scope ht hi)))

def withVar (v : Fin n) (fs : List (Factor n m)) := fs.filter fun F => v∈F.scope
def withoutVar (v : Fin n) (fs : List (Factor n m)) := fs.filter fun F => v∉F.scope

/-- The bag produced by eliminating v. -/
def bag (v : Fin n) (fs : List (Factor n m)) := (scope (withVar v fs)).erase v

def marginal (v : Fin n) (fs : List (Factor n m)) : Factor n m where
  scope := bag v fs
  eval f := ∑ x : Fin m, weight (withVar v fs) (update f v x)
  locality f g eq := by
    apply Finset.sum_congr rfl
    intro x _
    apply weight_local
    intro i hi
    by_cases iv : i=v
    · subst i; simp
    · simpa [iv] using eq i (Finset.mem_erase.mpr ⟨iv,hi⟩)

def eliminate (v : Fin n) (fs : List (Factor n m)) (fill : Fin m) :=
  cached (marginal v fs) fill :: withoutVar v fs

private theorem split_weight (v : Fin n) (fs : List (Factor n m)) (f : Assignment n m) :
    weight (withVar v fs) f * weight (withoutVar v fs) f = weight fs f := by
  have h := ((List.filter_append_perm (fun t : Factor n m => decide (v∈t.scope)) fs).map (fun t => t.eval f)).prod_eq
  simpa [weight,withVar,withoutVar,List.map_append] using h

theorem eliminate_eval (v : Fin n) (fs : List (Factor n m)) (fill : Fin m) (f : Assignment n m) :
    weight (eliminate v fs fill) f = ∑ x : Fin m, weight fs (update f v x) := by
  change (cached _ fill).eval f * weight (withoutVar v fs) f = _
  rw [cached_eval]
  change (∑ x : Fin m, weight (withVar v fs) (update f v x)) * _ = _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [←split_weight v fs (update f v x)]
  congr 1
  unfold weight
  congr 1
  apply List.map_congr_left
  intro t ht
  have avoids :=  of_decide_eq_true (List.mem_filter.mp ht).2
  apply t.locality
  intro i hi
  have ne : i≠v := fun iv => avoids (iv ▸ hi)
  exact (Function.update_of_ne ne _ _).symm

private def exchange (v : Fin n) :
    (Assignment n m × Fin m) ≃ (Assignment n m × Fin m) :=
  let swap (t : Assignment n m × Fin m) := (update t.1 v t.2,t.1 v)
  let inv : Function.Involutive swap := by
    rintro ⟨f,x⟩
    simp [swap,Function.update_idem]
  inv.toPerm _

private theorem weight_sum (v : Fin n) (fs : List (Factor n m)) (fill : Fin m) :
    (∑ f : Assignment n m, weight (eliminate v fs fill) f) = m*∑ f, weight fs f := by
  simp only [eliminate_eval]
  rw [← Fintype.sum_prod_type (fun t : Assignment n m × Fin m => weight fs (update t.1 v t.2))]
  have bij := (exchange (m := m) v).sum_comp (fun p => weight fs p.1)
  change (∑ t : Assignment n m × Fin m, weight fs (update t.1 v t.2)) =
    ∑ t : Assignment n m × Fin m, weight fs t.1 at bij
  rw [bij,Fintype.sum_prod_type]
  simp [←Finset.mul_sum]

/-- Eliminate the coordinates in the specified order. -/
def run (fill : Fin m) (order : List (Fin n)) (fs : List (Factor n m)) :=
  order.foldl (fun ts v => eliminate v ts fill) fs

private theorem run_sum (fill : Fin m) (order : List (Fin n)) (fs : List (Factor n m)) :
    (∑ f : Assignment n m, weight (run fill order fs) f) = m^order.length * ∑ f, weight fs f := by
  induction order generalizing fs with
  | nil => simp [run]
  | cons v vs ih =>
    change (∑ f, weight (run fill vs (eliminate v fs fill)) f) = _
    rw [ih,weight_sum]
    simp [pow_succ,Nat.mul_assoc]

private theorem scope_next (fill : Fin m) (v : Fin n) (fs : List (Factor n m)) :
    scope (eliminate v fs fill) ⊆ (scope fs).erase v := by
  have sub (xs : List (Factor n m)) (p : Factor n m → Bool) : scope (xs.filter p) ⊆ scope xs := by
    induction xs with
    | nil => simp [scope]
    | cons a as ih =>
      by_cases h : p a <;> simp [h,scope] <;>
        first | exact ih.trans Finset.subset_union_right | exact Finset.union_subset_union_right ih
  have lack (xs : List (Factor n m)) : v ∉ scope (withoutVar v xs) := by
    induction xs with
    | nil => simp [withoutVar,scope]
    | cons a as ih =>
      unfold withoutVar at *
      by_cases h : v∈a.scope <;> simpa [h,scope] using ih
  intro i hi
  change i∈bag v fs ∪ scope (withoutVar v fs) at hi
  rcases Finset.mem_union.mp hi with inside|outside
  · obtain ⟨ne,old⟩ := Finset.mem_erase.mp inside
    exact Finset.mem_erase.mpr ⟨ne,sub fs _ old⟩
  · exact Finset.mem_erase.mpr ⟨fun eq => lack fs (eq ▸ outside),sub fs _ outside⟩

private theorem run_scope (fill : Fin m) (order : List (Fin n)) (fs : List (Factor n m)) :
    ∀i ∈ scope (run fill order fs), i∈scope fs ∧ i∉order := by
  induction order generalizing fs with
  | nil => simp [run]
  | cons v vs ih =>
    intro i hi
    obtain ⟨h,skip⟩ := ih (eliminate v fs fill) i hi
    obtain ⟨ne,old⟩ := Finset.mem_erase.mp (scope_next fill v fs h)
    exact ⟨old,by simp [ne,skip]⟩

theorem run_exact (fill : Fin m) {order : List (Fin n)} (all : order.Perm (List.finRange n))
    (fs : List (Factor n m)) :
    weight (run fill order fs) (fun _ => fill) = ∑ f, weight fs f := by
  have empty : scope (run fill order fs)=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi =>
    (run_scope fill order fs i hi).2 (all.mem_iff.mpr (List.mem_finRange _)))
  have const (f : Assignment n m) : weight (run fill order fs) f =
      weight (run fill order fs) (fun _ => fill) := weight_local _ _ _ (by simp [empty])
  have total := run_sum fill order fs
  simp only [const,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul] at total
  have len : order.length=n := by simpa using all.length_eq
  rw [len] at total
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by have := fill.isLt; omega)) total

def vertexFactor (A : Colored n) (B : Colored m) (Y : Finset (Fin m)) (i : Fin n) : Factor n m :=
  { scope := {i}, eval := fun f => if A.color i=B.color (f i) ∧ f i∉Y then 1 else 0
    locality := by intro f g h; rw [h i (by simp)] }

def edgeFactor (B : Colored m) (ij : Fin n × Fin n) : Factor n m :=
  { scope := {ij.1,ij.2}, eval := fun f => if B.edge (f ij.1) (f ij.2) then 1 else 0
    locality := by intro f g h; rw [h ij.1 (by simp),h ij.2 (by simp)] }

def pairs (A : Colored n) := ((List.finRange n).flatMap fun i =>
  (List.finRange n).map fun j => (i,j)).filter fun ij => A.edge ij.1 ij.2

private theorem pairs_mem (A : Colored n) (i j : Fin n) : (i,j)∈pairs A ↔ A.edge i j=true := by
  simp [pairs]

def constraints (A : Colored n) (B : Colored m) (Y : Finset (Fin m)) :=
  (List.finRange n).map (vertexFactor A B Y) ++ (pairs A).map (edgeFactor B)

private theorem indicators (L : List α) (p : α → Prop) [DecidablePred p] :
    (L.map (fun a => if p a then 1 else 0)).prod = if ∀a∈L,p a then (1:Nat) else 0 := by
  induction L with
  | nil => simp
  | cons a ls ih => by_cases ok : p a <;> simp [ih,ok]

private theorem constraints_eval (A : Colored n) (B : Colored m) (Y : Finset (Fin m)) (f : Assignment n m) :
    weight (constraints A B Y) f = if Preserves A B f ∧ Y ⊆ missed f then 1 else 0 := by
  unfold weight constraints
  rw [List.map_append,List.prod_append,List.map_map,List.map_map]
  change ((List.finRange n).map fun i => if A.color i=B.color (f i) ∧ f i∉Y then 1 else 0).prod *
    ((pairs A).map fun p => if B.edge (f p.1) (f p.2)=true then 1 else 0).prod = _
  rw [indicators,indicators]
  let okv := ∀a∈List.finRange n,A.color a=B.color (f a) ∧ f a∉Y
  let oke := ∀p∈pairs A,B.edge (f p.1) (f p.2)=true
  have agree : (okv ∧ oke) ↔ Preserves A B f ∧ Y ⊆ missed f := by
    constructor
    · rintro ⟨vv,ee⟩
      refine ⟨⟨fun i => (vv i (List.mem_finRange _)).1,
          fun i j h => ee (i,j) ((pairs_mem A i j).mpr h)⟩,?_⟩
      intro t ht
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rintro member
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp member
      exact (vv i (List.mem_finRange _)).2 ht
    · rintro ⟨⟨col,edge⟩,avoid⟩
      refine ⟨fun i _ => ⟨col i,?_⟩,fun ⟨i,j⟩ h => edge i j ((pairs_mem A i j).mp h)⟩
      intro mem
      exact (Finset.mem_sdiff.mp (avoid mem)).2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  split <;> rename_i hv <;> split <;> rename_i he <;> split <;> rename_i both <;>
    first | rfl | exact False.elim (both (agree.mp ⟨hv,he⟩)) |
      exact False.elim (hv (agree.mpr both).1) | exact False.elim (he (agree.mpr both).2)

/-- Compute the homomorphisms avoiding the excluded set with an elimination order. -/
def count (A : Colored n) (B : Colored m) (order : List (Fin n)) (Y : Finset (Fin m)) :=
  if pos : 0<m then
    let fill : Fin m := ⟨0,pos⟩
    weight (run fill order (constraints A B Y)) (fun _ => fill)
  else homCount A B Y

theorem count_exact (A : Colored n) (B : Colored m) {order : List (Fin n)}
    (all : order.Perm (List.finRange n)) (Y : Finset (Fin m)) : count A B order Y=homCount A B Y := by
  unfold count
  split
  next pos =>
    rw [run_exact _ all]
    simp_rw [constraints_eval]
    rw [Finset.sum_boole]
    unfold homCount homs
    apply congrArg Finset.card
    ext f; simp
  next => rfl

def compare (A : Colored n) (B : Colored m) (order : List (Fin n)) : Bool :=
  decide (n=m ∧ (arcs A).card=(arcs B).card ∧ 0 < alternating (count A B order))

theorem compare_correct (A : Colored n) (B : Colored m) {order : List (Fin n)}
    (all : order.Perm (List.finRange n)) : compare A B order=true ↔ Iso A B := by
  have eq : count A B order=homCount A B := funext (count_exact A B all)
  simpa [compare,StateIso.compare,eq] using StateIso.compare_iff A B

/-! Each invocation of the marginal stores one leaf per assignment to its bag. -/
private def leaves : Nat → Rows → Nat
  | 0,.value _ => 1
  | k+1,.branches ts => (ts.toList.map (leaves k)).sum
  | _,_ => 0

theorem leaf_count (vs : List (Fin n)) (p : Assignment n m → Nat) (f : Assignment n m) :
    leaves vs.length (materialize vs p f) = m^vs.length := by
  induction vs generalizing f with
  | nil => simp [leaves,materialize]
  | cons v vs ih => simp [materialize,leaves,List.map_map,Function.comp_def,ih,pow_succ,Nat.mul_comm]

theorem names_length (S : Finset (Fin n)) : (names S).length=S.card := by
  have nd : (names S).Nodup := List.filter_sublist.nodup (List.nodup_finRange n)
  have eq : (names S).toFinset=S := by ext i; simp [names]
  rw [←eq,List.toFinset_card_of_nodup nd,eq]

def tableRows (fill : Fin m) : List (Fin n) → List (Factor n m) → Nat
  | [], _ => 0
  | v::vs,fs =>
    let F := marginal v fs
    let vars := names F.scope
    leaves vars.length (materialize vars F.eval (fun _ => fill)) +
      tableRows fill vs (eliminate v fs fill)

/-- Largest number of remaining coordinates in a materialized table. -/
def width (fill : Fin m) : List (Fin n) → List (Factor n m) → Nat
  | [],_ => 0
  | v::vs,fs => max (bag v fs).card (width fill vs (eliminate v fs fill))

theorem table_rows_bound (fill : Fin m) (order : List (Fin n)) (fs : List (Factor n m)) :
    tableRows fill order fs ≤ order.length * m^(width fill order fs) := by
  induction order generalizing fs with
  | nil => simp [tableRows]
  | cons v vs ih =>
    rw [tableRows,leaf_count,names_length,List.length_cons,Nat.succ_mul]
    change m^(bag v fs).card + _ ≤ _
    have q : 1≤m := by have := fill.isLt; omega
    exact Nat.le_trans (Nat.add_le_add (Nat.pow_le_pow_right q (Nat.le_max_left ..))
        ((ih _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right q (Nat.le_max_right ..)))))
      (Nat.le_of_eq (Nat.add_comm ..))

/-- A vertex order whose later neighbors lie on nested paths of bounded size.
This is the condition obtained by ordering separator-tree descendants first. -/
structure Layout (A : Colored n) (w : Nat) where
  later : Fin n → Finset (Fin n)
  cap : ∀ v, (later v).card ≤ w
  edge : ∀ u v, A.edge u v=true → u≠v →
    (if u≤v then v ∈ later u else u ∈ later v)
  nested : ∀r, ∀i∈later r, ∀j∈later r, i<j → j∈later i

private def compatible (up : Fin n → Finset (Fin n)) (fs : List (Factor n m)) :=
  ∀F∈fs, ∀i∈F.scope, ∀j∈F.scope, i<j → j∈up i

private theorem some_scope {fs : List (Factor n m)} {i : Fin n} (hi : i∈scope fs) :
    ∃t∈fs,i∈t.scope := by
  induction fs with
  | nil => simp [scope] at hi
  | cons a as ih =>
    rcases Finset.mem_union.mp hi with h|h
    · exact ⟨_,List.mem_cons_self,h⟩
    · obtain ⟨t,mem,here⟩ := ih h
      exact ⟨t,List.mem_cons_of_mem _ mem,here⟩

private theorem layout_width (A : Colored n) (D : Layout A w) (fill : Fin m)
    (order : List (Fin n)) (fs : List (Factor n m)) (ok : compatible D.later fs)
    (sorted : order.Pairwise (·≤·)) (inside : ∀i∈scope fs, i∈order) : width fill order fs ≤ w := by
  induction order generalizing fs with
  | nil => simp [width]
  | cons v vs ih =>
    have bagSub : bag v fs ⊆ D.later v := by
      intro i mem
      obtain ⟨ne,h⟩ := Finset.mem_erase.mp mem
      obtain ⟨f,ff,fi⟩ := some_scope h
      obtain ⟨old,fv⟩ := List.mem_filter.mp ff
      have oi := inside i (contains_scope old fi)
      have ivs := (List.mem_cons.mp oi).resolve_left ne
      exact ok f old v (of_decide_eq_true fv) i fi
        (lt_of_le_of_ne ((List.pairwise_cons.mp sorted).1 i ivs) ne.symm)
    rw [width,Nat.max_le]
    refine ⟨(Finset.card_le_card bagSub).trans (D.cap v),ih _ ?_ (List.pairwise_cons.mp sorted).2 ?_⟩
    · intro f mem i fi j fj lt
      rcases List.mem_cons.mp mem with eq|old
      · subst f
        exact D.nested v i (bagSub fi) j (bagSub fj) lt
      · exact ok _ (List.mem_filter.mp old).1 i fi j fj lt
    · intro i hi
      obtain ⟨ne,old⟩ := Finset.mem_erase.mp (scope_next fill v fs hi)
      exact (List.mem_cons.mp (inside i old)).resolve_left ne

private theorem init_compatible (A : Colored n) (B : Colored m) (D : Layout A w) (Y : Finset (Fin m)) :
    compatible D.later (constraints A B Y) := by
  intro f mem i fi j fj lt
  rcases List.mem_append.mp mem with vertex|arc
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp vertex
    change i∈({a} : Finset _) at fi
    change j∈({a} : Finset _) at fj
    simp at fi fj
    exact (lt.ne (fi.trans fj.symm)).elim
  · obtain ⟨⟨u,v⟩,h,rfl⟩ := List.mem_map.mp arc
    change i∈({u,v} : Finset _) at fi
    change j∈({u,v} : Finset _) at fj
    simp only [Finset.mem_insert,Finset.mem_singleton] at fi fj
    rcases fi with rfl|rfl <;> rcases fj with rfl|rfl
    · exact (lt_irrefl _ lt).elim
    · simpa [lt.le] using D.edge _ _ ((pairs_mem A _ _).mp h) lt.ne
    · simpa [not_le.mpr lt] using D.edge _ _ ((pairs_mem A _ _).mp h) lt.ne.symm
    · exact (lt_irrefl _ lt).elim

/-- A supplied separator layout controls the storage of every induced-target
homomorphism calculation, for any coloring and excluded subset. -/
theorem graph_table_rows (A : Colored n) (B : Colored m) (D : Layout A w) (fill : Fin m)
    (Y : Finset (Fin m)) :
    tableRows fill (List.finRange n) (constraints A B Y) ≤ n*m^w := by
  apply (table_rows_bound ..).trans
  simp only [List.length_finRange]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by have := fill.isLt; omega)
  exact layout_width A D fill _ _ (init_compatible A B D Y) (List.pairwise_le_finRange _) (fun i _ => List.mem_finRange i)

/-- Summation over all exclusion sets remains single-exponential when the
number of live coordinates is at most a constant times the square root. -/
theorem square_root_table_bound (A : Colored n) (B : Colored m) (K C : Nat)
    (source : n≤K) (target : m≤K) (D : Layout A (C*(K.sqrt+1))) (fill : Fin m) :
    (∑ Y ∈ (Finset.univ : Finset (Fin m)).powerset,
      tableRows fill (List.finRange n) (constraints A B Y)) ≤ 2^((2+9*C)*(K+1)) := by
  let a := PlanarDegrees.Frontier.cost K
  let b := K.sqrt+1
  have a2 : a*a ≤ 9*(K+1) := PlanarDegrees.Frontier.cost_square K
  have ss := Nat.sqrt_le K
  have sk : K.sqrt≤K := Nat.sqrt_le_self K
  have b2 : b*b ≤ 9*(K+1) := by dsimp [b]; nlinarith
  have ab : a*b≤9*(K+1) := by
    rcases Nat.le_total a b with h|h
    · exact (Nat.mul_le_mul_right b h).trans b2
    · exact (Nat.mul_le_mul_left a h).trans a2
  have e : m ≤ 2^a := target.trans ((Nat.le_add_right K 2).trans (PlanarDegrees.Frontier.cost_brackets K).2)
  have aw : a*(C*b) ≤ 9*C*(K+1) := by
    calc a*(C*b) = C*(a*b) := by ac_rfl
         _ ≤ C*(9*(K+1)) := Nat.mul_le_mul_left _ ab
         _ = _ := by ac_rfl
  have power : m^(C*b) ≤ 2^(9*C*(K+1)) := by
    apply (Nat.pow_le_pow_left e _).trans
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) aw
  have order : n ≤ 2^K := source.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := K)))
  calc
    _ ≤ ∑ _Y ∈ (Finset.univ : Finset (Fin m)).powerset, n*m^(C*b) :=
      Finset.sum_le_sum (fun Y _ => graph_table_rows A B D fill Y)
    _ = 2^m*(n*m^(C*b)) := by simp
    _ ≤ 2^K*(2^K*2^(9*C*(K+1))) := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide) target) (Nat.mul_le_mul order power)
    _ ≤ _ := by
      rw [←pow_add,←pow_add]
      apply Nat.pow_le_pow_right (by decide)
      nlinarith

end Recognition.BagHom
