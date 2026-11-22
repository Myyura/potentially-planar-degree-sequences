import MainResult
import HistogramCount
import Enumeration

/-! List one nonincreasing representative of every planaric multiset.
Each recursive node chooses only a part compatible with its remaining
mass and its preceding part; zero fills the unused slots. -/
namespace Recognition.Listing
open SparseBoundary

/-- Enumerate the bounded partitions, padded to precisely the requested
number of slots. A zero has only the all-zero continuation. -/
def rows : Nat → Nat → Nat → List (List Nat)
  | 0,_,_ => [[]]
  | s+1,cap,budget => (List.range (min cap budget+1)).flatMap fun a =>
    (rows s a (budget-a)).map (a::·)

theorem rows_spec (s cap budget : Nat) (xs : List Nat) :
    xs∈rows s cap budget ↔ xs.length=s ∧ xs.Pairwise (·≥·) ∧ xs.sum≤budget ∧ ∀x∈xs,x≤cap := by
  induction s generalizing xs cap budget with
  | zero => cases xs <;> simp [rows]
  | succ s ih =>
    cases xs with
    | nil => simp [rows]
    | cons a xs =>
      simp only [rows,List.mem_flatMap,List.mem_range,List.mem_map,List.cons.injEq,List.length_cons,
        Nat.succ.injEq,List.pairwise_cons,List.sum_cons,List.mem_cons]
      constructor
      · rintro ⟨b,hb,l,m,rfl,rfl⟩
        obtain ⟨len,order,size,lim⟩ := (ih _ _ _).mp m
        refine ⟨len,⟨lim,order⟩,by omega,?_⟩
        intro v hv
        rcases hv with rfl|mem
        · omega
        · exact (lim v mem).trans (by omega)
      · rintro ⟨len,⟨lim,order⟩,mass,capAll⟩
        have capA := capAll a (Or.inl rfl)
        exact ⟨a,by omega,xs,(ih _ _ _).mpr ⟨len,order,by omega,lim⟩,rfl,rfl⟩

theorem rows_nodup (s cap budget : Nat) : (rows s cap budget).Nodup := by
  induction s generalizing cap budget with
  | zero => simp [rows]
  | succ s ih =>
    rw [rows,List.nodup_flatMap]
    constructor
    · intro a _
      exact (ih a (budget-a)).map (fun _ _ eq => (List.cons.inj eq).2)
    · apply List.nodup_range.imp
      intro a b ne
      apply List.disjoint_left.mpr
      intro x ma mb
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp ma
      obtain ⟨v,_,eq⟩ := List.mem_map.mp mb
      exact ne (List.cons.inj eq).1.symm

private theorem entry_le {xs : List Nat} {a} (m : a∈xs) : a≤xs.sum := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_cons.mp m with rfl|m
    · simp
    · simpa only [List.sum_cons] using (ih m).trans (Nat.le_add_left ..)

def candidates (n : Nat) := rows n (6*n) (6*n)

theorem candidates_spec (n) (ds : List Nat) :
    ds∈candidates n ↔ ds.length=n ∧ ds.Pairwise (·≥·) ∧ ds.sum≤6*n := by
  rw [candidates,rows_spec]
  exact ⟨fun ⟨a,b,c,_⟩ => ⟨a,b,c⟩,fun ⟨a,b,c⟩ => ⟨a,b,c,fun _ h => (entry_le h).trans c⟩⟩

/-- A chooser can be the certificate search, the compressed comparator,
or any exact implementation returning a labelled graph. -/
def result (choose : (ds : List Nat) → Option (Graph ds.length)) (n : Nat) :=
  (candidates n).filter fun ds => (choose ds).isSome

theorem exact (choose : (ds : List Nat) → Option (Graph ds.length))
    (correct : ∀ds,(choose ds).isSome ↔ Planaric ds) (n) (ds : List Nat) :
    ds∈result choose n ↔ ds.length=n ∧ ds.Pairwise (·≥·) ∧ Planaric ds := by
  rw [result,List.mem_filter,candidates_spec,correct]
  exact ⟨fun ⟨⟨a,b,_⟩,p⟩ => ⟨a,b,p⟩,fun ⟨a,b,p⟩ => ⟨⟨a,b,by simpa [a] using MainResult.volume p⟩,p⟩⟩

theorem no_duplicates (choose : (ds : List Nat) → Option (Graph ds.length)) (n) :
    (result choose n).Nodup := (rows_nodup n _ _).filter _

private theorem rows_ordered (s cap budget) : (rows s cap budget).Pairwise (List.Lex (·<·)) := by
  induction s generalizing cap budget with
  | zero => simp [rows]
  | succ s ih =>
    rw [rows,List.pairwise_flatMap]
    constructor
    · intro a _
      apply List.pairwise_map.mpr
      exact (ih a (budget-a)).imp (fun h => List.Lex.cons h)
    · apply List.pairwise_lt_range.imp
      intro a b lt xs mx ys my
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp mx
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp my
      exact List.Lex.rel lt

/-- The list of records is lexicographically increasing; within a record,
the degrees are nonincreasing. -/
theorem output_order (choose : (ds : List Nat) → Option (Graph ds.length)) (n) :
    (result choose n).Pairwise (List.Lex (·<·)) := (rows_ordered ..).filter _

/-- An entirely executable lister, independent of external algorithms. -/
def listAll := result Certificate.findRealization

theorem listAll_spec (n) (ds : List Nat) :
    ds∈listAll n ↔ ds.length=n ∧ ds.Pairwise (·≥·) ∧ Planaric ds :=
  exact _ Certificate.findRealization_iff n ds

theorem compressed_spec (sep : SeparatorInput.WeightedPlanarSeparator) (n) (ds : List Nat) :
    ds∈result MainResult.find n ↔ ds.length=n ∧ ds.Pairwise (·≥·) ∧ Planaric ds :=
  exact _ (MainResult.find_iff sep) n ds

private def hist (M : Nat) (xs : List Nat) : HistogramCount.Histogram M :=
  fun j => ⟨min M (xs.count (j.val+1)),by omega⟩

private theorem hist_count {M : Nat} {xs : List Nat} (hs : xs.length≤M) (j : Fin M) :
    ((hist M xs) j).val=xs.count (j.val+1) := Nat.min_eq_right ((List.count_le_length).trans hs)

private theorem weighted (g : Nat → Nat) (M : Nat) (xs : List Nat) (bounded : ∀x∈xs,x≤M) :
    ∑j∈Finset.range (M+1),g j*xs.count j=(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha : a∈Finset.range (M+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (bounded a (by simp)))
    have tail := ih (fun x m => bounded x (List.mem_cons_of_mem _ m))
    simp only [List.count_cons,beq_iff_eq,Nat.mul_add,mul_ite,Nat.mul_one,Nat.mul_zero,
      Finset.sum_add_distrib,Finset.sum_ite_eq,ha,ite_true,List.map_cons,List.sum_cons]
    omega

private theorem histogram_mass {M : Nat} {xs : List Nat} (small : xs.length≤M) (bounded : ∀x∈xs,x≤M) :
    HistogramCount.mass (hist M xs)=xs.sum := by
  have w := weighted id M xs bounded
  rw [Finset.sum_range_succ'] at w
  simp only [HistogramCount.mass,hist_count small]
  rw [Fin.sum_univ_eq_sum_range (fun j => (j+1)*xs.count (j+1))]
  simpa using w

private theorem histogram_injective {M : Nat} {xs ys : List Nat}
    (len : xs.length=ys.length) (small : xs.length≤M)
    (xb : ∀x∈xs,x≤M) (yb : ∀y∈ys,y≤M) (eq : hist M xs=hist M ys) : xs.Perm ys := by
  have syl := len ▸ small
  have same (j : Nat) (h : j<M) : xs.count (j+1)=ys.count (j+1) := by
    let i := (⟨j,h⟩ : Fin M)
    simpa only [hist_count small,hist_count syl,i] using congrArg (fun f : HistogramCount.Histogram M => (f i).val) eq
  have off (ls : List Nat) (bound : ∀x∈ls,x≤M) (a : Nat) (ha : M<a) : ls.count a=0 :=
    List.count_eq_zero_of_not_mem (fun mem => by have := bound a mem; omega)
  apply List.perm_iff_count.mpr
  intro a
  cases a with
  | succ j =>
    by_cases h : j<M
    · exact same _ h
    · rw [off xs xb _ (by omega),off ys yb _ (by omega)]
  | zero =>
    have total (ls : List Nat) (bound : ∀x∈ls,x≤M) : (∑ j∈Finset.range M, ls.count (j+1))+ls.count 0=ls.length := by
      have w := weighted (fun _ => 1) M ls bound
      rw [Finset.sum_range_succ'] at w
      simpa using w
    have eqsum : (∑j∈Finset.range M, xs.count (j+1))=(∑j∈Finset.range M, ys.count (j+1)) :=
      Finset.sum_congr rfl (fun j hj => same _ (Finset.mem_range.mp hj))
    have tx := total xs xb
    have ty := total ys yb
    omega

theorem number_candidates (n : Nat) : (candidates n).length≤(HistogramCount.candidates (6*n)).card := by
  let M := 6*n
  have card : (candidates n).toFinset.card=(candidates n).length := List.toFinset_card_of_nodup (rows_nodup ..)
  rw [←card]
  apply Finset.card_le_card_of_injOn (hist M)
  · intro xs mem
    obtain ⟨len,_,mass⟩ := (candidates_spec n xs).mp (List.mem_toFinset.mp mem)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (histogram_mass (by dsimp [M]; omega : xs.length≤M) (fun _ h => (entry_le h).trans mass)).le.trans mass
  · intro xs mx ys my eq
    obtain ⟨lx,sx,hx⟩ := (candidates_spec n xs).mp (List.mem_toFinset.mp mx)
    obtain ⟨ly,sy,hy⟩ := (candidates_spec n ys).mp (List.mem_toFinset.mp my)
    apply List.Perm.eq_of_pairwise' sx sy
    exact histogram_injective (M := M) (lx.trans ly.symm) (by change xs.length≤6*n; omega)
      (fun _ h => (entry_le h).trans hx) (fun _ h => (entry_le h).trans hy) eq

theorem candidate_bound (n : Nat) (hn : 0<n) :
    ((candidates n).length : ℝ) ≤ Real.exp (3*Real.sqrt (6*n)) := by
  have card : ((candidates n).length : ℝ) ≤ (HistogramCount.candidates (6*n)).card := by exact_mod_cast number_candidates n
  exact card.trans (by simpa using HistogramCount.sqrt_bound (6*n) (by omega))

/-- A second return component meters the same traversal. The cost of a
branch includes generating its part, prefixing all child records, and
copying the outer flatMap result. -/
def generate : Nat → Nat → Nat → List (List Nat) × Nat
  | 0,_,_ => ([[]],1)
  | s+1,cap,budget =>
    let branches := (List.range (min cap budget+1)).map fun a =>
      let (ls,w) := generate s a (budget-a)
      (ls.map (a::·),w+8*(ls.length+1))
    (branches.flatMap Prod.fst,(branches.map Prod.snd).sum+1)

theorem generate_eq (s cap budget) : (generate s cap budget).1=rows s cap budget := by
  induction s generalizing cap budget with
  | zero => rfl
  | succ s ih => simp [generate,rows,List.flatMap_map,Function.comp_def,ih]

private theorem nonempty_rows (s cap budget : Nat) : 0<(rows s cap budget).length := by
  apply List.length_pos_of_mem (a := List.replicate s 0)
  rw [rows_spec]
  exact ⟨List.length_replicate,by simp,by simp,by simp⟩

/-- Aggregate generation work is linear in depth times the number of
candidate records, including all branches containing leading zeros. -/
theorem generate_cost (s cap budget) :
    (generate s cap budget).2≤32*(s+1)*(rows s cap budget).length := by
  induction s generalizing cap budget with
  | zero => change 1≤32*1*1; decide
  | succ s ih =>
    let parts := List.range (min cap budget+1)
    let kids := fun a => (rows s a (budget-a)).length
    let work := fun a => (generate s a (budget-a)).2+8*(kids a+1)
    have c (a : Nat) : work a≤(32*(s+1)+16)*kids a := by
      have t := ih a (budget-a)
      have pos := nonempty_rows s a (budget-a)
      dsimp [work,kids]; nlinarith
    have total := List.sum_le_sum (l := parts) (fun a _ => c a)
    rw [List.sum_map_mul_left] at total
    have num : (rows (s+1) cap budget).length=(parts.map kids).sum := by
      simp [rows,List.length_flatMap,parts,kids]
    have pos := nonempty_rows (s+1) cap budget
    rw [num] at pos ⊢
    simp only [generate,List.map_map,Function.comp_def,generate_eq]
    change (parts.map work).sum+1≤_
    nlinarith

/-- Charge every requested graph decision, including a rejected list.
The source bit budget does not constrain the caller's implementation. -/
def run (choose : (ds : List Nat) → Option (Graph ds.length) × Nat) (n : Nat) :
    List (List Nat) × Nat :=
  let (rows,w) := generate n (6*n) (6*n)
  let decisions := rows.map fun ds =>
    let (G,t) := choose ds
    (if G.isSome then some ds else none,t+4)
  (decisions.filterMap Prod.fst,w+(decisions.map Prod.snd).sum+1)

theorem run_eq (choose : (ds : List Nat) → Option (Graph ds.length) × Nat) (n) :
    (run choose n).1=result (fun ds => (choose ds).1) n := by
  simp only [run,generate_eq,result,candidates,List.filterMap_map,Function.comp_def]
  generalize rows n (6*n) (6*n)=ls
  induction ls with
  | nil => rfl
  | cons a ls ih => cases h : (choose a).1.isSome <;> simp [h,ih]

theorem run_cost (choose : (ds : List Nat) → Option (Graph ds.length) × Nat) (n D : Nat)
    (per : ∀ds∈candidates n,(choose ds).2≤D) :
    (run choose n).2≤(32*(n+1)+D+4)*(candidates n).length+1 := by
  have prod := generate_cost n (6*n) (6*n)
  have sum : ((candidates n).map (fun ds => (choose ds).2+4)).sum≤(candidates n).length*(D+4) := by
    simpa using List.sum_le_sum (l := candidates n) (g := fun _ => D+4) (fun x h => Nat.add_le_add_right (per x h) 4)
  simp only [run,List.map_map,Function.comp_def,generate_eq]
  change _+((candidates n).map (fun ds => (choose ds).2+4)).sum+1≤_
  change _≤32*(n+1)*(candidates n).length at prod
  nlinarith

/-- The normalized output itself contains all members of the independent
star-forest family, each in a different row. -/
theorem output_lower (k n : Nat) (fits : k*(k+5)≤2*n) : 2^k≤(listAll n).length := by
  let representative (b : Fin k → Bool) := (Enumeration.padded n (List.ofFn b)).mergeSort (·≥·)
  have family := Enumeration.output_family k n fits
  have reach (b : Fin k → Bool) : representative b∈listAll n := by
    obtain ⟨len,pg⟩ := family.1 (List.ofFn b) (by simp)
    have p := List.mergeSort_perm (Enumeration.padded n (List.ofFn b)) (·≥·)
    apply (listAll_spec ..).mpr
    exact ⟨p.length_eq.trans len,List.pairwise_mergeSort' (·≥·) _,(planaric_perm p).mpr pg⟩
  have inject : Function.Injective representative := by
    intro a b eq
    have p : (Enumeration.padded n (List.ofFn a)).Perm (Enumeration.padded n (List.ofFn b)) := by
      have l := List.mergeSort_perm (Enumeration.padded n (List.ofFn a)) (·≥·)
      change (representative a).Perm _ at l
      have r := List.mergeSort_perm (Enumeration.padded n (List.ofFn b)) (·≥·)
      exact l.symm.trans (eq ▸ r)
    have same := family.2 _ _ (by simp) (by simp) p
    exact List.ofFn_injective same
  have c := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin k → Bool)))
    (t := (listAll n).toFinset) representative (fun a _ => List.mem_toFinset.mpr (reach a)) inject.injOn
  have count : (listAll n).toFinset.card=(listAll n).length := List.toFinset_card_of_nodup (no_duplicates ..)
  simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,count] using c

theorem candidate_power (n : Nat) : (candidates n).length≤2^(18*(n.sqrt+1)) := by
  by_cases positive : 0<n
  · let S := n.sqrt+1
    have cut : n<S*S := Nat.lt_succ_sqrt n
    have real : (n:ℝ)<(S:ℝ)*S := by exact_mod_cast cut
    have root : Real.sqrt (6*n)≤3*(S:ℝ) := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity,by nlinarith⟩
    have half : Real.exp (1/2) ≤ 2 := by
      have e := Real.exp_bound_div_one_sub_of_interval (x:=1/2) (by norm_num) (by norm_num)
      norm_num at e ⊢
      exact e
    have high := (candidate_bound n positive).trans (Real.exp_le_exp.mpr (show 3*Real.sqrt (6*(n:ℝ))≤(18*S:Nat)*(1/2:ℝ) by push_cast; linarith))
    rw [Real.exp_nat_mul] at high
    exact_mod_cast high.trans (pow_le_pow_left₀ (Real.exp_nonneg _) half _)
  · have := Nat.eq_zero_of_not_pos positive
    subst n; decide

/-- Matching square-root exponents for the number of actual distinct
normalized outputs, unconditionally, at every order at least 25. -/
theorem population_growth (n : Nat) (hn : 25≤n) :
    2^n.sqrt≤(listAll n).length ∧ (listAll n).length≤2^(18*(n.sqrt+1)) := by
  have low : 5≤n.sqrt := Nat.le_sqrt.mpr (by omega)
  have sq := Nat.sqrt_le n
  refine ⟨output_lower n.sqrt n (by nlinarith [Nat.mul_le_mul_left n.sqrt low]),?_⟩
  exact (List.length_filter_le _ (candidates n)).trans (candidate_power n)

#print axioms population_growth
#print axioms output_lower
#print axioms candidate_power
#print axioms run_eq
#print axioms run_cost
#print axioms listAll_spec
#print axioms candidate_bound
end Recognition.Listing
