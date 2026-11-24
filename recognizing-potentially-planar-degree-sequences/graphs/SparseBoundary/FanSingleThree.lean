import SparseBoundary.FanThreeReduction
import SparseBoundary.FanPromote
import SparseBoundary.GraphFourReduction

namespace SparseBoundary.Fan.Three

open Graph

private def repairGraph : Graph 8 := ⟨186081121⟩

private theorem repair_planar : repairGraph.Planar := by
  apply outer_order_planar (v:=4)
  refine ⟨fun i => ([1,2,6,5,0,7,3,4] : List Nat)[i.val]!,?_,?_⟩ <;> decide +kernel

/-- Every preimage of the exceptional six-core sequence (5^5,3,2^2)
under equal-pair restoration has this single eight-vertex support. -/
private theorem repair_pair (g : Nat) (hg : 4≤g) :
    Planaric (List.replicate (g-2) 2 ++ [g,g,5,5,5,5,5,3]) := by
  let E : List (Fin 8 × Fin 8) := List.replicate (g-3) (0,1) ++ [(2,3)]
  have good : ∀ e∈E,repairGraph.adj e.1 e.2=true := by
    intro e he
    rcases List.mem_append.mp he with he|he
    · obtain ⟨_,rfl⟩ := List.mem_replicate.mp he; decide +kernel
    · obtain rfl := List.mem_singleton.mp he; decide +kernel
  have hp := expanded_planaric repair_planar E good
  have number : E.length=g-2 := by simp [E]; omega
  rw [number] at hp
  have eqn : List.ofFn (fun i => repairGraph.degree i+increments E i)=[g,g,5,5,5,5,5,3] := by
    have labels (f : Fin 8 → Nat) : List.ofFn f=[f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7] := rfl
    have deg : List.ofFn repairGraph.degree=[3,3,4,4,5,5,5,3] := by decide +kernel
    rw [labels] at deg ⊢
    simp only [List.cons.injEq,and_true] at deg
    obtain ⟨a,b,c,d,e,f,k,l⟩ := deg
    have inc i : increments E i = (if pairRow 0 1 i then g-3 else 0)+(if pairRow 2 3 i then 1 else 0) := by
      simp [E,increments,List.countP_replicate]
    simp only [a,b,c,d,e,f,k,l,inc]
    change [3+(g-3+0),3+(g-3+0),4+(0+1),4+(0+1),5+(0+0),5+(0+0),5+(0+0),3+(0+0)]=_
    simp only [List.cons.injEq,and_true]; omega
  rwa [eqn] at hp

private theorem min5_defect (h : List Nat) (hm : ∀d∈h,3≤d) :
    5*h.length≤h.sum+2*h.count 3+h.count 4 := by
  induction h with
  | nil => simp
  | cons a h ih =>
    have ha := hm a (by simp)
    have hh := ih (fun d m => hm d (by simp [m]))
    simp only [List.length_cons,List.sum_cons,List.count_cons]
    by_cases a3 : a=3 <;> by_cases a4 : a=4 <;>
      simp [a3,a4] <;> omega

private theorem repeat_when_small (h : List Nat) (hm : ∀d∈h,3≤d ∧ d<h.length) (size : 8≤h.length) :
    ∃g,2≤h.count g := by
  apply Classical.byContradiction; intro no
  have nodup : h.Nodup := List.nodup_iff_count.mpr (fun g => by
    have : ¬2≤h.count g := fun x => no ⟨g,x⟩; omega)
  have sub : h⊆List.range' 3 (h.length-3) := by
    intro x hx
    have := hm x hx
    apply List.mem_range'_1.mpr; omega
  have hle := nodup.length_le_of_subset sub
  simp only [List.length_range'] at hle; omega

private theorem rem_pair {h : List Nat} {g : Nat} (hh : 2≤h.count g) :
    ∃r, r.Sublist h ∧ h.Perm (g::g::r) := by
  have first : g∈h := List.count_pos_iff.mp (by omega)
  have next : g∈h.erase g := by
    apply List.count_pos_iff.mp; rw [List.count_erase_self]; omega
  exact ⟨_,List.erase_sublist.trans List.erase_sublist,
    (List.perm_cons_erase first).trans ((List.perm_cons_erase next).cons g)⟩

/-- If the largest target is smaller than the core order, a repeated
item can be removed while keeping at least two subdivision vertices,
the maximum bound, and the single three. -/
theorem single_three_pair {h : List Nat} {t : Nat} (size : 8≤h.length) (two : 2≤t)
    (input : Input h t) (single : h.count 3=1) (small : ∀d∈h,d<h.length) :
    ∃g r s, 4≤g ∧ 2≤s ∧ h.Perm (g::g::r) ∧ r.count 3=1 ∧
      Input r s ∧ s+g-4=t := by
  obtain ⟨⟨sort,low⟩,vol,cap⟩ := input
  have pick : ∃g,2≤h.count g ∧ (g=4 ∨ h.count 4≤1) := by
    by_cases h4 : 2≤h.count 4
    · exact ⟨4,h4,.inl rfl⟩
    obtain ⟨g,hg⟩ := repeat_when_small h (fun d m => ⟨low d m,small d m⟩) size
    exact ⟨g,hg,.inr (by omega)⟩
  obtain ⟨g,mul,typeg⟩ := pick
  obtain ⟨r,sub,pm⟩ := rem_pair mul
  have gm : g∈h := List.count_pos_iff.mp (by omega)
  have gl := low g gm
  have ng : g≠3 := by rintro rfl; omega
  have len := pm.length_eq; have sum := pm.sum_nat
  have cnt := pm.count_eq 3
  simp only [List.count_cons] at cnt
  simp [ng] at cnt
  simp only [List.length_cons] at len
  simp only [List.sum_cons] at sum
  have rlow : ∀d∈r,3≤d := fun d m => low d (sub.subset m)
  have r3 : r.count 3=1 := by omega
  let s := t+4-g
  have facts : 2≤s ∧ (∀d∈r,d+1≤r.length+s) ∧ s+g-4=t ∧ r.sum=4*r.length+2*s := by
    rcases typeg with rfl|less
    · have es : s=t := by dsimp [s]; omega
      rw [es]; refine ⟨two,?_,by omega,by omega⟩
      intro d m; have := small d (sub.subset m); omega
    · have r4 : r.count 4≤1 := Nat.le_trans (sub.count_le _) less
      have total := min5_defect r rlow
      have sg : g≤t+4 := by omega
      have es : s+g=t+4 := by dsimp [s]; omega
      refine ⟨by omega,?_,by omega,by omega⟩
      intro d m
      have hmax := small d (sub.subset m)
      have p := List.perm_cons_erase m
      have len' := p.length_eq
      have sum' := p.sum_nat
      have min' := min5_defect (r.erase d) (fun v hv => rlow v (List.mem_of_mem_erase hv))
      have c3 := (List.erase_sublist (l:=r) (a:=d)).count_le 3
      have c4 := (List.erase_sublist (l:=r) (a:=d)).count_le 4
      simp only [List.length_cons] at len'
      simp only [List.sum_cons] at sum'
      omega
  obtain ⟨ss,upper,rest,reduced⟩ := facts
  exact ⟨g,r,s,by omega,ss,pm,r3,⟨⟨sort.sublist sub,rlow⟩,reduced,upper⟩,rest⟩


private theorem reduced_small {r : List Nat} {s g : Nat} (small : r.length=6 ∨ r.length=7)
    (ss : 2≤s) (gg : 4≤g) (input : Input r s) (one : r.count 3=1) :
    Planaric (List.replicate (s+g-4) 2 ++ g::g::r) := by
  obtain ⟨⟨sorted,lo⟩,vol,cap⟩ := input
  match r with
  | [a,b,c,d,e,f] =>
    have ha := cap a (by simp); have lf := lo f (by simp)
    simp [List.pairwise_cons] at sorted
    simp only [List.length_cons,List.length_nil,List.sum_cons,List.sum_nil] at vol ha
    have some3 : 3∈[a,b,c,d,e,f] := List.count_pos_iff.mp (by omega)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at some3
    have f3 : f=3 := by omega
    subst f
    have e4 : 4≤e := by
      apply Nat.le_of_not_gt; intro no
      have eqn : e=3 := by omega
      simp [eqn,List.count_cons] at one; omega
    by_cases bad : a=5 ∧ e=5
    · obtain ⟨rfl,rfl⟩ := bad
      have eqn : b=5 ∧ c=5 ∧ d=5 ∧ s=2 := by omega
      obtain ⟨rfl,rfl,rfl,rfl⟩ := eqn
      simpa only [show 2+g-4=g-2 by omega] using repair_pair g gg
    · apply restore_equal_pair ss (by omega)
      apply (planaric_perm List.perm_append_comm).mp
      exact upper_six_one_three a b c d e s (by omega) (by omega) (by omega) (by omega) e4
        (by omega) (by omega) (by omega) bad
  | [a,b,c,d,e,f,g'] =>
    have ha := cap a (by simp); have lf := lo g' (by simp)
    simp [List.pairwise_cons] at sorted
    simp only [List.length_cons,List.length_nil,List.sum_cons,List.sum_nil] at vol ha
    apply restore_equal_pair ss (by omega)
    apply (planaric_perm List.perm_append_comm).mp
    apply upper_seven_numeric a b c d e f g' s <;> omega
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | _::_::_::_::_::_::_::_::_ => simp at small

/-- The minimum-four part needed from the independent classification. -/
def MinimumFourPositive : Prop :=
  ∀h t, 8≤h.length → 2≤t → FourCore.Input h t → Planaric (List.replicate t 2++h)

private theorem four_residual {r : List Nat} {t : Nat} (four : MinimumFourPositive)
    (size : 7≤r.length) (two : 2≤t) (data : FourCore.Input r t) :
    Planaric (List.replicate t 2++r) := by
  by_cases ns : 8≤r.length
  · exact four r t ns two data
  have ln : r.length=7 := by omega
  obtain ⟨sort,lo,vol,cap⟩ := data
  match r with
  | [a,b,c,d,e,f,g] =>
    have high := cap a (by simp); have low := lo g (by simp)
    simp [List.pairwise_cons] at sort
    simp only [List.length_cons,List.length_nil,List.sum_cons,List.sum_nil] at vol high
    apply (planaric_perm List.perm_append_comm).mp
    apply SevenFour.min_four a b c d e f g t <;> omega
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] |
      _::_::_::_::_::_::_::_::_ => simp at ln

private theorem single_when_high (four : MinimumFourPositive) {a t : Nat} {xs : List Nat}
    (size : 8≤(a::xs).length) (high : (a::xs).length≤a) (two : 2≤t)
    (one : (a::xs).count 3=1) (input : Input (a::xs) t) :
    Planaric (List.replicate t 2 ++ a::xs) := by
  obtain ⟨⟨order,minimum⟩,vol,cap⟩ := input
  have ha := cap a (by simp)
  by_cases univ : a=xs.length+t
  · apply Universal.boundary (j:=0) xs (by simp at size; omega) order.of_cons
      (fun v m => minimum v (by simp [m])) (by decide) univ
    simpa using vol
  have ne : a≠3 := by omega
  have count : xs.count 3=1 := by simpa [List.count_cons,ne] using one
  have mem : 3∈xs := List.count_pos_iff.mp (by omega)
  let rs := xs.erase 3
  have pm : xs.Perm (3::rs) := List.perm_cons_erase mem
  have len := pm.length_eq; have sum := pm.sum_nat
  simp only [List.length_cons] at len size high ha
  simp only [List.sum_cons] at sum
  let raw := (a-1)::rs
  let le := fun i j : Nat => decide (i≥j)
  let sr := raw.mergeSort le
  have perm : sr.Perm raw := List.mergeSort_perm .. 
  have srOrd : sr.Pairwise (·≥·) := by
    simpa [sr,le] using List.pairwise_mergeSort (le:=le) (by simp [le]; omega)
      (by simp [le]; omega) raw
  have lc := perm.length_eq
  have sc := perm.sum_nat
  simp only [raw,List.length_cons,List.sum_cons] at lc sc
  simp only [List.sum_cons,List.length_cons] at vol
  have inputR : FourCore.Input sr t := by
    refine ⟨srOrd,?_,by omega,?_⟩
    · intro d md
      have m : d=a-1 ∨ d∈rs := List.mem_cons.mp (perm.mem_iff.mp md)
      rcases m with e|e
      · omega
      · have old := minimum d (List.mem_cons_of_mem _ (List.mem_of_mem_erase e))
        have n3 : rs.count 3=0 := by simp [rs,count]
        have ne3 : d≠3 := by intro same; subst d; have := List.count_pos_iff.mpr e; omega
        omega
    · intro d md
      rcases List.mem_cons.mp (perm.mem_iff.mp md) with e|e
      · change d=a-1 at e; omega
      · have m : d∈xs := List.mem_of_mem_erase e
        have := List.rel_of_pairwise_cons order m; omega
  have sortedPlan := four_residual four (by omega) two inputR
  have rawPlan := (planaric_perm (perm.append_left _)).mp sortedPlan
  have sh : Planaric ((a-1)::(rs++List.replicate t 2)) :=
    (planaric_perm (List.perm_append_comm (l₁:=List.replicate t 2) (l₂:=raw))).mp rawPlan
  have raised := promote_high_hub rs sh (by omega)
  have ae : a-1+1=a := by omega
  rw [ae] at raised
  apply (planaric_perm _).mp raised
  apply List.perm_iff_count.mpr; intro v
  have counts := pm.count_eq v
  simp only [List.count_cons,List.count_append] at counts ⊢; omega

/-- A single three at positive budget of at least two reduces completely
to the independent minimum-four classification. -/
theorem single_three_of_minimum_four (four : MinimumFourPositive) {h : List Nat} {t : Nat}
    (size : 8≤h.length) (two : 2≤t) (input : Input h t) (one : h.count 3=1) :
    Planaric (List.replicate t 2++h) := by
  generalize hn : h.length=n at size
  induction n using Nat.strongRecOn generalizing h t with
  | ind n ih =>
    by_cases big : ∃v∈h,n≤v
    · obtain ⟨v,mem,large⟩ := big
      cases h with
      | nil => contradiction
      | cons a xs =>
        apply single_when_high four (by omega) _ two one input
        rcases List.mem_cons.mp mem with e|e
        · omega
        · have := List.rel_of_pairwise_cons input.1.1 e; omega
    have small : ∀v∈h,v<h.length := fun v m => Nat.lt_of_not_ge (fun no => big ⟨v,m,hn ▸ no⟩)
    obtain ⟨g,r,s,gg,ss,perm,ro,data,restore⟩ :=
      single_three_pair (by omega) two input one small
    have ln := perm.length_eq; simp only [List.length_cons] at ln
    apply (planaric_perm (perm.append_left _)).mpr
    rw [← restore]
    by_cases enough : 8≤r.length
    · apply restore_equal_pair ss (by omega)
      apply ih r.length (by omega) (h:=r) (t:=s) <;> first | exact data | exact ro | omega
    · exact reduced_small (by omega) ss gg data ro

/-- All upper-boundary cores of order at least eight with at least two
degree-two vertices follow from the minimum-four case. -/
theorem upper_of_minimum_four (four : MinimumFourPositive)
    {h : List Nat} {t : Nat} (size : 8≤h.length) (two : 2≤t) (input : Input h t) :
    Planaric (List.replicate t 2++h) := by
  apply upper_of_at_most_one_from 2 (by decide) _ size two input
  intro r s large positive data few
  by_cases one : r.count 3=1
  · exact single_three_of_minimum_four four large positive data one
  obtain ⟨⟨sort,low⟩,vol,cap⟩ := data
  apply four r s large positive ⟨sort,?_,vol,cap⟩
  intro x m
  have three := low x m
  have ne : x≠3 := by
    rintro rfl
    have nz := List.count_pos_iff.mpr m
    omega
  omega

end SparseBoundary.Fan.Three
