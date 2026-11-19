import SparseBoundary.FanInduction
import SparseBoundary.FanSevenTable

namespace SparseBoundary.Fan

/-- With seven core vertices of minimum degree five, the cone and the two
fan constructions reduce the problem to the bounded pentagonal-bipyramid
table. The hypotheses refer only to the entries of the profile. -/
theorem upper_seven_min_five (h : List Nat) (t : Nat) (size : h.length=7) (data : UpperHigh h t) :
    Planaric (List.replicate t 2++h) := by
  obtain ⟨sorted,low,vol,maxim⟩ := data
  obtain ⟨a,b,c,us,rfl⟩ : ∃a b c us, h=a::b::c::us := by
    cases h with
    | nil => simp at size
    | cons a h =>
      cases h with
      | nil => simp at size
      | cons b h =>
        cases h with
        | nil => simp at size
        | cons c h => exact ⟨a,b,c,h,rfl⟩
  have q : (c::us).length=5 := by simp only [List.length_cons] at *; omega
  have n : (b::c::us).length=6 := by simp only [List.length_cons] at *; omega
  have total : a+b+(c::us).sum=28+2*t := by rw [size] at vol; simp only [List.sum_cons] at *; omega
  have maxbound := maxim a (by simp); rw [size] at maxbound
  have ab : b≤a := List.rel_of_pairwise_cons sorted (by simp)
  have bc : c≤b := List.rel_of_pairwise_cons sorted.of_cons (by simp)
  have b5 := low b (by simp)
  have c5 := low c (by simp)
  have tailLow : ∀d∈(c::us),5≤d := fun d hd => low d (by simp [hd])
  by_cases cone : t+5≤a
  · apply cone_range_planaric (b::c::us) (by omega) (fun d hd => low d (by simp [hd]))
      (j:=0) _ (by omega) (by omega)
    simp only [List.sum_cons,List.length_cons] at *; omega
  by_cases near : a=t+4
  · apply near_cone_planaric (c::us) (by omega) (by omega) near _ tailLow
    omega
  by_cases wide : 6≤b ∧ 10+c≤a+b
  · have mx : ∀d∈(c::us), d≤c := by
      intro d hd
      rcases List.mem_cons.mp hd with e|m
      · omega
      · exact List.rel_of_pairwise_cons sorted.of_cons.of_cons m
    have weights := degree_weights_paired (a:=a) (b:=b) (c:=c) (p:=7) (c::us)
      (by omega) (by simp) sorted.of_cons.of_cons (by omega) ab tailLow mx (by omega)
      (by omega) (by omega) (by omega)
    apply degree_weights_planaric_with_twos weights (by simp) (by omega) (by omega)
      (fun d hd => Nat.le_trans (by decide) (tailLow d hd)) (by omega)
  have bounded : a≤9 := by
    by_cases b6 : 6≤b
    · omega
    have all5 : b::c::us=List.replicate 6 5 := by
      apply List.eq_replicate_iff.mpr
      refine ⟨n,?_⟩
      intro d hd
      have hm := low d (by simp [hd])
      rcases List.mem_cons.mp hd with he|mem
      · omega
      · have := List.rel_of_pairwise_cons sorted.of_cons mem; omega
    have h5 := congrArg List.sum all5
    simp only [List.sum_cons,List.sum_replicate_nat] at h5 total; omega
  have bounds : ∀d∈a::b::c::us,5≤d ∧ d≤9 := by
    intro d hd
    refine ⟨low d hd,?_⟩
    rcases List.mem_cons.mp hd with he|mem
    · omega
    · have := List.rel_of_pairwise_cons sorted mem; omega
  rcases SevenTable.bounded size sorted bounds (by simpa [size] using vol) with p|exc|exc
  · exact p
  · simp only [List.cons.injEq] at exc; omega
  · simp only [List.cons.injEq] at exc; omega

/-- Complete upper-boundary realization for every order six or more at
minimum core degree five. -/
theorem upper_min_five (h : List Nat) (t : Nat) (hn : 6≤h.length) (input : UpperHigh h t) :
    Planaric (List.replicate t 2++h) :=
  upper_min_five_of_seven upper_seven_min_five h t hn input


/-- Complete corresponding lower boundary. A universal hub uses the cone
construction, and every smaller maximum permits one ordinary subdivision
of the upper-boundary realization at budget t-1. -/
theorem lower_min_five (h : List Nat) (t : Nat) (hn : 6≤h.length)
    (sorted : h.Pairwise (·≥·)) (low : ∀d∈h,5≤d) (vol : h.sum+2=4*h.length+2*t)
    (cap : ∀d∈h,d+1≤h.length+t) : Planaric (List.replicate t 2++h) := by
  cases h with
  | nil => simp at hn
  | cons a us =>
    have ha := cap a (by simp); have hm := low a (by simp)
    simp only [List.length_cons,List.sum_cons] at ha hn vol
    have tail : ∀d∈us,5≤d := fun d hd => low d (by simp [hd])
    by_cases cone : t+4≤a
    · exact cone_range_planaric us (by omega) tail (j:=1) vol (by omega) (by omega)
    have sumlow (v : List Nat) (l : ∀x∈v,5≤x) : 5*v.length≤v.sum := by
      induction v with
      | nil => simp
      | cons x v ih =>
        have := l x (by simp)
        have := ih (fun z m => l z (by simp [m]))
        simp; omega
    have hsum := sumlow us tail
    have pos : 1≤t := by omega
    have smaller : UpperHigh (a::us) (t-1) := by
      refine ⟨sorted,low,?_,?_⟩
      · simp only [List.sum_cons,List.length_cons]; omega
      · intro d hd
        rcases List.mem_cons.mp hd with e|e
        · simp; omega
        · have := List.rel_of_pairwise_cons sorted e; simp; omega
    have graph := upper_min_five (a::us) (t-1) (by simpa using hn) smaller
    have ext := planaric_add_two graph ⟨a,List.mem_append_right _ (by simp),by omega⟩
    have tEq : t=(t-1)+1 := by omega
    simpa only [← List.cons_append,← List.replicate_succ,← tEq] using ext

end SparseBoundary.Fan
