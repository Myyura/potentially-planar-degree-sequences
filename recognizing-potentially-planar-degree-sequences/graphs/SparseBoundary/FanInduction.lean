import SparseBoundary.FanTerminal
import SparseBoundary.GraphPairInsertion
import SparseBoundary.GraphSixClassification

namespace SparseBoundary.Fan

private theorem min_total (h : List Nat) (hm : ∀d∈h, 5≤d) : 5*h.length≤h.sum := by
  induction h with
  | nil => simp
  | cons x h ih =>
    have hx := hm x (by simp)
    have hh := ih (fun d hd => hm d (by simp [hd]))
    simp only [List.length_cons,List.sum_cons]; omega

private theorem six_high (h : List Nat) (t : Nat) (size : h.length=6)
    (sorted : h.Pairwise (·≥·)) (minim : ∀ d∈h, 5≤d)
    (vol : h.sum=4*h.length+2*t) (cap : ∀d∈h, d+1≤h.length+t) :
    Planaric (List.replicate t 2++h) := by
  have shape : ∃ a b c d e f, h=[a,b,c,d,e,f] := by
    exact ⟨h[0]'(by omega),h[1]'(by omega),h[2]'(by omega),h[3]'(by omega),
      h[4]'(by omega),h[5]'(by omega),by
        apply List.ext_getElem
        · simpa using size
        · intro i hi _
          have eqn : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
          rcases eqn with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl⟩
  obtain ⟨a,b,c,d,e,f,rfl⟩ := shape
  have ha := cap a (by simp)
  have low := minim f (by simp)
  simp only [List.length_cons,List.length_nil,List.sum_cons,List.sum_nil] at vol ha
  apply (planaric_perm List.perm_append_comm).mp
  simp [List.pairwise_cons] at sorted
  apply six_min_four a b c d e f t t <;> first | grind | omega

/-- Numerical upper-boundary hypotheses. These are sufficient construction
conditions at minimum core degree five. -/
def UpperHigh (h : List Nat) (t : Nat) : Prop :=
  h.Pairwise (·≥·) ∧ (∀d∈h, 5≤d) ∧ h.sum=4*h.length+2*t ∧
  (∀d∈h, d+1≤h.length+t)

/-- Strong induction discharges every upper-boundary case of minimum five
and order six or more from the size-seven statement alone. -/
theorem upper_min_five_of_seven
    (seven : ∀ h t, h.length=7 → UpperHigh h t → Planaric (List.replicate t 2 ++ h))
    (h : List Nat) (t : Nat) (hn : 6≤h.length) (input : UpperHigh h t) :
    Planaric (List.replicate t 2 ++ h) := by
  generalize hn' : h.length=n at *
  induction n using Nat.strongRecOn generalizing h t with
  | ind n ih =>
    obtain ⟨sort,low,vol,cap⟩ := input
    by_cases h6 : n=6
    · exact six_high h t (by omega) sort low vol cap
    by_cases h7 : n=7
    · exact seven h t (by omega) ⟨sort,low,vol,cap⟩
    have eight : 8≤n := by omega
    obtain ⟨a,b,c,us,rfl⟩ : ∃a b c us, h=a::b::c::us := by
      cases h with
      | nil => simp at hn'; omega
      | cons a h =>
        cases h with
        | nil => simp at hn'; omega
        | cons b h =>
          cases h with
          | nil => simp at hn'; omega
          | cons c h => exact ⟨a,b,c,h,rfl⟩
    rcases min_five_planar_or_pair (p:=n) (t:=t) (k:=0) us (by simpa using hn'.symm) eight
      (by decide) sort low (by simpa [hn'] using vol) (by simpa [hn'] using cap a (by simp))
      with done|⟨g,rs,perm,bound⟩
    · exact done
    have pn := perm.length_eq
    have ps := perm.sum_nat
    have rg : 5≤g := low g (perm.mem_iff.mpr (by simp))
    have rl : ∀d∈rs, 5≤d := fun d hd => low d (perm.mem_iff.mpr (by simp [hd]))
    have rh := min_total rs rl
    let s := t+4-g
    have ln : n=rs.length+2 := by simp only [List.length_cons] at hn' pn; omega
    have total : g+g+rs.sum=4*n+2*t := by
      rw [← hn']
      simpa only [← vol,List.sum_cons,Nat.add_assoc] using ps.symm
    have budget : 2≤s := by dsimp [s]; omega
    have restore : s+g-4=t := by dsimp [s]; omega
    let le := fun a b : Nat => decide (a≥b)
    let ss := rs.mergeSort le
    have rel : ss.Perm rs := List.mergeSort_perm .. 
    have ssSorted : ss.Pairwise (·≥·) := by
      simpa [le,ss] using List.pairwise_mergeSort (le:=le) (by simp [le]; omega)
        (by simp [le]; omega) rs
    have nss := rel.length_eq
    have hss := rel.sum_nat
    have rsInput : UpperHigh ss s := by
      refine ⟨ssSorted,fun d hd => rl d (rel.mem_iff.mp hd),?_,?_⟩
      · dsimp [s]; omega
      · intro d hd; have := bound d (rel.mem_iff.mp hd); dsimp [s]; omega
    have smaller := ih ss.length (by omega) ss s rsInput rfl (by omega)
    have realized := restore_equal_pair budget (by omega : 3≤g)
      ((planaric_perm (rel.append_left _)).mp smaller)
    rw [restore] at realized
    exact (planaric_perm (perm.append_left _)).mpr realized

end SparseBoundary.Fan
