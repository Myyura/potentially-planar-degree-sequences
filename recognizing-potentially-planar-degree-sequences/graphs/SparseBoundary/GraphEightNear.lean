import SparseBoundary.GraphFourCone
import SparseBoundary.GraphWeighted

namespace SparseBoundary.FourCone
open Graph

private def support8 : Graph 8 := ⟨40295675⟩
private def rank8 (i : Fin 8) : Nat := ([0,4,1,3,6,7,2,5] : List Nat)[i]

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem support8_planar : support8.Planar := by
  apply Fan.outer_order_planar (v:=0)
  exact ⟨rank8,by decide +kernel,by decide +kernel⟩

private theorem rim8_small : ∀ i : Fin 7, i.val≠0 → support8.degree i.succ≤4 := by decide +kernel

private def other8 : Graph 8 := ⟨175163007⟩

private theorem other8_planar : other8.Planar := by
  apply Fan.outer_order_planar (v:=0)
  exact ⟨Fin.val,fun _ _ => Fin.ext,by decide +kernel⟩

private theorem fixed8 : Planaric (List.replicate 2 2 ++ [8,4,4,4,4,4,4,4]) := by
  let E : List (Fin 8 × Fin 8) := [(0,2),(5,6)]
  have p := expanded_planaric other8_planar E (by decide +kernel)
  have row : List.ofFn (fun i => other8.degree i + increments E i)=[8,4,4,4,4,4,4,4] := by decide +kernel
  exact (row ▸ p)

/-- The next-to-universal eight-core case, including its unique case where
    all seven rim targets are four. -/
theorem eight_near (a b c d e f g h t : Nat)
    (order : [b,c,d,e,f,g,h].Pairwise (·≥·)) (minimum : 4≤h)
    (vol : a+b+c+d+e+f+g+h=32+2*t) (hub : a=t+6) :
    Planaric (List.replicate t 2 ++ [a,b,c,d,e,f,g,h]) := by
  simp at order
  by_cases high : 5≤b
  · let us := [b,c,d,e,f,g,h]
    have tgt (i : Fin 7) : support8.degree i.succ≤us[i.val]'(by simp [us]) := by
      by_cases z : i.val=0
      · have eqn : i=0 := Fin.ext z
        subst i; change 5≤b; exact high
      · have cap := rim8_small i z
        have lower : ∀v∈us,4≤v := by simp [us]; omega
        exact Nat.le_trans cap (lower _ (List.getElem_mem _))
    obtain ⟨m,sum,p⟩ := Fan.expand_spokes us support8 support8_planar (show ∀ i : Fin 7,support8.adj 0 i.succ=true by decide +kernel) tgt
    have base : ((List.finRange 7).map (fun i => support8.degree i.succ)).sum=27 := by decide +kernel
    change m+((List.finRange 7).map (fun i => support8.degree i.succ)).sum=us.sum at sum
    rw [base] at sum
    simp [us] at sum
    have pole : support8.degree 0=7 := by decide +kernel
    rw [pole,show 7+m=a by omega] at p
    have pp := (planaric_perm List.perm_middle).mpr p
    have aux := planaric_add_two pp ⟨a,List.mem_append_right _ (by simp),by omega⟩
    have tm : t=m+1 := by omega
    simpa [tm,List.replicate_succ,us] using aux
  · have b4 : b=4 := by omega
    have c4 : c=4 := by omega
    have d4 : d=4 := by omega
    have e4 : e=4 := by omega
    have f4 : f=4 := by omega
    have g4 : g=4 := by omega
    have h4 : h=4 := by omega
    have a8 : a=8 := by omega
    have t2 : t=2 := by omega
    simpa [a8,b4,c4,d4,e4,f4,g4,h4,t2] using fixed8

end SparseBoundary.FourCone
