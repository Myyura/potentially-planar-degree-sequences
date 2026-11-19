import SparseBoundary.LeafRepairs
import SparseBoundary.GraphWeighted

namespace SparseBoundary.SevenCore

open Graph

private theorem labels (f : Fin 7 → Nat) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6] := rfl

/-- An explicit planar realization for seven core vertices, exactly
    four of degree three, on the upper boundary away from its two
    exceptional triples. -/
theorem four_threes (a b c t : Nat) (hab : b ≤ a) (hbc : c ≤ b) (hc : 4 ≤ c)
    (budget : a + b + c = 2*t+16) (maximum : a ≤ t+6)
    (ex1 : (a,b,c) ≠ (6,5,5)) (ex2 : (a,b,c) ≠ (6,6,6)) :
    Planaric ([a,b,c,3,3,3,3] ++ List.replicate t 2) := by
  obtain ⟨G,hp,deg,h01,h02,h12⟩ := LeafRepair4.triangle_support
  simp only [ne_eq,Prod.mk.injEq] at ex1 ex2
  let u := (a+b-c-8)/2
  let v := (a+c-b-4)/2
  let w := (b+c-a-4)/2
  have uv : 6+u+v=a := by dsimp [u,v]; omega
  have uw : 6+u+w=b := by dsimp [u,w]; omega
  have vw : 4+v+w=c := by dsimp [v,w]; omega
  have count : u+v+w=t := by omega
  let E : List (Fin 7 × Fin 7) := List.replicate u (0,1) ++
    List.replicate v (0,2) ++ List.replicate w (1,2)
  have good e (he : e ∈ E) : G.adj e.1 e.2 = true := by
    simp only [E,List.mem_append,List.mem_replicate] at he
    rcases he with ((⟨_,rfl⟩|⟨_,rfl⟩)|⟨_,rfl⟩)
    · exact h01
    · exact h02
    · exact h12
  have pl := expanded_planaric hp E good
  rw [labels] at deg pl
  simp only [List.cons.injEq,and_true] at deg
  obtain ⟨d0,d1,d2,d3,d4,d5,d6⟩ := deg
  have weight (i : Fin 7) : increments E i =
      (if pairRow 0 1 i then u else 0) + (if pairRow 0 2 i then v else 0) +
      (if pairRow 1 2 i then w else 0) := by simp [increments,E,List.countP_replicate,Nat.add_assoc]
  have weights : [increments E 0,increments E 1,increments E 2,increments E 3,
      increments E 4,increments E 5,increments E 6]=[u+v,u+w,v+w,0,0,0,0] := by
    simp only [weight]
    change [u+v+0,u+0+w,0+v+w,0,0,0,0]=_
    simp
  simp only [List.cons.injEq,and_true] at weights
  obtain ⟨w0,w1,w2,w3,w4,w5,w6⟩ := weights
  have len : E.length=t := by simpa [E,Nat.add_assoc] using count
  simp only [d0,d1,d2,d3,d4,d5,d6,w0,w1,w2,w3,w4,w5,w6,Nat.add_zero,
    ← Nat.add_assoc,uv,uw,vw,len] at pl
  exact (planaric_perm List.perm_append_comm).mp pl

end SparseBoundary.SevenCore
