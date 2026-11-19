import SparseBoundary.GraphMultipartite
import SparseBoundary.SevenUniversal
import SparseBoundary.LeafRepairs
import SparseBoundary.Repair3

set_option maxHeartbeats 12000000

namespace SparseBoundary.SevenTwo
open Graph

private def packed (a b c d e : Nat) : List (Fin 7) :=
  List.replicate a 0 ++ List.replicate b 1 ++ List.replicate c 2 ++
  List.replicate d 3 ++ List.replicate e 4

def getColor (wheel : Bool) (i : Fin 7) : Nat :=
  if wheel then [0,1,2,1,2,3,3][i] else [0,1,2,3,3,4,4][i]

theorem weights (H : Graph 7) (wheel : Bool)
    (edges : ∀ i j : Fin 7, i.val≤4 → j.val≤4 → getColor wheel i ≠ getColor wheel j → H.adj i j = true)
    (a b c d e t : Nat) (sum : a+b+c+d+e=2*t)
    (cap : if wheel then a≤t ∧ b+d≤t ∧ c+e≤t else a≤t ∧ b≤t ∧ c≤t ∧ d+e≤t) :
    ∃ E : List (Fin 7 × Fin 7), E.length = t ∧ (∀ e ∈ E, H.adj e.1 e.2 = true) ∧
      [increments E 0,increments E 1,increments E 2,increments E 3,
        increments E 4,increments E 5,increments E 6]=[a,b,c,d,e,0,0] := by
  let T := packed a b c d e
  have active i (hi : i ∈ T) : i.val≤4 := by
    simp only [T,packed,List.mem_append,List.mem_replicate] at hi
    rcases hi with ((((⟨_,rfl⟩|⟨_,rfl⟩)|⟨_,rfl⟩)|⟨_,rfl⟩)|⟨_,rfl⟩) <;> decide
  have caps (x : Nat) : (T.map (getColor wheel)).count x≤t := by
    simp only [T,packed,List.map_append,List.map_replicate,List.count_append,List.count_replicate]
    cases wheel
    · change ((if (0:Nat)==x then a else 0)+(if (1:Nat)==x then b else 0)+
        (if (2:Nat)==x then c else 0)+(if (3:Nat)==x then d else 0)+
        (if (3:Nat)==x then e else 0))≤t
      simp at cap
      simp only [beq_iff_eq]
      split <;> split <;> split <;> split <;> omega
    · change ((if (0:Nat)==x then a else 0)+(if (1:Nat)==x then b else 0)+
        (if (2:Nat)==x then c else 0)+(if (1:Nat)==x then d else 0)+
        (if (2:Nat)==x then e else 0))≤t
      simp at cap
      simp only [beq_iff_eq]
      split <;> split <;> split <;> omega
  obtain ⟨E,el,hcol,inc⟩ := cross_pairing (getColor wheel) T t
    (by simp only [T,packed,List.length_append,List.length_replicate]; omega) caps
  have good (q) (hq : q ∈ E) : H.adj q.1 q.2 = true := by
    apply edges _ _ _ _ (hcol q hq) <;> apply active <;> apply List.count_pos_iff.mp <;>
      rw [←inc] <;> apply List.countP_pos_iff.mpr <;> exact ⟨q,hq,by simp [pairRow]⟩
  refine ⟨E,el,good,?_⟩
  simp only [inc]
  simp only [T,packed,List.count_append,List.count_replicate]
  change [a+0+0+0+0,0+b+0+0+0,0+0+c+0+0,0+0+0+d+0,0+0+0+0+e,0,0]=_
  simp

private theorem lift (H : Graph 7) (plan : H.Planar) (wheel : Bool)
    (edges : ∀ i j : Fin 7, i.val≤4 → j.val≤4 → getColor wheel i ≠ getColor wheel j → H.adj i j = true)
    (a b c d e t : Nat) (sum : a+b+c+d+e=2*t)
    (cap : if wheel then a≤t ∧ b+d≤t ∧ c+e≤t else a≤t ∧ b≤t ∧ c≤t ∧ d+e≤t) :
    Planaric ([H.degree 0+a,H.degree 1+b,H.degree 2+c,H.degree 3+d,
      H.degree 4+e,H.degree 5,H.degree 6] ++ List.replicate t 2) := by
  obtain ⟨E,el,good,p⟩ := weights H wheel edges a b c d e t sum cap
  obtain ⟨s0,s1,s2,s3,s4,s5,s6⟩ : increments E 0=a ∧ increments E 1=b ∧
      increments E 2=c ∧ increments E 3=d ∧ increments E 4=e ∧
      increments E 5=0 ∧ increments E 6=0 := by simpa only [List.cons.injEq,and_true] using p
  have pl := expanded_planaric plan E good
  rw [el] at pl
  apply (planaric_perm List.perm_append_comm).mp
  change Planaric (List.replicate t 2 ++ [H.degree 0+increments E 0,H.degree 1+increments E 1,
    H.degree 2+increments E 2,H.degree 3+increments E 3,H.degree 4+increments E 4,
    H.degree 5+increments E 5,H.degree 6+increments E 6]) at pl
  simpa only [s0,s1,s2,s3,s4,s5,s6,Nat.add_zero] using pl

private theorem residual (j : Fin 4) : Planaric ([
  [5,5,4,4,4,3,3], [6,6,4,4,4,3,3,2], [5,5,5,5,4,3,3,2], [6,6,6,6,4,3,3,2,2,2]
  ] : List (List Nat))[j] := by
  let edges : List (List (Fin 7 × Fin 7)) := [[], [(0,1)], [(2,4)], [(0,1),(2,4),(2,4)]]
  let E := edges[j]
  have good : ∀ j : Fin 4, ∀ e ∈ edges[j], Repair3.sevenGraph.adj e.1 e.2 = true := by decide +kernel
  have pl := expanded_planaric Repair3.sevenGraph_planar E (good j)
  have profiles : ∀ i : Fin 4, (List.replicate edges[i].length 2 ++
      List.ofFn (fun v => Repair3.sevenGraph.degree v + increments edges[i] v)).Perm
      ([ [5,5,4,4,4,3,3], [6,6,4,4,4,3,3,2], [5,5,5,5,4,3,3,2],
         [6,6,6,6,4,3,3,2,2,2] ] : List (List Nat))[i] := by decide +kernel
  exact (planaric_perm (profiles j)).mp pl

/-- Seven core vertices, exactly two of degree three, on the upper boundary. -/
theorem two_threes (a b c d e t : Nat) (ab : b≤a) (bc : c≤b) (cd : d≤c) (de : e≤d)
    (lo : 4≤e) (sum : a+b+c+d+e=22+2*t) (maximum : a≤6+t) :
    Planaric ([a,b,c,d,e,3,3] ++ List.replicate t 2) := by
  by_cases dbl : 6≤b ∧ c≤t+4 ∧ d+e≤t+6
  · let H := LeafRepair4.doubleFan
    have p := lift H LeafRepair4.doubleFan_planar false (by decide +kernel)
      (a-6) (b-6) (c-4) (d-3) (e-3) t (by omega) (by simp; omega)
    have deg : H.degree 0=6 ∧ H.degree 1=6 ∧ H.degree 2=4 ∧ H.degree 3=3 ∧ H.degree 4=3 ∧ H.degree 5=3 ∧ H.degree 6=3 := by decide +kernel
    obtain ⟨d0,d1,d2,d3,d4,d5,d6⟩ := deg
    simp only [d0,d1,d2,d3,d4,d5,d6] at p
    simpa only [show 6+(a-6)=a by omega,show 6+(b-6)=b by omega,show 4+(c-4)=c by omega,
      show 3+(d-3)=d by omega,show 3+(e-3)=e by omega] using p
  by_cases wh : 6≤a ∧ b+e≤t+8 ∧ c+d≤t+8
  · let H := SevenUniversal.Layer0.wheel
    have p := lift H SevenUniversal.Layer0.wheel_planar true (by decide +kernel)
      (a-6) (b-4) (c-4) (e-4) (d-4) t (by omega) (by simp; omega)
    have deg : H.degree 0=6 ∧ H.degree 1=4 ∧ H.degree 2=4 ∧ H.degree 3=4 ∧ H.degree 4=4 ∧ H.degree 5=3 ∧ H.degree 6=3 := by decide +kernel
    obtain ⟨d0,d1,d2,d3,d4,d5,d6⟩ := deg
    simp only [d0,d1,d2,d3,d4,d5,d6] at p
    simp only [show 6+(a-6)=a by omega,show 4+(b-4)=b by omega,show 4+(c-4)=c by omega,
      show 4+(e-4)=e by omega,show 4+(d-4)=d by omega] at p
    apply (planaric_perm (d:=[a,b,c,e,d,3,3] ++ List.replicate t 2) _).mp p
    exact (List.Perm.cons a (List.Perm.cons b (List.Perm.cons c (List.Perm.swap d e [3,3])))).append_right _
  have exc :
    (a=5 ∧ b=5 ∧ c=4 ∧ d=4 ∧ e=4 ∧ t=0) ∨
    (a=6 ∧ b=6 ∧ c=4 ∧ d=4 ∧ e=4 ∧ t=1) ∨
    (a=5 ∧ b=5 ∧ c=5 ∧ d=5 ∧ e=4 ∧ t=1) ∨
    (a=6 ∧ b=6 ∧ c=6 ∧ d=6 ∧ e=4 ∧ t=3) := by
    by_cases p : 6≤b <;> by_cases q : c≤t+4 <;> by_cases r : d+e≤t+6 <;>
      by_cases x : 6≤a <;> by_cases y : b+e≤t+8 <;> by_cases z : c+d≤t+8 <;>
      first | contradiction | (exfalso; omega) | (by_cases u : d=4 <;> by_cases v : d=5 <;> omega)
  rcases exc with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact residual 0
  · exact residual 1
  · exact residual 2
  · exact residual 3

end SparseBoundary.SevenTwo
