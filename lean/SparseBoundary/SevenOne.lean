import SparseBoundary.SevenTwo

set_option maxHeartbeats 4000000

namespace SparseBoundary.SevenOne
open Graph

private theorem split_three (l m n a b c z : Nat) (la : l≤a) (mb : m≤b) (nc : n≤c)
    (lower : l+m+n≤z) (upper : z≤a+b+c) :
    ∃ x y w, x+y+w=z ∧ l≤x ∧ x≤a ∧ m≤y ∧ y≤b ∧ n≤w ∧ w≤c := by
  let x := min a (z-m-n)
  let y := min b (z-x-n)
  refine ⟨x,y,z-x-y,?_⟩
  dsimp [x,y,Nat.min_def]
  split <;> split <;> omega

theorem weights (A B C D E F t : Nat) (sum : A+B+C+D+E+F=2*t)
    (fs : F≤t) (neighbors : F≤A+B+C) (ca : A≤t) (cb : B+D≤t) (cc : C+E≤t)
    (rd : D≤t-F) (re : E≤t-F) :
    ∃ W : List (Fin 7 × Fin 7), W.length=t ∧
      (∀ e ∈ W, SevenUniversal.Layer0.wheel.adj e.1 e.2 = true) ∧
      [increments W 0,increments W 1,increments W 2,increments W 3,increments W 4,
        increments W 5,increments W 6]=[A,B,C,D,E,F,0] := by
  let H := SevenUniversal.Layer0.wheel
  let m := t-F
  obtain ⟨x,y,z,sxyz,lx,hx,ly,hy,lz,hz⟩ := split_three (A-m) (B+D-m) (C+E-m) A B C F
    (by omega) (by dsimp [m]; omega) (by dsimp [m]; omega) (by dsimp [m]; omega) neighbors
  have scale : A-x+(B-y)+(C-z)+D+E=2*m := by dsimp [m]; omega
  have cap : A-x≤m ∧ B-y+D≤m ∧ C-z+E≤m := by omega
  obtain ⟨P,pLen,pEdges,pInc⟩ := SevenTwo.weights H true (by decide +kernel)
    (A-x) (B-y) (C-z) D E m scale (by simpa using cap)
  simp only [List.cons.injEq,and_true] at pInc
  obtain ⟨p0,p1,p2,p3,p4,p5,p6⟩ := pInc
  let Q : List (Fin 7 × Fin 7) := List.replicate x (0,5) ++ List.replicate y (1,5) ++ List.replicate z (2,5)
  have qEdges e (he : e ∈ Q) : H.adj e.1 e.2 = true := by
    simp only [Q,List.mem_append,List.mem_replicate] at he
    rcases he with ((⟨_,rfl⟩|⟨_,rfl⟩)|⟨_,rfl⟩) <;> decide +kernel
  have qInc : [increments Q 0,increments Q 1,increments Q 2,increments Q 3,
      increments Q 4,increments Q 5,increments Q 6]=[x,y,z,0,0,F,0] := by
    simp only [Q,increments,List.countP_append,List.countP_replicate]
    change [x+0+0,0+y+0,0+0+z,0,0,x+y+z,0]=_
    simp [sxyz]
  simp only [List.cons.injEq,and_true] at qInc
  obtain ⟨q0,q1,q2,q3,q4,q5,q6⟩ := qInc
  have ens e (he : e ∈ P++Q) : H.adj e.1 e.2 = true := by
    rcases List.mem_append.mp he with h|h
    · exact pEdges e h
    · exact qEdges e h
  have inc (i : Fin 7) : increments (P++Q) i = increments P i + increments Q i := List.countP_append
  have elen : (P++Q).length=t := by
    simp only [Q,List.length_append,List.length_replicate,pLen]
    dsimp [m]; omega
  refine ⟨P++Q,elen,ens,?_⟩
  simp only [inc,p0,p1,p2,p3,p4,p5,p6,q0,q1,q2,q3,q4,q5,q6,
    Nat.add_zero,Nat.zero_add,Nat.sub_add_cancel hx,Nat.sub_add_cancel hy,Nat.sub_add_cancel hz]

private theorem satellite (A B C D E F t : Nat) (sum : A+B+C+D+E+F=2*t)
    (fs : F≤t) (neighbors : F≤A+B+C) (ca : A≤t) (cb : B+D≤t) (cc : C+E≤t)
    (rd : D≤t-F) (re : E≤t-F) :
    Planaric ([6+A,4+B,4+C,4+D,4+E,3+F,3] ++ List.replicate t 2) := by
  let H := SevenUniversal.Layer0.wheel
  obtain ⟨W,len,edge,inc⟩ := weights A B C D E F t sum fs neighbors ca cb cc rd re
  simp only [List.cons.injEq,and_true] at inc
  obtain ⟨i0,i1,i2,i3,i4,i5,i6⟩ := inc
  have hdeg : H.degree 0=6 ∧ H.degree 1=4 ∧ H.degree 2=4 ∧ H.degree 3=4 ∧
      H.degree 4=4 ∧ H.degree 5=3 ∧ H.degree 6=3 := by decide +kernel
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := hdeg
  have wp := expanded_planaric SevenUniversal.Layer0.wheel_planar W edge
  rw [len] at wp
  apply (planaric_perm List.perm_append_comm).mp
  change Planaric (List.replicate t 2 ++ [H.degree 0+increments W 0,H.degree 1+increments W 1,
    H.degree 2+increments W 2,H.degree 3+increments W 3,H.degree 4+increments W 4,
    H.degree 5+increments W 5,H.degree 6+increments W 6]) at wp
  simpa only [i0,i1,i2,i3,i4,i5,i6,h0,h1,h2,h3,h4,h5,h6,Nat.add_zero] using wp

private theorem finite (j : Fin 3) : Planaric
    ([ [5,4,4,4,4,4,3], [5,5,5,4,4,4,3,2], [5,5,5,5,5,4,3,2,2] ] : List (List Nat))[j] := by
  let E : List (List (Fin 7 × Fin 7)) := [[], [(1,4)], [(1,4),(2,3)]]
  have good : ∀ j : Fin 3, ∀ e ∈ E[j], LeafRepair3.oneThreeBase.adj e.1 e.2 = true := by decide +kernel
  have pl := expanded_planaric LeafRepair3.oneThreeBase_planar E[j] (good j)
  have profiles : ∀ j : Fin 3, (List.replicate E[j].length 2 ++
      List.ofFn (fun i => LeafRepair3.oneThreeBase.degree i + increments E[j] i)).Perm
      ([ [5,4,4,4,4,4,3], [5,5,5,4,4,4,3,2], [5,5,5,5,5,4,3,2,2] ] : List (List Nat))[j] := by decide +kernel
  exact (planaric_perm (profiles j)).mp pl

/-- The entire one-three branch for seven core vertices on the upper boundary. -/
theorem one_three (a b c d e f t : Nat) (ab : b≤a) (bc : c≤b) (cd : d≤c) (de : e≤d) (ef : f≤e)
    (lo : 4≤f) (hs : a+b+c+d+e+f=25+2*t) (maximum : a≤6+t) :
    Planaric ([a,b,c,d,e,f,3] ++ List.replicate t 2) := by
  by_cases cover : 6≤a ∧ f-3≤t ∧ f+d≤t+7 ∧ f-3≤a-6+(b-4)+(c-4)
  · have wp := satellite (a-6) (b-4) (c-4) (e-4) (d-4) (f-3) t
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [show 6+(a-6)=a by omega,show 4+(b-4)=b by omega,show 4+(c-4)=c by omega,
      show 4+(d-4)=d by omega,show 4+(e-4)=e by omega,show 3+(f-3)=f by omega] at wp
    exact (planaric_perm (((List.Perm.swap d e [f,3]).cons c |>.cons b |>.cons a).append_right _)).mp wp
  have exc :
      (a=5 ∧ b=4 ∧ c=4 ∧ d=4 ∧ e=4 ∧ f=4 ∧ t=0) ∨
      (a=5 ∧ b=5 ∧ c=5 ∧ d=4 ∧ e=4 ∧ f=4 ∧ t=1) ∨
      (a=5 ∧ b=5 ∧ c=5 ∧ d=5 ∧ e=5 ∧ f=4 ∧ t=2) := by
    by_cases q : 6≤a <;> by_cases r : f-3≤t <;> by_cases u : f+d≤t+7 <;>
      first | (exfalso; omega) | (by_cases v : t=0 <;> by_cases w : t=1 <;> omega)
  rcases exc with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact finite 0
  · exact finite 1
  · exact finite 2

end SparseBoundary.SevenOne
