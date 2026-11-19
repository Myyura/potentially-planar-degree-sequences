import SparseBoundary.SevenOne

namespace SparseBoundary.SevenFour
open Graph

set_option maxHeartbeats 40000000
set_option maxRecDepth 32768

private def smallProfiles : List (List Nat) := [
  [6, 4, 4, 4, 4, 4, 4, 2],
  [5, 5, 4, 4, 4, 4, 4, 2],
  [6, 6, 4, 4, 4, 4, 4, 2, 2],
  [6, 5, 5, 4, 4, 4, 4, 2, 2],
  [6, 6, 6, 4, 4, 4, 4, 2, 2, 2],
  [5, 5, 5, 5, 4, 4, 4, 2, 2],
  [6, 6, 5, 5, 4, 4, 4, 2, 2, 2],
  [6, 6, 6, 6, 4, 4, 4, 2, 2, 2, 2],
  [6, 5, 5, 5, 5, 4, 4, 2, 2, 2],
  [6, 6, 6, 5, 5, 4, 4, 2, 2, 2, 2],
  [6, 6, 6, 6, 6, 4, 4, 2, 2, 2, 2, 2],
  [5, 5, 5, 5, 5, 5, 4, 2, 2, 2],
  [6, 6, 5, 5, 5, 5, 4, 2, 2, 2, 2],
  [6, 6, 6, 6, 5, 5, 4, 2, 2, 2, 2, 2],
  [6, 6, 6, 6, 6, 6, 4, 2, 2, 2, 2, 2, 2],
  [6, 5, 5, 5, 5, 5, 5, 2, 2, 2, 2],
  [6, 6, 6, 5, 5, 5, 5, 2, 2, 2, 2, 2],
  [6, 6, 6, 6, 6, 5, 5, 2, 2, 2, 2, 2, 2],
  [6, 6, 6, 6, 6, 6, 6, 2, 2, 2, 2, 2, 2, 2] ]

private def edges : List (Bool × List (Fin 7 × Fin 7)) := [
  (false,[(0, 6)]),
  (false,[(2, 6)]),
  (true,[(0, 5), (1, 6)]),
  (true,[(1, 6), (4, 5)]),
  (true,[(4, 1), (0, 6), (4, 5)]),
  (true,[(3, 6), (4, 5)]),
  (true,[(3, 4), (3, 6), (4, 5)]),
  (true,[(5, 0), (4, 5), (1, 6), (4, 5)]),
  (true,[(4, 5), (3, 6), (4, 5)]),
  (true,[(2, 4), (3, 4), (2, 5), (3, 6)]),
  (true,[(6, 0), (3, 4), (6, 1), (3, 6), (4, 5)]),
  (true,[(5, 2), (3, 6), (4, 5)]),
  (true,[(3, 6), (4, 5), (3, 6), (4, 5)]),
  (true,[(5, 2), (3, 4), (5, 2), (3, 6), (4, 5)]),
  (true,[(5, 0), (6, 1), (3, 6), (4, 5), (3, 6), (4, 5)]),
  (true,[(3, 6), (5, 2), (3, 6), (4, 5)]),
  (true,[(5, 2), (3, 6), (4, 5), (3, 6), (4, 5)]),
  (true,[(5, 2), (6, 1), (3, 6), (4, 5), (3, 6), (4, 5)]),
  (true,[(5, 0), (6, 1), (2, 4), (3, 6), (5, 2), (3, 6), (4, 5)]) ]

private def base (s : Bool) : Graph 7 :=
  if s then Repair3.sevenGraph else LeafRepair3.oneThreeBase

private theorem small_valid (i : Fin 19) : Planaric smallProfiles[i] := by
  let b := edges[i].1
  let E := edges[i].2
  have pl : (base b).Planar := by
    cases b <;> first | exact LeafRepair3.oneThreeBase_planar | exact Repair3.sevenGraph_planar
  have ok : ∀ j : Fin 19, ∀ e ∈ edges[j].2, (base edges[j].1).adj e.1 e.2 = true := by decide +kernel
  have out := expanded_planaric pl E (ok i)
  have fits : ∀ j : Fin 19, (List.replicate edges[j].2.length 2 ++ List.ofFn (fun v =>
      (base edges[j].1).degree v + increments edges[j].2 v)).Perm smallProfiles[j] := by decide +kernel
  exact (planaric_perm (fits i)).mp out

private theorem small (a b c d e f g t : Nat)
    (ab : b≤a) (bc : c≤b) (cd : d≤c) (de : e≤d) (ef : f≤e) (fg : g≤f)
    (lo : 4≤g) (hi : a≤6) (someHigh : 5≤a) (sum : a+b+c+d+e+f+g=28+2*t) (mx : a≤6+t) :
    Planaric ([a,b,c,d,e,f,g] ++ List.replicate t 2) := by
  let val (x : Fin 3) := 4+x.val
  have exhaustive : ∀ (a b c d e f g : Fin 3), b≤a → c≤b → d≤c → e≤d → f≤e → g≤f →
      ∀ t : Fin 8, 5≤val a → val a+val b+val c+val d+val e+val f+val g=28+2*t.val →
      val a≤6+t.val → ([val a,val b,val c,val d,val e,val f,val g] ++ List.replicate t.val 2) ∈ smallProfiles := by
    decide +kernel
  let pack (x : Nat) (hlo : 4≤x) (hhi : x≤6) : Fin 3 := ⟨x-4,by omega⟩
  have ep (x) (lw : 4≤x) (up : x≤6) : val (pack x lw up)=x := by dsimp [val,pack]; omega
  have list := exhaustive (pack a (by omega) hi) (pack b (by omega) (by omega))
    (pack c (by omega) (by omega)) (pack d (by omega) (by omega)) (pack e (by omega) (by omega))
    (pack f (by omega) (by omega)) (pack g lo (by omega))
    (by change b-4≤a-4; omega) (by change c-4≤b-4; omega) (by change d-4≤c-4; omega)
    (by change e-4≤d-4; omega) (by change f-4≤e-4; omega) (by change g-4≤f-4; omega)
    ⟨t,by omega⟩
  simp only [ep] at list
  obtain ⟨j,hj,eql⟩ := List.getElem_of_mem (list someHigh sum mx)
  rw [←eql]
  exact small_valid ⟨j,hj⟩

private def twin := LeafRepair4.doubleFan

private theorem high_pair (a : Nat) (ha : 7≤a) :
    Planaric ([a,a,4,4,4,4,4] ++ List.replicate (a-4) 2) := by
  let E : List (Fin 7 × Fin 7) := List.replicate (a-7) (0,1) ++ [(0,3),(1,4),(5,6)]
  have ok : ∀ e∈E, twin.adj e.1 e.2 = true := by
    intro q h; simp only [E,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with ⟨_,rfl⟩|rfl|rfl|rfl <;> decide +kernel
  have pl := expanded_planaric LeafRepair4.doubleFan_planar E ok
  have len : E.length=a-4 := by simp [E]; omega
  have get (i : Fin 7) : increments E i = (if pairRow 0 1 i then a-7 else 0) +
      increments ([(0,3),(1,4),(5,6)]:List (Fin 7 × Fin 7)) i := by
    simp only [E,increments,List.countP_append,List.countP_replicate]
  have profile : List.ofFn (fun i => twin.degree i + increments E i)=[a,a,4,4,4,4,4] := by
    change [twin.degree 0+increments E 0,twin.degree 1+increments E 1,twin.degree 2+increments E 2,
      twin.degree 3+increments E 3,twin.degree 4+increments E 4,twin.degree 5+increments E 5,
      twin.degree 6+increments E 6]=_
    simp only [get]
    change [6+((a-7)+1),6+((a-7)+1),4,4,4,4,4]=_
    simp only [List.cons.injEq,and_true]; omega
  change Planaric (List.replicate E.length 2 ++ List.ofFn (fun i => twin.degree i+increments E i)) at pl
  rw [len,profile] at pl
  exact (planaric_perm List.perm_append_comm).mp pl

private theorem high_four (a : Nat) (ha : 7≤a) :
    Planaric ([a,a,a,a,4,4,4] ++ List.replicate (2*a-8) 2) := by
  let m := 2*a-10
  obtain ⟨P,hl,good,inc⟩ := SevenTwo.weights twin false (by decide +kernel)
    (a-7) (a-6) (a-4) (a-3) 0 m (by dsimp [m]; omega) (by simp [m]; omega)
  simp only [List.cons.injEq,and_true] at inc
  obtain ⟨p0,p1,p2,p3,p4,p5,p6⟩ := inc
  let Q : List (Fin 7 × Fin 7) := [(0,4),(5,6)]
  have ok : ∀ e∈P++Q, twin.adj e.1 e.2 = true := by
    intro e he; rcases List.mem_append.mp he with h|h
    · exact good e h
    · have hq : ∀ q∈Q, twin.adj q.1 q.2 = true := by decide +kernel
      exact hq e h
  have el : (P++Q).length=2*a-8 := by simp only [List.length_append,hl]; change m+2=2*a-8; dsimp [m]; omega
  have row (i : Fin 7) : increments (P++Q) i = increments P i + increments Q i := List.countP_append
  have prof : List.ofFn (fun i => twin.degree i + increments (P++Q) i)=[a,a,a,a,4,4,4] := by
    change [twin.degree 0+increments (P++Q) 0,twin.degree 1+increments (P++Q) 1,twin.degree 2+increments (P++Q) 2,
      twin.degree 3+increments (P++Q) 3,twin.degree 4+increments (P++Q) 4,twin.degree 5+increments (P++Q) 5,
      twin.degree 6+increments (P++Q) 6]=_
    simp only [row,p0,p1,p2,p3,p4,p5,p6]
    change [6+((a-7)+1),6+((a-6)+0),4+((a-4)+0),3+((a-3)+0),4,4,4]=_
    simp only [List.cons.injEq,and_true]; omega
  have out := expanded_planaric LeafRepair4.doubleFan_planar (P++Q) ok
  change Planaric (List.replicate (P++Q).length 2 ++ List.ofFn (fun i => twin.degree i+increments (P++Q) i)) at out
  rw [el,prof] at out
  exact (planaric_perm List.perm_append_comm).mp out

private theorem capacity (a b c d e f g t : Nat) (ab : b≤a) (bc : c≤b) (cd : d≤c) (de : e≤d) (ef : f≤e)
    (fg : g≤f) (lo : 4≤g) (hs : a+b+c+d+e+f+g=28+2*t) (mx : a≤6+t)
    (hi : 7≤a) (no1 : ¬ (a=b ∧ c=4)) (no2 : ¬ (a=d ∧ e=4)) :
    let A:=a-6; let B:=b-4; let C:=c-4; let D:=e-4; let E:=d-4; let F:=f-3; let G:=g-3
    let x:=min A G; let y:=G-x; let aa:=A-x; let dd:=D-y; let m:=t-G
    y≤D ∧ G≤t ∧ aa+B+C+dd+E+F=2*m ∧ F≤m ∧ F≤aa+B+C ∧ aa≤m ∧ B+dd≤m ∧ C+E≤m ∧ dd≤m-F ∧ E≤m-F := by
  simp only [Nat.min_def]
  split <;> (repeat' apply And.intro) <;> omega


/-- The seven-core upper-boundary classification at minimum degree at
    least four. The only omitted degree list is the unexpanded
    four-regular seven-vertex list. -/
theorem min_four (a b c d e f g t : Nat) (ab : b≤a) (bc : c≤b) (cd : d≤c) (de : e≤d)
    (ef : f≤e) (fg : g≤f) (lo : 4≤g) (sum : a+b+c+d+e+f+g=28+2*t)
    (mx : a≤6+t) (someHigh : 5≤a) :
    Planaric ([a,b,c,d,e,f,g] ++ List.replicate t 2) := by
  by_cases little : a≤6
  · exact small a b c d e f g t ab bc cd de ef fg lo little someHigh sum mx
  by_cases sameTwo : a=b ∧ c=4
  · obtain ⟨hx,hc⟩ := sameTwo
    subst b; subst c
    have s : d=4 ∧ e=4 ∧ f=4 ∧ g=4 ∧ t=a-4 := by omega
    obtain ⟨sd,se,sf,sg,st⟩ := s
    subst d e f g t
    exact high_pair a (by omega)
  by_cases sameFour : a=d ∧ e=4
  · obtain ⟨hx,he⟩ := sameFour
    subst d; subst e
    have s : b=a ∧ c=a ∧ f=4 ∧ g=4 ∧ t=2*a-8 := by omega
    obtain ⟨sb,sc,sf,sg,st⟩ := s
    subst b c f g t
    exact high_four a (by omega)
  let A:=a-6; let B:=b-4; let C:=c-4; let D:=e-4; let E:=d-4; let F:=f-3; let G:=g-3
  let x:=min A G; let y:=G-x; let aa:=A-x; let dd:=D-y; let m:=t-G
  obtain ⟨dy,gt,sz,fs,nb,ca,cb,cc,rd,re⟩ := capacity a b c d e f g t ab bc cd de ef fg
    lo sum mx (by omega) sameTwo sameFour
  obtain ⟨P,pl,pe,pinc⟩ := SevenOne.weights aa B C dd E F m sz fs nb ca cb cc rd re
  simp only [List.cons.injEq,and_true] at pinc
  obtain ⟨p0,p1,p2,p3,p4,p5,p6⟩ := pinc
  let H := SevenUniversal.Layer0.wheel
  let Q : List (Fin 7 × Fin 7) := List.replicate x (0,6) ++ List.replicate y (3,6)
  have qok e (he : e∈Q) : H.adj e.1 e.2 = true := by
    simp only [Q,List.mem_append,List.mem_replicate] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩ <;> decide +kernel
  have ok e (he : e∈P++Q) : H.adj e.1 e.2 = true := by
    rcases List.mem_append.mp he with he|he
    · exact pe e he
    · exact qok e he
  have qinc : [increments Q 0,increments Q 1,increments Q 2,increments Q 3,
      increments Q 4,increments Q 5,increments Q 6]=[x,0,0,y,0,0,x+y] := by
    simp only [Q,increments,List.countP_append,List.countP_replicate]
    change [x+0,0,0,0+y,0,0,x+y]=_; simp
  simp only [List.cons.injEq,and_true] at qinc
  obtain ⟨q0,q1,q2,q3,q4,q5,q6⟩ := qinc
  have row (i : Fin 7) : increments (P++Q) i = increments P i + increments Q i := List.countP_append
  have xg : x≤G := Nat.min_le_right _ _
  have xa : x≤A := Nat.min_le_left _ _
  have yd : y≤D := dy
  have tot : x+y=G := by dsimp [y]; omega
  have leng : (P++Q).length=t := by
    simp only [List.length_append,pl,Q,List.length_replicate]
    change m+(x+y)=t; dsimp [m]; omega
  have prof : List.ofFn (fun i => H.degree i+increments (P++Q) i)=[a,b,c,e,d,f,g] := by
    change [H.degree 0+increments (P++Q) 0,H.degree 1+increments (P++Q) 1,H.degree 2+increments (P++Q) 2,
      H.degree 3+increments (P++Q) 3,H.degree 4+increments (P++Q) 4,H.degree 5+increments (P++Q) 5,
      H.degree 6+increments (P++Q) 6]=_
    simp only [row,p0,p1,p2,p3,p4,p5,p6,q0,q1,q2,q3,q4,q5,q6,Nat.add_zero,Nat.zero_add,tot]
    have hh : H.degree 0=6 ∧ H.degree 1=4 ∧ H.degree 2=4 ∧ H.degree 3=4 ∧
        H.degree 4=4 ∧ H.degree 5=3 ∧ H.degree 6=3 := by decide +kernel
    obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := hh
    rw [h0,h1,h2,h3,h4,h5,h6]
    simp only [List.cons.injEq,and_true]
    dsimp only [aa,dd,A,B,C,D,E,F,G] at xa yd ⊢
    omega
  have out := expanded_planaric SevenUniversal.Layer0.wheel_planar (P++Q) ok
  rw [leng,prof] at out
  have out' := (planaric_perm List.perm_append_comm).mp out
  exact (planaric_perm (((List.Perm.swap d e [f,g]).cons c |>.cons b |>.cons a).append_right _)).mp out'

end SparseBoundary.SevenFour
