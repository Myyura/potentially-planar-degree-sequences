import SparseBoundary.FanUniversal
import SparseBoundary.GraphWeighted
import SparseBoundary.GraphSixClassification
import SparseBoundary.GraphPairInsertion

namespace SparseBoundary.Fan.Eight

open Graph

private def shell : Fin 5 → Graph 8
  | 0 => ⟨140627199⟩
  | 1 => ⟨24219119⟩
  | 2 => ⟨28413423⟩
  | 3 => ⟨140630399⟩
  | _ => ⟨45885343⟩

private def ranks : Fin 5 → List Nat
  | 0 => [0,5,1,2,3,4,6,7]
  | 1 => [0,6,2,1,3,4,5,7]
  | 2 => [0,5,6,1,2,3,4,7]
  | 3 => [0,5,2,1,3,4,6,7]
  | _ => [0,1,7,2,5,3,4,6]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
private theorem shell_planar (k : Fin 5) : (shell k).Planar := by
  apply outer_order_planar (v:=0)
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by simp only [Fin.ext_iff]; omega
  refine ⟨fun i => (ranks k)[i.val]!,?_,?_⟩ <;>
    rcases hk with rfl|rfl|rfl|rfl|rfl <;> decide +kernel

private theorem repair : Planaric (2::[5,5,5,5,5,3,3,3]) := by
  let E : List (Fin 8 × Fin 8) := [(1,2)]
  have hp := expanded_planaric (shell_planar 4) E (by decide +kernel)
  have eqn : List.ofFn (fun i => (shell 4).degree i+increments E i)=[5,5,5,5,5,3,3,3] :=
    by decide +kernel
  exact eqn ▸ hp

private def BaseFits (a b c t x y z : Nat) : Prop :=
  x≤a ∧ y≤b ∧ z≤c ∧ a≤x+t ∧ b≤y+t ∧ c≤z+t

private theorem triangle (a b c t x y z : Nat) (k : Fin 5)
    (base : List.ofFn (shell k).degree=[x,y,z,3,3,3,3,3])
    (edge : (shell k).adj 0 1=true ∧ (shell k).adj 0 2=true ∧ (shell k).adj 1 2=true)
    (total : a+b+c=17+2*t) (budget : x+y+z=17) (fit : BaseFits a b c t x y z) :
    Planaric (List.replicate t 2 ++ [a,b,c,3,3,3,3,3]) := by
  obtain ⟨hx,hy,hz,ax,by',cz⟩ := fit
  let u := t-(c-z)
  let v := t-(b-y)
  let w := t-(a-x)
  have uv : x+u+v=a := by dsimp [u,v]; omega
  have uw : y+u+w=b := by dsimp [u,w]; omega
  have vw : z+v+w=c := by dsimp [v,w]; omega
  have count : u+v+w=t := by dsimp [u,v,w]; omega
  let E : List (Fin 8 × Fin 8) := List.replicate u (0,1) ++ List.replicate v (0,2) ++ List.replicate w (1,2)
  have good e (mem : e∈E) : (shell k).adj e.1 e.2=true := by
    simp only [E,List.mem_append,List.mem_replicate] at mem
    rcases mem with ((⟨_,rfl⟩|⟨_,rfl⟩)|⟨_,rfl⟩)
    · exact edge.1
    · exact edge.2.1
    · exact edge.2.2
  have hp := expanded_planaric (shell_planar k) E good
  have labels (f : Fin 8 → Nat) : List.ofFn f=[f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7] := rfl
  rw [labels] at hp base
  simp only [List.cons.injEq,and_true] at base
  obtain ⟨d0,d1,d2,d3,d4,d5,d6,d7⟩ := base
  have weight (i : Fin 8) : increments E i=
      (if pairRow 0 1 i then u else 0)+(if pairRow 0 2 i then v else 0)+
      (if pairRow 1 2 i then w else 0) := by simp [increments,E,List.countP_replicate,Nat.add_assoc]
  rw [show E.length=t by simpa [E,Nat.add_assoc] using count] at hp
  simp only [d0,d1,d2,d3,d4,d5,d6,d7,weight] at hp
  change Planaric (List.replicate t 2 ++ [x+(u+v+0),y+(u+0+w),z+(0+v+w),3+0,3+0,3+0,3+0,3+0]) at hp
  simpa [← Nat.add_assoc,uv,uw,vw] using hp

/-- Five threes on eight core vertices. Four constant plane supports have
a triangle on the three distinguished vertices. -/
theorem five_threes (a b c t : Nat) (ab : b≤a) (bc : c≤b) (hc : 4≤c)
    (vol : a+b+c=17+2*t) (cap : a≤t+6) :
    Planaric (List.replicate t 2 ++ [a,b,c,3,3,3,3,3]) := by
  have alloc : BaseFits a b c t 7 7 3 ∨ BaseFits a b c t 7 6 4 ∨
      BaseFits a b c t 7 5 5 ∨ BaseFits a b c t 6 6 5 := by unfold BaseFits; omega
  rcases alloc with h|h|h|h
  · exact triangle a b c t 7 7 3 0 (by decide +kernel) (by decide +kernel) vol (by decide) h
  · exact triangle a b c t 7 6 4 1 (by decide +kernel) (by decide +kernel) vol (by decide) h
  · exact triangle a b c t 7 5 5 2 (by decide +kernel) (by decide +kernel) vol (by decide) h
  · exact triangle a b c t 6 6 5 3 (by decide +kernel) (by decide +kernel) vol (by decide) h

/-- Two or more threes on eight core vertices with positive two-budget,
including all residual six-core exceptions. -/
theorem two_threes (a b c d e f t : Nat) (ab : b≤a) (bc : c≤b) (cd : d≤c) (de : e≤d)
    (ef : f≤e) (hf : 3≤f) (pos : 1≤t) (vol : a+b+c+d+e+f+6=32+2*t) (cap : a≤t+7) :
    Planaric (List.replicate t 2 ++ [a,b,c,d,e,f,3,3]) := by
  by_cases univ : a=t+7
  · apply Universal.boundary (j:=0) [b,c,d,e,f,3,3] (by simp) (by simp; omega)
      (by simp; omega) (by decide) (by simp; omega) (by simp; omega)
  by_cases md : d≤3
  · have h : d=3 ∧ e=3 ∧ f=3 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact five_threes a b c t ab bc (by omega) (by omega) (by omega)
  by_cases special : a=5 ∧ e=5 ∧ f=3
  · obtain ⟨rfl,rfl,rfl⟩ := special
    have h : b=5 ∧ c=5 ∧ d=5 ∧ t=1 := by omega
    obtain ⟨rfl,rfl,rfl,rfl⟩ := h
    exact repair
  have old : Planaric ([a,b,c,d,e,f] ++ List.replicate (t+1) 2) := by
    by_cases f4 : 4≤f
    · apply six_min_four a b c d e f (t+1) (t+1) ab bc cd de ef f4 <;> omega
    have f3 : f=3 := by omega
    subst f
    by_cases e4 : 4≤e
    · exact upper_six_one_three a b c d e (t+1) ab bc cd de e4 (by omega) (by omega) (by omega) (by omega)
    have e3 : e=3 := by omega
    subst e
    exact upper_six_two_threes a b c d (t+1) ab bc cd (by omega) (by omega) (by omega)
  have hp := restore_equal_pair (s:=t+1) (g:=3) (by omega) (by decide)
    ((planaric_perm List.perm_append_comm).mp old)
  rw [show t+1+3-4=t by omega] at hp
  have ps : (3::3::[a,b,c,d,e,f]).Perm [a,b,c,d,e,f,3,3] := List.perm_append_comm (l₁:=[3,3])
  exact (planaric_perm (ps.append_left _)).mp hp

end SparseBoundary.Fan.Eight
