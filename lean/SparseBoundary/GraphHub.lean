import SparseBoundary.GraphWeighted
import SparseBoundary.GraphPetals
import SparseBoundary.GraphSixCore
import SparseBoundary.FanPlanar

namespace SparseBoundary
open Graph

/-- Increase entries of an arbitrary realizable six-vertex cone while
    increasing its pole with spokes and disjoint triangles at that pole. -/
theorem six_hub_extensions (b c d e f u v w x y k : Nat)
    (base : Planaric [5,b,c,d,e,f]) :
    Planaric ([5+(u+v+w+x+y)+2*k,b+u,c+v,d+w,e+x,f+y] ++
      List.replicate (u+v+w+x+y+2*k) 2) := by
  obtain ⟨G,real,hp⟩ := base
  let E : List (Fin 6 × Fin 6) := List.replicate u (0,1) ++ List.replicate v (0,2) ++
    List.replicate w (0,3) ++ List.replicate x (0,4) ++ List.replicate y (0,5)
  have sat : G.degree 0=5 := real 0
  have valid (ij) (h : ij∈E) : G.adj ij.1 ij.2=true := by
    simp only [E,List.mem_append,List.mem_replicate] at h
    rcases h with (((⟨_,rfl⟩|⟨_,rfl⟩)|⟨_,rfl⟩)|⟨_,rfl⟩)|⟨_,rfl⟩ <;>
      first | exact root_universal sat 0 | exact root_universal sat 1 | exact root_universal sat 2 | exact root_universal sat 3 | exact root_universal sat 4
  have pl := expanded_planaric hp E valid
  have labels (F : Fin 6 → Nat) : List.ofFn F=[F 0,F 1,F 2,F 3,F 4,F 5] := rfl
  have d0 : G.degree 0=5 := real 0
  have d1 : G.degree 1=b := real 1
  have d2 : G.degree 2=c := real 2
  have d3 : G.degree 3=d := real 3
  have d4 : G.degree 4=e := real 4
  have d5 : G.degree 5=f := real 5
  rw [labels,d0,d1,d2,d3,d4,d5] at pl
  let s := u+v+w+x+y
  have stage : Planaric (List.replicate s 2 ++ [5+s,b+u,c+v,d+w,e+x,f+y]) := by
    simpa [s,E,increments,List.countP_append,List.countP_replicate,pairRow,Nat.add_assoc] using pl
  have stage' := (planaric_perm List.perm_append_comm).mp stage
  have p := planaric_petals stage' k
  let tail := [b+u,c+v,d+w,e+x,f+y]
  have swap : (List.replicate (2*k) 2 ++ (tail ++ List.replicate s 2)).Perm
      (tail ++ List.replicate (s+2*k) 2) := by
    have eqn : List.replicate (s+2*k) 2=List.replicate s 2 ++ List.replicate (2*k) 2 := by
      symm; apply List.eq_replicate_iff.mpr; exact ⟨by simp, by simp⟩
    rw [eqn]
    have p : (List.replicate (2*k) 2 ++ (tail ++ List.replicate s 2)).Perm
        ((tail ++ List.replicate s 2) ++ List.replicate (2*k) 2) := List.perm_append_comm
    simpa only [List.append_assoc] using p
  exact (planaric_perm (swap.cons _)).mp p

/-- A pentagon with a chord, coned over a new vertex. -/
private theorem six_chord_base : Planaric [5,4,4,3,3,3] := by
  let G : Graph 6 := ⟨20095⟩
  apply (planaric_perm (d:=[5, 4, 3, 4, 3, 3]) (by decide +kernel)).mp
  refine ⟨G,?_,Fan.two_apex_path_planar ?_⟩
  · show ∀ i : Fin 6, G.degree i = ([5, 4, 3, 4, 3, 3] : List Nat)[i]
    decide +kernel
  · unfold Fan.TwoApexPath
    decide +kernel

private theorem six_pentagon_base : Planaric [5,5,4,4,3,3] := by
  let B : Graph 6 := ⟨20223⟩
  have h : Planaric [5,5,3,4,4,3] := by
    refine ⟨B,?_,Fan.two_apex_path_planar ?_⟩
    · show ∀ i : Fin 6, B.degree i = ([5,5,3,4,4,3] : List Nat)[i]
      decide +kernel
    · unfold Fan.TwoApexPath; decide +kernel
  exact (planaric_perm (by decide +kernel)).mp h

private theorem spend {core : List Nat} {t m : Nat} (hm : m≤t)
    (pos : ∃ v∈core, 0<v) (h : Planaric (core ++ List.replicate m 2)) :
    Planaric (core ++ List.replicate t 2) := by
  have p := (planaric_perm List.perm_append_comm).mp h
  obtain ⟨x,hx,hv⟩ := pos
  have q := planaric_add_twos p ⟨x,List.mem_append_right _ hx,hv⟩ (t-m)
  have eqn : List.replicate (t-m) 2 ++ List.replicate m 2=List.replicate t 2 := by
    apply List.eq_replicate_iff.mpr; exact ⟨by simp; omega,by simp⟩
  rw [← List.append_assoc,eqn] at q
  exact (planaric_perm List.perm_append_comm).mp q

/-- The high-pole part of the six-core lemma for b ≥ 5. -/
theorem six_high_hub (a b c d e f m t : Nat)
    (hab : b≤a) (hb : 5≤b) (hc : 4≤c) (hd : 4≤d) (he : 3≤e) (hf : 3≤f)
    (sum : a+b+c+d+e+f=24+2*m) (large : m+5≤a) (budget : a≤t+5) :
    Planaric ([a,b,c,d,e,f] ++ List.replicate t 2) := by
  let s := (b-5)+(c-4)+(d-4)+(e-3)+(f-3)
  let k := a-m-5
  have eq₁ : 5+s+2*k=a := by dsimp [s,k]; omega
  have pl := six_hub_extensions 5 4 4 3 3 (b-5) (c-4) (d-4) (e-3) (f-3) k six_pentagon_base
  change Planaric ([5+s+2*k,_,_,_,_,_] ++ List.replicate (s+2*k) 2) at pl
  rw [eq₁,show 5+(b-5)=b by omega,show 4+(c-4)=c by omega,show 4+(d-4)=d by omega,
    show 3+(e-3)=e by omega,show 3+(f-3)=f by omega] at pl
  exact spend (by omega) ⟨a,by simp,by omega⟩ pl

/-- For five equal targets four, every even pole of degree at least eight
    is realized at its minimum possible degree-two budget. -/
theorem six_four_rim (a t : Nat) (large : 8≤a) (even : a%2=0) (budget : a≤t+5) :
    Planaric ([a,4,4,4,4,4] ++ List.replicate t 2) := by
  let k := (a-8)/2
  have eqn : 8+2*k=a := by dsimp [k]; omega
  have pl := six_hub_extensions 4 4 3 3 3 0 0 1 1 1 k six_chord_base
  change Planaric ([8+2*k,4,4,4,4,4] ++ List.replicate (3+2*k) 2) at pl
  rw [eqn] at pl
  exact spend (by omega) ⟨a,by simp,by omega⟩ pl

/-- The exceptional minimum budget two for the profile (6,4,4,4,4,4). -/
theorem six_exception_budget (t : Nat) (budget : 2≤t) :
    Planaric ([6,4,4,4,4,4] ++ List.replicate t 2) := by
  have h : Planaric [4,4,4,4,4,4] := by
    exact Graph.Octahedron.realize 0 0 0 0 0 0 0 (by decide) (by decide) (by decide) (by decide)
  have p := planaric_petal h
  have q : Planaric ([6,4,4,4,4,4] ++ List.replicate 2 2) :=
    (planaric_perm (by decide +kernel)).mp p
  exact spend budget ⟨6,by simp,by decide⟩ q

end SparseBoundary
