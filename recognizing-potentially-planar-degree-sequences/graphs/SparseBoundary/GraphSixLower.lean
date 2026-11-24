import SparseBoundary.GraphMultipartite
import SparseBoundary.GraphHub

namespace SparseBoundary

open Graph

private def sixChord : Graph 6 := ⟨20095⟩
private theorem sixChord_planar : sixChord.Planar := by
  apply Fan.two_apex_path_planar
  unfold Fan.TwoApexPath
  decide +kernel
private theorem six_labels (F : Fin 6 → Nat) :
    List.ofFn F=[F 0,F 1,F 2,F 3,F 4,F 5] := rfl

private theorem six_clique_increments (u v w x t : Nat) (len : u+v+w+x=t+t)
    (h0 : u≤t) (h1 : v≤t) (h3 : w≤t) (h2 : x≤t) :
    Planaric ([5+u,4+v,3+x,4+w,3,3] ++ List.replicate t 2) := by
  let T : List (Fin 6) := List.replicate u 0 ++ List.replicate v 1 ++ List.replicate w 3 ++ List.replicate x 2
  let C (i : Fin 6) := i.val
  let active : List (Fin 6) := [0,1,3,2]
  have supported (i : Fin 6) (hi : i∈T) : i∈active := by
    simp only [T,List.mem_append,List.mem_replicate] at hi
    simp only [active,List.mem_cons,List.mem_nil_iff,or_false]
    grind
  have cross : ∀ i ∈ active, ∀ j ∈ active, C i ≠ C j → sixChord.adj i j=true := by
    decide +kernel
  have cap (z) : (T.map C).count z≤t := by
    have c0 : C 0=0 := by decide
    have c1 : C 1=1 := by decide
    have c3 : C 3=3 := by decide
    have c2 : C 2=2 := by decide
    simp only [T,List.map_append,List.map_replicate,List.count_append,List.count_replicate,c0,c1,c3,c2,beq_iff_eq]
    by_cases z0 : 0=z
    · subst z; simp_all
    by_cases z1 : 1=z
    · subst z; simp_all
    by_cases z3 : 3=z
    · subst z; simp_all
    by_cases z2 : 2=z
    · subst z; simp_all
    simp [z0,z1,z3,z2]
  have pl := active_multipartite_planaric sixChord_planar C T t
    (fun i hi j hj => cross i (supported i hi) j (supported j hj))
    (by simpa [T,Nat.add_assoc] using len) cap
  have d0 : sixChord.degree 0=5 := by decide +kernel
  have d1 : sixChord.degree 1=4 := by decide +kernel
  have d2 : sixChord.degree 2=3 := by decide +kernel
  have d3 : sixChord.degree 3=4 := by decide +kernel
  have d4 : sixChord.degree 4=3 := by decide +kernel
  have d5 : sixChord.degree 5=3 := by decide +kernel
  rw [six_labels] at pl
  apply (planaric_perm List.perm_append_comm).mp
  simpa [T,List.count_replicate,d0,d1,d2,d3,d4,d5] using pl

private theorem six_parts_increments (u v w x y t : Nat) (len : u+v+w+x+y=t+t)
    (h0 : u≤t) (h1 : v+x≤t) (h2 : w+y≤t) :
    Planaric ([5+u,4+v,3,4+w,3+x,3+y] ++ List.replicate t 2) := by
  let T : List (Fin 6) := List.replicate u 0 ++ List.replicate v 1 ++ List.replicate w 3 ++ List.replicate x 4 ++ List.replicate y 5
  let C (i : Fin 6) := if i.val=0 then 0 else if i.val=1 ∨ i.val=4 then 1 else 2
  let active : List (Fin 6) := [0,1,3,4,5]
  have supported (i : Fin 6) (hi : i∈T) : i∈active := by
    simp only [T,List.mem_append,List.mem_replicate] at hi
    simp only [active,List.mem_cons,List.mem_nil_iff,or_false]
    grind
  have cross : ∀ i ∈ active, ∀ j ∈ active, C i ≠ C j → sixChord.adj i j=true := by
    decide +kernel
  have cap (z) : (T.map C).count z≤t := by
    have c0 : C 0=0 := by decide
    have c1 : C 1=1 := by decide
    have c3 : C 3=2 := by decide
    have c4 : C 4=1 := by decide
    have c5 : C 5=2 := by decide
    simp only [T,List.map_append,List.map_replicate,List.count_append,List.count_replicate,c0,c1,c3,c4,c5,beq_iff_eq]
    by_cases z0 : 0=z
    · subst z; simp_all
    by_cases z1 : 1=z
    · subst z; simp_all
    by_cases z2 : 2=z
    · subst z; simp_all
    simp [z0,z1,z2]
  have pl := active_multipartite_planaric sixChord_planar C T t
    (fun i hi j hj => cross i (supported i hi) j (supported j hj))
    (by simpa [T,Nat.add_assoc] using len) cap
  have d0 : sixChord.degree 0=5 := by decide +kernel
  have d1 : sixChord.degree 1=4 := by decide +kernel
  have d2 : sixChord.degree 2=3 := by decide +kernel
  have d3 : sixChord.degree 3=4 := by decide +kernel
  have d4 : sixChord.degree 4=3 := by decide +kernel
  have d5 : sixChord.degree 5=3 := by decide +kernel
  rw [six_labels] at pl
  apply (planaric_perm List.perm_append_comm).mp
  simpa [T,List.count_replicate,d0,d1,d2,d3,d4,d5] using pl

/-- Exactly one three in a six-vertex core on the lower boundary. -/
theorem lower_six_one_three (a b c d e t : Nat) (hab : b≤a) (hbc : c≤b)
    (hcd : d≤c) (hde : e≤d) (he : 4≤e) (sum : a+b+c+d+e+3=22+2*t) (upper : a≤t+5) :
    Planaric ([a,b,c,d,e,3] ++ List.replicate t 2) := by
  have ha : 5≤a := by
    apply Classical.byContradiction; intro hn
    rw [show a=4 by omega,show b=4 by omega,show c=4 by omega,show d=4 by omega,show e=4 by omega] at sum
    omega
  have h := six_parts_increments (a-5) (b-4) (c-4) (e-3) (d-3) t
    (by omega) (by omega) (by omega) (by omega)
  rw [show 5+(a-5)=a by omega,show 4+(b-4)=b by omega,show 4+(c-4)=c by omega,
      show 3+(d-3)=d by omega,show 3+(e-3)=e by omega] at h
  have p : [a,b,3,c,e,d].Perm [a,b,c,d,e,3] := by
    apply List.perm_iff_count.mpr
    intro v; simp only [List.count_cons,List.count_nil]; omega
  exact (planaric_perm (p.append_right _)).mp h

private theorem three_three_base : Planaric [4,4,4,4,3,3] := by
  let G : Graph 6 := ⟨20222⟩
  apply (planaric_perm (d:=[4,4,3,4,4,3]) (by decide +kernel)).mp
  refine ⟨G,?_,Fan.two_apex_path_planar ?_⟩
  · show ∀ i : Fin 6, G.degree i = ([4,4,3,4,4,3] : List Nat)[i]
    decide +kernel
  · unfold Fan.TwoApexPath; decide +kernel

/-- Two or three threes in a six-vertex core on the lower boundary. -/
theorem lower_six_two_or_three_threes (a b c d t : Nat) (hab : b≤a) (hbc : c≤b)
    (hcd : d≤c) (hc : 4≤c) (hd : 3≤d) (sum : a+b+c+d+6=22+2*t) (upper : a≤t+5) :
    Planaric ([a,b,c,d,3,3] ++ List.replicate t 2) := by
  by_cases big : 5≤a
  · have h := six_clique_increments (a-5) (b-4) (c-4) (d-3) t
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show 5+(a-5)=a by omega,show 4+(b-4)=b by omega,show 4+(c-4)=c by omega,
        show 3+(d-3)=d by omega] at h
    exact (planaric_perm (((List.Perm.swap c d [3,3]).cons b |>.cons a).append_right _)).mp h
  · have ha : a=4 := by omega
    have hb : b=4 := by omega
    have hc' : c=4 := by omega
    have hd' : d=4 := by omega
    have ht : t=0 := by omega
    simpa [ha,hb,hc',hd',ht] using three_three_base

private theorem four_three_base : Planaric [5,5,3,3,3,3] := by
  let G : Graph 6 := ⟨19711⟩
  refine ⟨G,?_,Fan.two_apex_path_planar ?_⟩
  · show ∀ i : Fin 6, G.degree i = ([5,5,3,3,3,3] : List Nat)[i]
    decide +kernel
  · unfold Fan.TwoApexPath; decide +kernel

/-- Four or more threes in a six-vertex core on the lower boundary. -/
theorem lower_six_four_threes (a b t : Nat) (hab : b≤a) (sum : a+b+12=22+2*t)
    (upper : a≤t+5) : Planaric ([a,b,3,3,3,3] ++ List.replicate t 2) := by
  have ha : a=t+5 := by omega
  have hb : b=t+5 := by omega
  have h := six_hub_extensions 5 3 3 3 3 t 0 0 0 0 0 four_three_base
  simpa [ha,hb,Nat.add_comm] using h

end SparseBoundary
