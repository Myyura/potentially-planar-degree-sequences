import SparseBoundary.MinorGroups
import SparseBoundary.GraphMultipartite
import SparseBoundary.LeafRepairs

namespace SparseBoundary.SevenThree
open Graph MinorSearch

namespace Base0

private def realization : Graph 7 := ⟨1347071⟩
private def initial : Nat := 0xfeeeffeffeaaffabeeeeeeeffefffffe
private def catalog : Array (Option Nat) := ((List.range 128).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 7).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 7 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

private theorem planar : realization.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

theorem base : Planaric [6, 5, 4, 4, 3, 3, 3] :=
  ⟨realization,by unfold Realizes; decide +kernel,planar⟩

theorem lift0 : Planaric [7, 5, 5, 4, 3, 3, 3, 2] := by
  let E : List (Fin 7 × Fin 7) := [(0,2)]
  have hp := expanded_planaric planar E (by decide +kernel)
  exact (planaric_perm (d:=List.replicate E.length 2 ++
    List.ofFn (fun i => realization.degree i + increments E i)) (by decide +kernel)).mp hp

theorem lift1 : Planaric [6, 5, 5, 5, 3, 3, 3, 2] := by
  let E : List (Fin 7 × Fin 7) := [(2,3)]
  have hp := expanded_planaric planar E (by decide +kernel)
  exact (planaric_perm (d:=List.replicate E.length 2 ++
    List.ofFn (fun i => realization.degree i + increments E i)) (by decide +kernel)).mp hp

theorem lift2 : Planaric [8, 5, 5, 5, 3, 3, 3, 2, 2] := by
  let E : List (Fin 7 × Fin 7) := [(0,2),(0,3)]
  have hp := expanded_planaric planar E (by decide +kernel)
  exact (planaric_perm (d:=List.replicate E.length 2 ++
    List.ofFn (fun i => realization.degree i + increments E i)) (by decide +kernel)).mp hp

end Base0

namespace Base1

private def realization : Graph 7 := ⟨1251071⟩
private def initial : Nat := 0xfeeefefffcecfcfdfaeafafbffeffffe
private def catalog : Array (Option Nat) := ((List.range 128).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 7).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 7 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

private theorem planar : realization.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

theorem base : Planaric [5, 5, 5, 4, 3, 3, 3] :=
  ⟨realization,by unfold Realizes; decide +kernel,planar⟩

end Base1


set_option maxHeartbeats 3000000

private theorem clique_lift (a b c d t : Nat) (ha : 6≤a) (hb : 6≤b) (hc : 4≤c) (hd : 3≤d)
    (amax : a-6≤t) (bmax : b-6≤t) (cmax : c-4≤t) (dmax : d-3≤t)
    (sum : a+b+c+d=19+2*t) :
    Planaric ([a,b,c,d,3,3,3] ++ List.replicate t 2) := by
  let T : List (Fin 7) := List.replicate (a-6) 0 ++ List.replicate (b-6) 1 ++
    List.replicate (c-4) 2 ++ List.replicate (d-3) 3
  let color := fun i : Fin 7 => i.val
  have active (i) (hi : i ∈ T) : i.val ≤ 3 := by
    simp only [T,List.mem_append,List.mem_replicate] at hi
    rcases hi with (((⟨_,rfl⟩|⟨_,rfl⟩)|⟨_,rfl⟩)|⟨_,rfl⟩) <;> decide
  have clique : ∀ i j : Fin 7, i.val ≤ 3 → j.val ≤ 3 → i.val ≠ j.val →
      LeafRepair4.doubleFan.adj i j = true := by decide +kernel
  have cap (x : Nat) : (T.map color).count x ≤ t := by
    simp only [T,List.map_append,List.map_replicate,List.count_append,List.count_replicate]
    change ((if (0:Nat)==x then a-6 else 0)+(if (1:Nat)==x then b-6 else 0)+
      (if (2:Nat)==x then c-4 else 0)+(if (3:Nat)==x then d-3 else 0))≤t
    simp only [beq_iff_eq]; split <;> split <;> split <;> split <;> omega
  have pl := active_multipartite_planaric LeafRepair4.doubleFan_planar color T t
    (fun i hi j hj => clique i j (active i hi) (active j hj))
    (by simp only [T,List.length_append,List.length_replicate]; omega) cap
  apply (planaric_perm List.perm_append_comm).mp
  have profile : List.ofFn (fun i => LeafRepair4.doubleFan.degree i + T.count i)=[a,b,c,d,3,3,3] := by
    change [LeafRepair4.doubleFan.degree 0 + T.count 0,LeafRepair4.doubleFan.degree 1 + T.count 1,
      LeafRepair4.doubleFan.degree 2 + T.count 2,LeafRepair4.doubleFan.degree 3 + T.count 3,
      LeafRepair4.doubleFan.degree 4 + T.count 4,LeafRepair4.doubleFan.degree 5 + T.count 5,
      LeafRepair4.doubleFan.degree 6 + T.count 6]=_
    simp only [T,List.count_append,List.count_replicate]
    change [6+(a-6+0+0+0),6+(0+(b-6)+0+0),4+(0+0+(c-4)+0),3+(0+0+0+(d-3)),3,3,3]=_
    simp only [List.cons.injEq,and_true]; omega
  rwa [profile] at pl

/-- Full upper-boundary positive case for seven core vertices of which
    exactly three have degree three. -/
theorem three_threes (a b c d t : Nat) (ha : b≤a) (hb : c≤b) (hc : d≤c) (hd : 4≤d)
    (sum : a+b+c+d=19+2*t) (maximum : a≤6+t) :
    Planaric ([a,b,c,d,3,3,3] ++ List.replicate t 2) := by
  by_cases high : 6≤b
  · apply clique_lift <;> omega
  have hb5 : b=5 := by omega
  subst b
  have cases :
      (a=6 ∧ c=4 ∧ d=4 ∧ t=0) ∨ (a=5 ∧ c=5 ∧ d=4 ∧ t=0) ∨
      (a=7 ∧ c=5 ∧ d=4 ∧ t=1) ∨ (a=6 ∧ c=5 ∧ d=5 ∧ t=1) ∨
      (a=8 ∧ c=5 ∧ d=5 ∧ t=2) := by
    by_cases h0 : t=0 <;> by_cases h1 : t=1 <;> by_cases h2 : c=4 <;> by_cases h3 : d=4 <;> omega
  rcases cases with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩
  · exact Base0.base
  · exact Base1.base
  · exact Base0.lift0
  · exact Base0.lift1
  · exact Base0.lift2

end SparseBoundary.SevenThree
