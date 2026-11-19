import SparseBoundary.GraphMultipartite
import SparseBoundary.GraphPerm
import SparseBoundary.MinorBits

namespace SparseBoundary.Graph
open MinorSearch

set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Bipyramid

private def support : Graph 5 := ⟨511⟩
private def color (i : Fin 5) := min i.val 3
private def initial : Nat := 0xfefffffe
private def cat : Array (Option Nat) := ((List.range 32).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 5).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh support v) 0)
  else none).toArray
private def table := makeTable 5 cat initial

private theorem support_planar : support.Planar := by
  have cov : covers support cat = true := by decide +kernel
  have tab : validTable cat initial table = true := by decide +kernel
  constructor
  · apply forbidden_of_table support clique5 cat initial table [0,1,2,3,4] (by decide) cov tab
    decide +kernel
  · apply forbidden_of_table support biclique33 cat initial table [0,3,1,4,2,5] (by decide) cov tab
    decide +kernel

private theorem labels (f : Fin 5 → Nat) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4] := rfl

/-- All balanced degree increments on the bipyramid give a planar simple
    realization with one degree-two vertex for each extra edge. -/
theorem realize (a b c d e m : Nat) (length : a+b+c+d+e=m+m)
    (h0 : a ≤ m) (h1 : b ≤ m) (h2 : c ≤ m) (h3 : d + e ≤ m) :
    Planaric ([4+a, 4+b, 4+c, 3+d, 3+e] ++ List.replicate m 2) := by
  let T : List (Fin 5) := List.replicate a 0 ++ List.replicate b 1 ++ List.replicate c 2 ++ List.replicate d 3 ++ List.replicate e 4
  have cap (z) : (T.map color).count z ≤ m := by
    have c0 : color 0 = 0 := by decide
    have c1 : color 1 = 1 := by decide
    have c2 : color 2 = 2 := by decide
    have c3 : color 3 = 3 := by decide
    have c4 : color 4 = 3 := by decide
    simp only [T,List.map_append,List.map_replicate,List.count_append,List.count_replicate,c0,c1,c2,c3,c4]
    simp only [beq_iff_eq]
    by_cases z0 : 0=z
    · subst z; simp_all
    by_cases z1 : 1=z
    · subst z; simp_all
    by_cases z2 : 2=z
    · subst z; simp_all
    by_cases z3 : 3=z
    · subst z; simp_all
    simp [z0,z1,z2,z3]
  have pl := multipartite_planaric support_planar color (by decide +kernel) T m (by simpa [T,Nat.add_assoc] using length) cap
  have d0 : support.degree 0=4 := by decide +kernel
  have d1 : support.degree 1=4 := by decide +kernel
  have d2 : support.degree 2=4 := by decide +kernel
  have d3 : support.degree 3=3 := by decide +kernel
  have d4 : support.degree 4=3 := by decide +kernel
  rw [labels] at pl
  apply (planaric_perm List.perm_append_comm).mp
  simpa [d0,d1,d2,d3,d4,T,List.count_replicate] using pl

end Bipyramid

namespace Octahedron

private def support : Graph 6 := ⟨31583⟩
private def color (i : Fin 6) := min i.val (5-i.val)
private def initial : Nat := 0xfffffffdfffbeffe
private def cat : Array (Option Nat) := ((List.range 64).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 6).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh support v) 0)
  else none).toArray
private def table := makeTable 6 cat initial

private theorem support_planar : support.Planar := by
  have cov : covers support cat = true := by decide +kernel
  have tab : validTable cat initial table = true := by decide +kernel
  constructor
  · apply forbidden_of_table support clique5 cat initial table [0,1,2,3,4] (by decide) cov tab
    decide +kernel
  · apply forbidden_of_table support biclique33 cat initial table [0,3,1,4,2,5] (by decide) cov tab
    decide +kernel

private theorem labels (f : Fin 6 → Nat) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5] := rfl

/-- All balanced degree increments on the octahedron give a planar simple
    realization with one degree-two vertex for each extra edge. -/
theorem realize (a b c d e f m : Nat) (length : a+b+c+d+e+f=m+m)
    (h0 : a + f ≤ m) (h1 : b + e ≤ m) (h2 : c + d ≤ m) :
    Planaric ([4+a, 4+b, 4+c, 4+d, 4+e, 4+f] ++ List.replicate m 2) := by
  let T : List (Fin 6) := List.replicate a 0 ++ List.replicate b 1 ++ List.replicate c 2 ++ List.replicate d 3 ++ List.replicate e 4 ++ List.replicate f 5
  have cap (z) : (T.map color).count z ≤ m := by
    have c0 : color 0 = 0 := by decide
    have c1 : color 1 = 1 := by decide
    have c2 : color 2 = 2 := by decide
    have c3 : color 3 = 2 := by decide
    have c4 : color 4 = 1 := by decide
    have c5 : color 5 = 0 := by decide
    simp only [T,List.map_append,List.map_replicate,List.count_append,List.count_replicate,c0,c1,c2,c3,c4,c5]
    simp only [beq_iff_eq]
    by_cases z0 : 0=z
    · subst z; simp_all
    by_cases z1 : 1=z
    · subst z; simp_all
    by_cases z2 : 2=z
    · subst z; simp_all
    simp [z0,z1,z2]
  have pl := multipartite_planaric support_planar color (by decide +kernel) T m (by simpa [T,Nat.add_assoc] using length) cap
  have d0 : support.degree 0=4 := by decide +kernel
  have d1 : support.degree 1=4 := by decide +kernel
  have d2 : support.degree 2=4 := by decide +kernel
  have d3 : support.degree 3=4 := by decide +kernel
  have d4 : support.degree 4=4 := by decide +kernel
  have d5 : support.degree 5=4 := by decide +kernel
  rw [labels] at pl
  apply (planaric_perm List.perm_append_comm).mp
  simpa [d0,d1,d2,d3,d4,d5,T,List.count_replicate] using pl

end Octahedron

end SparseBoundary.Graph
