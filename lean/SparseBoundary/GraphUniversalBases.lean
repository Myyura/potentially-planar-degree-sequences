import SparseBoundary.GraphCone
import SparseBoundary.GraphEnumeration

namespace SparseBoundary.Graph

private def rowBags {n k : Nat} (xs : List (List (Fin n))) (i : Fin k) : List (Fin n) :=
  xs[i.val]?.getD []

private def detects {n : Nat} (G : Graph n) (K B : List (List (List (Fin n)))) : Bool :=
  K.any (fun r => G.minorTest clique5 (rowBags r)) ||
  B.any (fun r => G.minorTest biclique33 (rowBags r))

private theorem excluded {n : Nat} (G : Graph n) (K B : List (List (List (Fin n))))
    (h : detects G K B) : ¬ G.Planar := by
  intro hp
  change (_ || _) = true at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨r,_,hr⟩ := List.any_eq_true.mp h
    exact hp.1 ⟨rowBags r,hr⟩
  · obtain ⟨r,_,hr⟩ := List.any_eq_true.mp h
    exact hp.2 ⟨rowBags r,hr⟩

private def E1K : List (List (List (Fin 6))) := [

]

private def E1B : List (List (List (Fin 6))) := [
  [[0], [1], [2], [3], [4], [5]],
  [[0], [1], [3], [2], [4], [5]],
  [[0], [1], [4], [2], [3], [5]],
  [[0], [2], [3], [1], [4], [5]],
  [[0], [2], [4], [1], [3], [5]],
  [[0], [3], [4], [1], [2], [5]]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem E1_check :
    (candidates 5 (fun i => ([4, 4, 4, 4, 3] : List Nat)[i.val]'i.isLt - 1)).all
      (fun H => detects H.cone E1K E1B) := by
  decide +kernel

theorem E1_nonplanar : ¬ Planaric [5, 4, 4, 4, 4, 3] := by
  intro h
  obtain ⟨G,hp,hd⟩ := planaric_universal (n := 5) [4, 4, 4, 4, 3] rfl h
  apply excluded G.cone E1K E1B _ hp
  apply List.all_eq_true.mp E1_check G
  apply candidates_complete
  intro v
  have he := hd v
  omega

private def E3K : List (List (List (Fin 7))) := [

]

private def E3B : List (List (List (Fin 7))) := [
  [[0], [1], [2], [3], [4], [5]],
  [[0], [1], [3], [2], [4], [5]],
  [[0], [1], [4], [2], [3], [5]],
  [[0], [1], [5], [2], [3], [4]],
  [[0], [2], [3], [1], [4], [5]],
  [[0], [2], [4], [1], [3], [5]],
  [[0], [2], [5], [1], [3], [4]],
  [[0], [3], [4], [1], [2], [5]],
  [[0], [3], [5], [1], [2], [4]],
  [[0], [4], [5], [1], [2], [3]]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem E3_check :
    (candidates 6 (fun i => ([4, 4, 4, 4, 4, 2] : List Nat)[i.val]'i.isLt - 1)).all
      (fun H => detects H.cone E3K E3B) := by
  decide +kernel

theorem E3_nonplanar : ¬ Planaric [6, 4, 4, 4, 4, 4, 2] := by
  intro h
  obtain ⟨G,hp,hd⟩ := planaric_universal (n := 6) [4, 4, 4, 4, 4, 2] rfl h
  apply excluded G.cone E3K E3B _ hp
  apply List.all_eq_true.mp E3_check G
  apply candidates_complete
  intro v
  have he := hd v
  omega

private def F2K : List (List (List (Fin 7))) := [

]

private def F2B : List (List (List (Fin 7))) := [
  [[0], [1], [2], [4], [5], [6]],
  [[0], [1], [2, 4], [3], [5], [6]],
  [[0], [1], [2, 5], [3], [4], [6]],
  [[0], [1], [2, 6], [3], [4], [5]],
  [[0], [1, 4], [2], [3], [5], [6]],
  [[0], [1, 5], [2], [3], [4], [6]],
  [[0], [1, 6], [2], [3], [4], [5]]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem F2_check :
    (candidates 6 (fun i => ([5, 5, 3, 3, 3, 3] : List Nat)[i.val]'i.isLt - 1)).all
      (fun H => detects H.cone F2K F2B) := by
  decide +kernel

theorem F2_nonplanar : ¬ Planaric [6, 5, 5, 3, 3, 3, 3] := by
  intro h
  obtain ⟨G,hp,hd⟩ := planaric_universal (n := 6) [5, 5, 3, 3, 3, 3] rfl h
  apply excluded G.cone F2K F2B _ hp
  apply List.all_eq_true.mp F2_check G
  apply candidates_complete
  intro v
  have he := hd v
  omega

/-- All three universal-root exceptional families, including zero leaves. -/
theorem upper_universal_exceptions (l : Nat) :
    (¬ Planaric ((5+l)::([4,4,4,4,3] ++ List.replicate l 1))) ∧
    (¬ Planaric ((6+l)::([4,4,4,4,4,2] ++ List.replicate l 1))) ∧
    (¬ Planaric ((6+l)::([5,5,3,3,3,3] ++ List.replicate l 1))) :=
  ⟨fun h => E1_nonplanar (strip_forced_leaves _ l h),
   fun h => E3_nonplanar (strip_forced_leaves _ l h),
   fun h => F2_nonplanar (strip_forced_leaves _ l h)⟩

end SparseBoundary.Graph
