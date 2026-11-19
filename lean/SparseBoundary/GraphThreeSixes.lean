import SparseBoundary.GraphEnumeration
import SparseBoundary.GraphFiniteTest

namespace SparseBoundary.Graph

private def witnesses : Array (List (List (Fin 8))) := #[
  [[0], [1], [2], [3], [4], [5]],
  [[0], [1], [2], [3], [4], [6]],
  [[0], [1], [2], [3], [5], [6]],
  [[0], [1], [2], [4], [5], [6]],
  [[0], [1], [2, 6], [3], [4], [5]],
  [[0], [1, 6], [2], [3], [4], [5]],
  [[0], [1], [2, 5], [3], [4], [6]],
  [[0], [1, 5], [2], [3], [4], [6]],
  [[0], [1], [2, 4], [3], [5], [6]],
  [[0], [1, 4], [2], [3], [5], [6]],
  [[0, 6], [1], [2], [3], [4], [5]],
  [[0, 5], [1], [2], [3], [4], [6]],
  [[0, 4], [1], [2], [3], [5], [6]]
]

/-- Pairs of adjacency masks and indices in the branch-set certificate table. -/
private def indices : Array (Nat × Nat) := #[
  (6528510, 0), (6528887, 12), (6528943, 9), (6534647, 11), (6535663, 7),
  (6542783, 9), (6543743, 7), (6725111, 10), (6757871, 5), (6987199, 9),
  (7019903, 5), (7510527, 7), (7542271, 5), (10722813, 0), (10723063, 12),
  (10723231, 8), (10726903, 11), (10729951, 6), (10735039, 8), (10737919, 6),
  (10853879, 10), (10952159, 4), (11115967, 8), (11214079, 4), (11639295, 6),
  (11734527, 4), (12819963, 0), (12820207, 9), (12820319, 8), (12824047, 7),
  (12826079, 6), (12832127, 7), (12834047, 6), (12951023, 5), (13016543, 4),
  (13213055, 5), (13278463, 4), (13735423, 5), (13798911, 4), (19111415, 3),
  (21208559, 3), (25402847, 3), (35888575, 2), (37985663, 2), (42179839, 2),
  (69442047, 1), (71538175, 1), (75730431, 1), (136519167, 0), (138583551, 0),
  (142712319, 0)
]

private def select (v : Nat) : Nat :=
  ((indices.binSearch (v, 0) (fun a b => a.1 < b.1)).getD (v, 0)).2

private def profile : List Nat := [6, 6, 6, 3, 3, 3, 3, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
private theorem certificate_check :
    (candidates 8 (fun i => profile[i.val]!)).all
      (fun G => certificateTest G (witnesses[select G.bits.toNat]?.getD [])) := by
  decide +kernel

theorem ThreeSixes_nonplanar : ¬ Planaric [6, 6, 6, 3, 3, 3, 3, 2] := by
  intro ⟨G,hd,hp⟩
  have hc : G ∈ candidates 8 (fun i => profile[i.val]!) :=
    candidates_complete G _ (fun i => by simpa [profile] using hd i)
  exact certificate_nonplanar G _ (List.all_eq_true.mp certificate_check G hc) hp

end SparseBoundary.Graph
