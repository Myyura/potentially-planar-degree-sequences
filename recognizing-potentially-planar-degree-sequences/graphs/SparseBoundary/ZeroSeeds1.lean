import SparseBoundary.ZeroGrowth
import SparseBoundary.GraphContractionLayer8

namespace SparseBoundary.ZeroSeeds1
open Graph ZeroGrowth
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def g8 : Graph 8 := ⟨244150843⟩
private theorem p8 : g8.Planar := by
  let host : Graph 8 := ⟨0xa7cf1eb⟩
  have hp : host.Planar := ContractionLayer8.known host (by decide +kernel)
  let relabel (i : Fin 8) : Fin 8 := ([1, 7, 0, 4, 5, 2, 6, 3] : List (Fin 8))[i.val]!
  exact planar_subgraph_map hp relabel (by decide +kernel) (by decide +kernel)

-- Truncate vertex zero. Contract the first site onto the old second
-- vertex. The other two sites form the distinguished three-valent edge.
private def g9 : Graph 9 := ⟨62387929999⟩
private theorem p9 : g9.Planar := by
  let t : Graph 10 := ⟨31913990451343⟩
  have ht : t.Planar := Truncation.planar (n:=7) (H:=g8)
    ⟨Truncation.triple 0 1 2, by decide +kernel, by decide +kernel, by decide +kernel⟩ p8
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def g10 : Graph 10 := ⟨31913990451319⟩
private theorem p10 : g10.Planar := by
  let t : Graph 11 := ⟨32665451215194895⟩
  have ht : t.Planar := Truncation.planar (n:=8) (H:=g9)
    ⟨Truncation.triple 0 2 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p9
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def g11 : Graph 11 := ⟨32665451215193911⟩
private theorem p11 : g11.Planar := by
  let t : Graph 12 := ⟨66884114786906366735⟩
  have ht : t.Planar := Truncation.planar (n:=9) (H:=g10)
    ⟨Truncation.triple 0 3 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p10
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def g12 : Graph 12 := ⟨66884114786906334007⟩
private theorem p12 : g12.Planar := by
  let t : Graph 13 := ⟨273927263508408913388303⟩
  have ht : t.Planar := Truncation.planar (n:=10) (H:=g11)
    ⟨Truncation.triple 0 4 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p11
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def g13 : Graph 13 := ⟨273927263508408911291191⟩
private theorem p13 : g13.Planar := by
  let t : Graph 14 := ⟨2243889167314955802588504847⟩
  have ht : t.Planar := Truncation.planar (n:=11) (H:=g12)
    ⟨Truncation.triple 0 5 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p12
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

theorem two (i : Fin 6) : Planaric ([6, 3, 3] ++ List.replicate (i.val+5) 4) := by
  have cases6 : ∀ x : Fin 6, x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 := by decide
  rcases cases6 i with rfl|rfl|rfl|rfl|rfl|rfl
  · exact profile p8 (by decide +kernel)
  · exact profile p9 (by decide +kernel)
  · exact profile p10 (by decide +kernel)
  · exact profile p11 (by decide +kernel)
  · exact profile p12 (by decide +kernel)
  · exact profile p13 (by decide +kernel)

end SparseBoundary.ZeroSeeds1
