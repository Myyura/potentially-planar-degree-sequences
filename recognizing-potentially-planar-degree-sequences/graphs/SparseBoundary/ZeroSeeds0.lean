import SparseBoundary.ZeroGrowth
import SparseBoundary.GraphContractionLayer8

namespace SparseBoundary.ZeroSeeds0
open Graph ZeroGrowth
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def g8 : Graph 8 := ⟨58159875⟩
private theorem p8 : g8.Planar := by
  let host : Graph 8 := ⟨0xece4e6f⟩
  have hp : host.Planar := ContractionLayer8.known host (by decide +kernel)
  let relabel (i : Fin 8) : Fin 8 := ([0, 1, 3, 7, 4, 6, 2, 5] : List (Fin 8))[i.val]!
  exact planar_subgraph_map hp relabel (by decide +kernel) (by decide +kernel)

-- Truncate vertex zero. Contract the first site onto the old second
-- vertex. The other two sites form the distinguished three-valent edge.
private def g9 : Graph 9 := ⟨14690312207⟩
private theorem p9 : g9.Planar := by
  let t : Graph 10 := ⟨7471332065423⟩
  have ht : t.Planar := Truncation.planar (n:=7) (H:=g8)
    ⟨Truncation.triple 0 1 6, by decide +kernel, by decide +kernel, by decide +kernel⟩ p8
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def single8 : Graph 8 := ⟨58159879⟩
private theorem ps8 : single8.Planar :=
  contract p9 2 (by decide +kernel) (by decide +kernel)

private def g10 : Graph 10 := ⟨7471332065399⟩
private theorem p10 : g10.Planar := by
  let t : Graph 11 := ⟨7625173469498127⟩
  have ht : t.Planar := Truncation.planar (n:=8) (H:=g9)
    ⟨Truncation.triple 0 2 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p9
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def single9 : Graph 9 := ⟨14690312223⟩
private theorem ps9 : single9.Planar :=
  contract p10 3 (by decide +kernel) (by decide +kernel)

private def g11 : Graph 11 := ⟨7625173469497143⟩
private theorem p11 : g11.Planar := by
  let t : Graph 12 := ⟨15590366847915090703⟩
  have ht : t.Planar := Truncation.planar (n:=9) (H:=g10)
    ⟨Truncation.triple 0 3 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p10
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def single10 : Graph 10 := ⟨7471332065527⟩
private theorem ps10 : single10.Planar :=
  contract p11 4 (by decide +kernel) (by decide +kernel)

private def g12 : Graph 12 := ⟨15590366847915057975⟩
private theorem p12 : g12.Planar := by
  let t : Graph 13 := ⟨63805013459537801798415⟩
  have ht : t.Planar := Truncation.planar (n:=10) (H:=g11)
    ⟨Truncation.triple 0 4 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p11
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def single11 : Graph 11 := ⟨7625173469499191⟩
private theorem ps11 : single11.Planar :=
  contract p12 5 (by decide +kernel) (by decide +kernel)

private def g13 : Graph 13 := ⟨63805013459537799701303⟩
private theorem p13 : g13.Planar := by
  let t : Graph 14 := ⟨522473247522357663640347407⟩
  have ht : t.Planar := Truncation.planar (n:=11) (H:=g12)
    ⟨Truncation.triple 0 5 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p12
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def single12 : Graph 12 := ⟨15590366847915123511⟩
private theorem ps12 : single12.Planar :=
  contract p13 6 (by decide +kernel) (by decide +kernel)

private def g14 : Graph 14 := ⟨522473247522357663371911991⟩
private theorem p14 : g14.Planar := by
  let t : Graph 15 := ⟨8558421354854884467358356235023⟩
  have ht : t.Planar := Truncation.planar (n:=12) (H:=g13)
    ⟨Truncation.triple 0 6 1, by decide +kernel, by decide +kernel, by decide +kernel⟩ p13
  exact contract ht 2 (by decide +kernel) (by decide +kernel)

private def single13 : Graph 13 := ⟨63805013459537803895607⟩
private theorem ps13 : single13.Planar :=
  contract p14 7 (by decide +kernel) (by decide +kernel)

theorem two (i : Fin 6) : Planaric ([3, 3] ++ List.replicate (i.val+6) 4) := by
  have cases6 : ∀ x : Fin 6, x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 := by decide
  rcases cases6 i with rfl|rfl|rfl|rfl|rfl|rfl
  · exact profile p8 (by decide +kernel)
  · exact profile p9 (by decide +kernel)
  · exact profile p10 (by decide +kernel)
  · exact profile p11 (by decide +kernel)
  · exact profile p12 (by decide +kernel)
  · exact profile p13 (by decide +kernel)

theorem one (i : Fin 6) : Planaric ([5, 3] ++ List.replicate (i.val+6) 4) := by
  have cases6 : ∀ x : Fin 6, x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 := by decide
  rcases cases6 i with rfl|rfl|rfl|rfl|rfl|rfl
  · exact profile ps8 (by decide +kernel)
  · exact profile ps9 (by decide +kernel)
  · exact profile ps10 (by decide +kernel)
  · exact profile ps11 (by decide +kernel)
  · exact profile ps12 (by decide +kernel)
  · exact profile ps13 (by decide +kernel)

end SparseBoundary.ZeroSeeds0
