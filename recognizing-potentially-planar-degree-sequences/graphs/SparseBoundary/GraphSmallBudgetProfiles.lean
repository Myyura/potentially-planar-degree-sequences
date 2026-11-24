import SparseBoundary.GraphContractionLayer13
import SparseBoundary.GraphTwoIncrements

namespace SparseBoundary.FourCore.FiniteProfiles
open Graph

/-- The seven low-budget profiles, in the order regular, two fives,
one six, and four profiles with a single three. -/
def Profiles (p : Nat) :=
  Planaric (List.replicate p 4) ∧
  Planaric ([2, 5, 5] ++ List.replicate (p-2) 4) ∧
  Planaric ([2, 6] ++ List.replicate (p-1) 4) ∧
  Planaric ([5] ++ List.replicate (p-2) 4 ++ [3]) ∧
  Planaric ([2, 7] ++ List.replicate (p-2) 4 ++ [3]) ∧
  Planaric ([2, 6, 5] ++ List.replicate (p-3) 4 ++ [3]) ∧
  Planaric ([2, 5, 5, 5] ++ List.replicate (p-4) 4 ++ [3])

private def readMap (code : Nat) (i : Fin n) : Fin n :=
  ⟨((code >>> (4*i.val)) % 16) % n,Nat.mod_lt _ (by have := i.isLt; omega)⟩

namespace Order8

private def regular : Graph 8 := ⟨0xcce4e6d⟩
private theorem regular_planar : regular.Planar :=
  planar_subgraph_map (ContractionLayer8.known (⟨0xece4e6f⟩ : Graph 8) (by decide +kernel))
    (readMap 0x76543210) (by decide +kernel) (by decide +kernel)
private theorem regular_real : regular.Realizes [4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 8,regular.degree i=([4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def mixed : Graph 8 := ⟨0xa74f1ab⟩
private theorem mixed_planar : mixed.Planar :=
  planar_subgraph_map (ContractionLayer8.known (⟨0xa7cf1eb⟩ : Graph 8) (by decide +kernel))
    (readMap 0x76543210) (by decide +kernel) (by decide +kernel)
private theorem mixed_real : mixed.Realizes [5, 3, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 8,mixed.degree i=([5, 3, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def sortedmixed : Graph 8 := ⟨0x934d797⟩
private theorem sortedmixed_planar : sortedmixed.Planar :=
  planar_subgraph_map (ContractionLayer8.known (⟨0xa7cf1eb⟩ : Graph 8) (by decide +kernel))
    (readMap 0x17654320) (by decide +kernel) (by decide +kernel)
private theorem sortedmixed_real : sortedmixed.Realizes [5, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 8,sortedmixed.degree i=([5, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def sixfive : Graph 8 := ⟨0x934d797⟩
private theorem sixfive_planar : sixfive.Planar :=
  planar_subgraph_map (ContractionLayer8.known (⟨0xa7cf1eb⟩ : Graph 8) (by decide +kernel))
    (readMap 0x17654320) (by decide +kernel) (by decide +kernel)
private theorem sixfive_real : sixfive.Realizes [5, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 8,sixfive.degree i=([5, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def five3 : Graph 8 := ⟨0x9965acf⟩
private theorem five3_planar : five3.Planar :=
  planar_subgraph_map (ContractionLayer8.known (⟨0xa7cf1eb⟩ : Graph 8) (by decide +kernel))
    (readMap 0x17654032) (by decide +kernel) (by decide +kernel)
private theorem five3_real : five3.Realizes [4, 4, 5, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 8,five3.degree i=([4, 4, 5, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def seven : Graph 8 := ⟨0x92cde67⟩
private theorem seven_planar : seven.Planar :=
  planar_subgraph_map (ContractionLayer8.known (⟨0xe6ece6b⟩ : Graph 8) (by decide +kernel))
    (readMap 0x15347620) (by decide +kernel) (by decide +kernel)
private theorem seven_real : seven.Realizes [6, 3, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 8,seven.degree i=([6, 3, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

theorem all_profiles : Profiles 8 := by
  exact ⟨⟨regular,regular_real,regular_planar⟩,
    first_two_increments regular_real regular_planar (by decide +kernel),
    first_two_increments mixed_real mixed_planar (by decide +kernel),
    ⟨sortedmixed,sortedmixed_real,sortedmixed_planar⟩,
    first_two_increments seven_real seven_planar (by decide +kernel),
    first_two_increments sixfive_real sixfive_planar (by decide +kernel),
    first_two_increments five3_real five3_planar (by decide +kernel)⟩

private def lowerThree : Graph 8 := ⟨0xb08f91f⟩
private theorem lowerThree_planar : lowerThree.Planar :=
  planar_subgraph_map (ContractionLayer8.known (⟨0xece4e6f⟩ : Graph 8) (by decide +kernel))
    (readMap 0x43765210) (by decide +kernel) (by decide +kernel)
theorem lower_twothree : Planaric [4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨lowerThree,?_,lowerThree_planar⟩
  show ∀ i : Fin 8,lowerThree.degree i=([4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

private def upperThree : Graph 8 := ⟨0x265f9ab⟩
private theorem upperThree_planar : upperThree.Planar :=
  planar_subgraph_map (ContractionLayer8.known (⟨0xece4e6f⟩ : Graph 8) (by decide +kernel))
    (readMap 0x31765420) (by decide +kernel) (by decide +kernel)
theorem upper_twothree : Planaric [5, 5, 4, 4, 4, 4, 3, 3] := by
  refine ⟨upperThree,?_,upperThree_planar⟩
  show ∀ i : Fin 8,upperThree.degree i=([5, 5, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

theorem six_twothree : Planaric [6, 4, 4, 4, 4, 4, 3, 3] := by
  apply (planaric_perm (d:=[6, 3, 4, 4, 4, 4, 4, 3]) (by decide +kernel)).mp
  exact ⟨seven,seven_real,seven_planar⟩

end Order8
namespace Order9

private def regular : Graph 9 := ⟨0x66791c26d⟩
private theorem regular_planar : regular.Planar :=
  planar_subgraph_map (ContractionLayer9.known (⟨0x66791d66f⟩ : Graph 9) (by decide +kernel))
    (readMap 0x876543210) (by decide +kernel) (by decide +kernel)
private theorem regular_real : regular.Realizes [4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 9,regular.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def mixed : Graph 9 := ⟨0x95395ce23⟩
private theorem mixed_planar : mixed.Planar :=
  planar_subgraph_map (ContractionLayer9.known (⟨0x95395ee6b⟩ : Graph 9) (by decide +kernel))
    (readMap 0x876543210) (by decide +kernel) (by decide +kernel)
private theorem mixed_real : mixed.Realizes [5, 3, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 9,mixed.degree i=([5, 3, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def sortedmixed : Graph 9 := ⟨0x319675665⟩
private theorem sortedmixed_planar : sortedmixed.Planar :=
  planar_subgraph_map (ContractionLayer9.known (⟨0x95395ee6b⟩ : Graph 9) (by decide +kernel))
    (readMap 0x187654320) (by decide +kernel) (by decide +kernel)
private theorem sortedmixed_real : sortedmixed.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 9,sortedmixed.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def sixfive : Graph 9 := ⟨0x319675665⟩
private theorem sixfive_planar : sixfive.Planar :=
  planar_subgraph_map (ContractionLayer9.known (⟨0x95395ee6b⟩ : Graph 9) (by decide +kernel))
    (readMap 0x187654320) (by decide +kernel) (by decide +kernel)
private theorem sixfive_real : sixfive.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 9,sixfive.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def five3 : Graph 9 := ⟨0x349a5db13⟩
private theorem five3_planar : five3.Planar :=
  planar_subgraph_map (ContractionLayer9.known (⟨0x95395ee6b⟩ : Graph 9) (by decide +kernel))
    (readMap 0x187654032) (by decide +kernel) (by decide +kernel)
private theorem five3_real : five3.Realizes [4, 4, 5, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 9,five3.degree i=([4, 4, 5, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def seven : Graph 9 := ⟨0x15cd48f69⟩
private theorem seven_planar : seven.Planar :=
  planar_subgraph_map (ContractionLayer9.known (⟨0xa3cee866f⟩ : Graph 9) (by decide +kernel))
    (readMap 0x562381740) (by decide +kernel) (by decide +kernel)
private theorem seven_real : seven.Realizes [6, 3, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 9,seven.degree i=([6, 3, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

theorem all_profiles : Profiles 9 := by
  exact ⟨⟨regular,regular_real,regular_planar⟩,
    first_two_increments regular_real regular_planar (by decide +kernel),
    first_two_increments mixed_real mixed_planar (by decide +kernel),
    ⟨sortedmixed,sortedmixed_real,sortedmixed_planar⟩,
    first_two_increments seven_real seven_planar (by decide +kernel),
    first_two_increments sixfive_real sixfive_planar (by decide +kernel),
    first_two_increments five3_real five3_planar (by decide +kernel)⟩

private def lowerThree : Graph 9 := ⟨0x7052b30ed⟩
private theorem lowerThree_planar : lowerThree.Planar :=
  planar_subgraph_map (ContractionLayer9.known (⟨0x66791d66f⟩ : Graph 9) (by decide +kernel))
    (readMap 0x548763210) (by decide +kernel) (by decide +kernel)
theorem lower_twothree : Planaric [4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨lowerThree,?_,lowerThree_planar⟩
  show ∀ i : Fin 9,lowerThree.degree i=([4, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

private def upperThree : Graph 9 := ⟨0x51389bcb3⟩
private theorem upperThree_planar : upperThree.Planar :=
  planar_subgraph_map (ContractionLayer9.known (⟨0x66791d66f⟩ : Graph 9) (by decide +kernel))
    (readMap 0x108764352) (by decide +kernel) (by decide +kernel)
theorem upper_twothree : Planaric [5, 5, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨upperThree,?_,upperThree_planar⟩
  show ∀ i : Fin 9,upperThree.degree i=([5, 5, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

theorem six_twothree : Planaric [6, 4, 4, 4, 4, 4, 4, 3, 3] := by
  apply (planaric_perm (d:=[6, 3, 4, 4, 4, 4, 4, 4, 3]) (by decide +kernel)).mp
  exact ⟨seven,seven_real,seven_planar⟩

end Order9
namespace Order10

private def regular : Graph 10 := ⟨0x1468c711c665⟩
private theorem regular_planar : regular.Planar :=
  planar_subgraph_map (ContractionLayer10.known (⟨0x166ac711c66f⟩ : Graph 10) (by decide +kernel))
    (readMap 0x9876543210) (by decide +kernel) (by decide +kernel)
private theorem regular_real : regular.Realizes [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 10,regular.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def mixed : Graph 10 := ⟨0x18c07d11e343⟩
private theorem mixed_planar : mixed.Planar :=
  planar_subgraph_map (ContractionLayer10.known (⟨0x18e07d51e763⟩ : Graph 10) (by decide +kernel))
    (readMap 0x9876543210) (by decide +kernel) (by decide +kernel)
private theorem mixed_real : mixed.Realizes [5, 3, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 10,mixed.degree i=([5, 3, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def sortedmixed : Graph 10 := ⟨0xa1c607a4739⟩
private theorem sortedmixed_planar : sortedmixed.Planar :=
  planar_subgraph_map (ContractionLayer10.known (⟨0x18e07d51e763⟩ : Graph 10) (by decide +kernel))
    (readMap 0x1987654320) (by decide +kernel) (by decide +kernel)
private theorem sortedmixed_real : sortedmixed.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 10,sortedmixed.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def sixfive : Graph 10 := ⟨0xa1c607a4739⟩
private theorem sixfive_planar : sixfive.Planar :=
  planar_subgraph_map (ContractionLayer10.known (⟨0x18e07d51e763⟩ : Graph 10) (by decide +kernel))
    (readMap 0x1987654320) (by decide +kernel) (by decide +kernel)
private theorem sixfive_real : sixfive.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 10,sixfive.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def five3 : Graph 10 := ⟨0xa4c90bc5297⟩
private theorem five3_planar : five3.Planar :=
  planar_subgraph_map (ContractionLayer10.known (⟨0x18e07d51e763⟩ : Graph 10) (by decide +kernel))
    (readMap 0x1987653042) (by decide +kernel) (by decide +kernel)
private theorem five3_real : five3.Realizes [4, 4, 5, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 10,five3.degree i=([4, 4, 5, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def seven : Graph 10 := ⟨0x1888307ab761⟩
private theorem seven_planar : seven.Planar :=
  planar_subgraph_map (ContractionLayer10.known (⟨0x127a5d3c464f⟩ : Graph 10) (by decide +kernel))
    (readMap 0x8294537610) (by decide +kernel) (by decide +kernel)
private theorem seven_real : seven.Realizes [6, 3, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 10,seven.degree i=([6, 3, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

theorem all_profiles : Profiles 10 := by
  exact ⟨⟨regular,regular_real,regular_planar⟩,
    first_two_increments regular_real regular_planar (by decide +kernel),
    first_two_increments mixed_real mixed_planar (by decide +kernel),
    ⟨sortedmixed,sortedmixed_real,sortedmixed_planar⟩,
    first_two_increments seven_real seven_planar (by decide +kernel),
    first_two_increments sixfive_real sixfive_planar (by decide +kernel),
    first_two_increments five3_real five3_planar (by decide +kernel)⟩

private def lowerThree : Graph 10 := ⟨0x4c07e4a4e29⟩
private theorem lowerThree_planar : lowerThree.Planar :=
  planar_subgraph_map (ContractionLayer10.known (⟨0x166ac711c66f⟩ : Graph 10) (by decide +kernel))
    (readMap 0x7298654310) (by decide +kernel) (by decide +kernel)
theorem lower_twothree : Planaric [4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨lowerThree,?_,lowerThree_planar⟩
  show ∀ i : Fin 10,lowerThree.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

private def upperThree : Graph 10 := ⟨0x834a633497a⟩
private theorem upperThree_planar : upperThree.Planar :=
  planar_subgraph_map (ContractionLayer10.known (⟨0x166ac711c66f⟩ : Graph 10) (by decide +kernel))
    (readMap 0x8176542093) (by decide +kernel) (by decide +kernel)
theorem upper_twothree : Planaric [5, 5, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨upperThree,?_,upperThree_planar⟩
  show ∀ i : Fin 10,upperThree.degree i=([5, 5, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

theorem six_twothree : Planaric [6, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  apply (planaric_perm (d:=[6, 3, 4, 4, 4, 4, 4, 4, 4, 3]) (by decide +kernel)).mp
  exact ⟨seven,seven_real,seven_planar⟩

end Order10
namespace Order11

private def regular : Graph 11 := ⟨0x50c4c788704665⟩
private theorem regular_planar : regular.Planar :=
  planar_subgraph_map (ContractionLayer11.known (⟨0x58c4c78874c66f⟩ : Graph 11) (by decide +kernel))
    (readMap 0xa9876543210) (by decide +kernel) (by decide +kernel)
private theorem regular_real : regular.Realizes [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 11,regular.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def mixed : Graph 11 := ⟨0x227860cc364661⟩
private theorem mixed_planar : mixed.Planar :=
  planar_subgraph_map (ContractionLayer11.known (⟨0x237870ecb66661⟩ : Graph 11) (by decide +kernel))
    (readMap 0xa9876543210) (by decide +kernel) (by decide +kernel)
private theorem mixed_real : mixed.Realizes [5, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 11,mixed.degree i=([5, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def sortedmixed : Graph 11 := ⟨0x60289c20d8da6c⟩
private theorem sortedmixed_planar : sortedmixed.Planar :=
  planar_subgraph_map (ContractionLayer11.known (⟨0x237870ecb66661⟩ : Graph 11) (by decide +kernel))
    (readMap 0x1a987654320) (by decide +kernel) (by decide +kernel)
private theorem sortedmixed_real : sortedmixed.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 11,sortedmixed.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def sixfive : Graph 11 := ⟨0x60283c4198f0f1⟩
private theorem sixfive_planar : sixfive.Planar :=
  planar_subgraph_map (ContractionLayer11.known (⟨0x237870ecb66661⟩ : Graph 11) (by decide +kernel))
    (readMap 0x1a987653240) (by decide +kernel) (by decide +kernel)
private theorem sixfive_real : sixfive.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 11,sixfive.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def five3 : Graph 11 := ⟨0x6088cc107a4f31⟩
private theorem five3_planar : five3.Planar :=
  planar_subgraph_map (ContractionLayer11.known (⟨0x237870ecb66661⟩ : Graph 11) (by decide +kernel))
    (readMap 0x1a987654032) (by decide +kernel) (by decide +kernel)
private theorem five3_real : five3.Realizes [4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 11,five3.degree i=([4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def seven : Graph 11 := ⟨0x20a78861d8a643⟩
private theorem seven_planar : seven.Planar :=
  planar_subgraph_map (ContractionLayer11.known (⟨0x1e10f3bc28e46b⟩ : Graph 11) (by decide +kernel))
    (readMap 0x2a987654310) (by decide +kernel) (by decide +kernel)
private theorem seven_real : seven.Realizes [6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 11,seven.degree i=([6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

theorem all_profiles : Profiles 11 := by
  exact ⟨⟨regular,regular_real,regular_planar⟩,
    first_two_increments regular_real regular_planar (by decide +kernel),
    first_two_increments mixed_real mixed_planar (by decide +kernel),
    ⟨sortedmixed,sortedmixed_real,sortedmixed_planar⟩,
    first_two_increments seven_real seven_planar (by decide +kernel),
    first_two_increments sixfive_real sixfive_planar (by decide +kernel),
    first_two_increments five3_real five3_planar (by decide +kernel)⟩

private def lowerThree : Graph 11 := ⟨0x24451a259c0267⟩
private theorem lowerThree_planar : lowerThree.Planar :=
  planar_subgraph_map (ContractionLayer11.known (⟨0x58c4c78874c66f⟩ : Graph 11) (by decide +kernel))
    (readMap 0x75a98643210) (by decide +kernel) (by decide +kernel)
theorem lower_twothree : Planaric [4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨lowerThree,?_,lowerThree_planar⟩
  show ∀ i : Fin 11,lowerThree.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

private def upperThree : Graph 11 := ⟨0x20ae08c15944f3⟩
private theorem upperThree_planar : upperThree.Planar :=
  planar_subgraph_map (ContractionLayer11.known (⟨0x58c4c78874c66f⟩ : Graph 11) (by decide +kernel))
    (readMap 0x76a98542130) (by decide +kernel) (by decide +kernel)
theorem upper_twothree : Planaric [5, 5, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨upperThree,?_,upperThree_planar⟩
  show ∀ i : Fin 11,upperThree.degree i=([5, 5, 4, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

theorem six_twothree : Planaric [6, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  apply (planaric_perm (d:=[6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3]) (by decide +kernel)).mp
  exact ⟨seven,seven_real,seven_planar⟩

end Order11
namespace Order12

private def regular : Graph 12 := ⟨0x2434191870870c625⟩
private theorem regular_planar : regular.Planar :=
  planar_subgraph_map (ContractionLayer12.known (⟨0x2634995870870c66f⟩ : Graph 12) (by decide +kernel))
    (readMap 0xba9876543210) (by decide +kernel) (by decide +kernel)
private theorem regular_real : regular.Realizes [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 12,regular.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def mixed : Graph 12 := ⟨0x1941940b2ca2a1541⟩
private theorem mixed_planar : mixed.Planar :=
  planar_subgraph_map (ContractionLayer12.known (⟨0x19499e0b2ca2a1573⟩ : Graph 12) (by decide +kernel))
    (readMap 0xba9876543210) (by decide +kernel) (by decide +kernel)
private theorem mixed_real : mixed.Realizes [5, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 12,mixed.degree i=([5, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def sortedmixed : Graph 12 := ⟨0x180b2864052d4a8d8⟩
private theorem sortedmixed_planar : sortedmixed.Planar :=
  planar_subgraph_map (ContractionLayer12.known (⟨0x19499e0b2ca2a1573⟩ : Graph 12) (by decide +kernel))
    (readMap 0x1ba987654320) (by decide +kernel) (by decide +kernel)
private theorem sortedmixed_real : sortedmixed.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 12,sortedmixed.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def sixfive : Graph 12 := ⟨0x180b3068093919945⟩
private theorem sixfive_planar : sixfive.Planar :=
  planar_subgraph_map (ContractionLayer12.known (⟨0x19499e0b2ca2a1573⟩ : Graph 12) (by decide +kernel))
    (readMap 0x1ba987653240) (by decide +kernel) (by decide +kernel)
private theorem sixfive_real : sixfive.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 12,sixfive.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def five3 : Graph 12 := ⟨0x182330680c3330d45⟩
private theorem five3_planar : five3.Planar :=
  planar_subgraph_map (ContractionLayer12.known (⟨0x19499e0b2ca2a1573⟩ : Graph 12) (by decide +kernel))
    (readMap 0x1ba987653042) (by decide +kernel) (by decide +kernel)
private theorem five3_real : five3.Realizes [4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 12,five3.degree i=([4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def seven : Graph 12 := ⟨0x160306c43880236cb⟩
private theorem seven_planar : seven.Planar :=
  planar_subgraph_map (ContractionLayer12.known (⟨0x185b1a7a8d18ccc49⟩ : Graph 12) (by decide +kernel))
    (readMap 0x2ba987654310) (by decide +kernel) (by decide +kernel)
private theorem seven_real : seven.Realizes [6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 12,seven.degree i=([6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

theorem all_profiles : Profiles 12 := by
  exact ⟨⟨regular,regular_real,regular_planar⟩,
    first_two_increments regular_real regular_planar (by decide +kernel),
    first_two_increments mixed_real mixed_planar (by decide +kernel),
    ⟨sortedmixed,sortedmixed_real,sortedmixed_planar⟩,
    first_two_increments seven_real seven_planar (by decide +kernel),
    first_two_increments sixfive_real sixfive_planar (by decide +kernel),
    first_two_increments five3_real five3_planar (by decide +kernel)⟩

private def lowerThree : Graph 12 := ⟨0x220891328cb084c27⟩
private theorem lowerThree_planar : lowerThree.Planar :=
  planar_subgraph_map (ContractionLayer12.known (⟨0x2634995870870c66f⟩ : Graph 12) (by decide +kernel))
    (readMap 0x54ba98763210) (by decide +kernel) (by decide +kernel)
theorem lower_twothree : Planaric [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨lowerThree,?_,lowerThree_planar⟩
  show ∀ i : Fin 12,lowerThree.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

private def upperThree : Graph 12 := ⟨0x1052848c708b044f3⟩
private theorem upperThree_planar : upperThree.Planar :=
  planar_subgraph_map (ContractionLayer12.known (⟨0x2634995870870c66f⟩ : Graph 12) (by decide +kernel))
    (readMap 0xa9b876542130) (by decide +kernel) (by decide +kernel)
theorem upper_twothree : Planaric [5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨upperThree,?_,upperThree_planar⟩
  show ∀ i : Fin 12,upperThree.degree i=([5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

theorem six_twothree : Planaric [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  apply (planaric_perm (d:=[6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3]) (by decide +kernel)).mp
  exact ⟨seven,seven_real,seven_planar⟩

end Order12
namespace Order13

private def regular : Graph 13 := ⟨0x241a06130f083810c625⟩
private theorem regular_planar : regular.Planar :=
  planar_subgraph_map (ContractionLayer13.known (⟨0x261a46130f083a30c66f⟩ : Graph 13) (by decide +kernel))
    (readMap 0xcba9876543210) (by decide +kernel) (by decide +kernel)
private theorem regular_real : regular.Realizes [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 13,regular.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def mixed : Graph 13 := ⟨0x8b308a8260467224071⟩
private theorem mixed_planar : mixed.Planar :=
  planar_subgraph_map (ContractionLayer13.known (⟨0x8b328a827447722607d⟩ : Graph 13) (by decide +kernel))
    (readMap 0xcba9876543210) (by decide +kernel) (by decide +kernel)
private theorem mixed_real : mixed.Realizes [5, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  show ∀ i : Fin 13,mixed.degree i=([5, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] : List Nat)[i]
  decide +kernel

private def sortedmixed : Graph 13 := ⟨0x2148b612a13044e8a0c⟩
private theorem sortedmixed_planar : sortedmixed.Planar :=
  planar_subgraph_map (ContractionLayer13.known (⟨0x8b328a827447722607d⟩ : Graph 13) (by decide +kernel))
    (readMap 0x1cba987654320) (by decide +kernel) (by decide +kernel)
private theorem sortedmixed_real : sortedmixed.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 13,sortedmixed.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def sixfive : Graph 13 := ⟨0x2248e606a13048d90a1⟩
private theorem sixfive_planar : sixfive.Planar :=
  planar_subgraph_map (ContractionLayer13.known (⟨0x8b328a827447722607d⟩ : Graph 13) (by decide +kernel))
    (readMap 0x1cba987653240) (by decide +kernel) (by decide +kernel)
private theorem sixfive_real : sixfive.Realizes [5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 13,sixfive.degree i=([5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def five3 : Graph 13 := ⟨0x21889e18a43042f0621⟩
private theorem five3_planar : five3.Planar :=
  planar_subgraph_map (ContractionLayer13.known (⟨0x8b328a827447722607d⟩ : Graph 13) (by decide +kernel))
    (readMap 0x1cba987654032) (by decide +kernel) (by decide +kernel)
private theorem five3_real : five3.Realizes [4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 13,five3.degree i=([4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

private def seven : Graph 13 := ⟨0x240448f110c01a1c4c27⟩
private theorem seven_planar : seven.Planar :=
  planar_subgraph_map (ContractionLayer13.known (⟨0x4978a43205b4e51869b⟩ : Graph 13) (by decide +kernel))
    (readMap 0x2cba987654310) (by decide +kernel) (by decide +kernel)
private theorem seven_real : seven.Realizes [6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] := by
  show ∀ i : Fin 13,seven.degree i=([6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

theorem all_profiles : Profiles 13 := by
  exact ⟨⟨regular,regular_real,regular_planar⟩,
    first_two_increments regular_real regular_planar (by decide +kernel),
    first_two_increments mixed_real mixed_planar (by decide +kernel),
    ⟨sortedmixed,sortedmixed_real,sortedmixed_planar⟩,
    first_two_increments seven_real seven_planar (by decide +kernel),
    first_two_increments sixfive_real sixfive_planar (by decide +kernel),
    first_two_increments five3_real five3_planar (by decide +kernel)⟩

private def lowerThree : Graph 13 := ⟨0x2c0c848d0c28611806d⟩
private theorem lowerThree_planar : lowerThree.Planar :=
  planar_subgraph_map (ContractionLayer13.known (⟨0x261a46130f083a30c66f⟩ : Graph 13) (by decide +kernel))
    (readMap 0x64cba98753210) (by decide +kernel) (by decide +kernel)
theorem lower_twothree : Planaric [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨lowerThree,?_,lowerThree_planar⟩
  show ∀ i : Fin 13,lowerThree.degree i=([4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

private def upperThree : Graph 13 := ⟨0x108560026e08e05206f2⟩
private theorem upperThree_planar : upperThree.Planar :=
  planar_subgraph_map (ContractionLayer13.known (⟨0x261a46130f083a30c66f⟩ : Graph 13) (by decide +kernel))
    (readMap 0xa6b98754210c3) (by decide +kernel) (by decide +kernel)
theorem upper_twothree : Planaric [5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  refine ⟨upperThree,?_,upperThree_planar⟩
  show ∀ i : Fin 13,upperThree.degree i=([5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

theorem six_twothree : Planaric [6, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3] := by
  apply (planaric_perm (d:=[6, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3]) (by decide +kernel)).mp
  exact ⟨seven,seven_real,seven_planar⟩

end Order13

end SparseBoundary.FourCore.FiniteProfiles
