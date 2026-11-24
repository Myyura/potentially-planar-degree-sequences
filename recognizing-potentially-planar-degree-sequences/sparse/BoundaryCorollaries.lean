import FullBoundary

namespace SparseBoundary

/-- With at least three entries of degree two, only the two core-count
obstructions survive on the upper boundary. The input need not be sorted. -/
theorem upper_with_three_twos (d : List Nat) (positive : ∀ x ∈ d, 1 ≤ x)
    (graphic : Graphic d) (boundary : d.sum + 2 * d.count 1 = 4 * d.length)
    (twos : 3 ≤ d.count 2) :
    ¬ Planaric d ↔ highCount d = 5 ∨ (highCount d = 6 ∧ d.count 3 = 3) := by
  have nonempty : d ≠ [] := by rintro rfl; simp at twos
  rw [second_boundary_invariant d nonempty positive graphic boundary]
  constructor
  · rintro (five | six | ⟨e, mem, perm⟩ | ⟨e, mem, perm⟩)
    · exact Or.inl five
    · exact Or.inr six
    · have eq := perm.count_eq 2
      simp only [seeds, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;>
        simp [universals, List.count_replicate, show ∀ n : Nat, 5+n≠2 by omega,
          show ∀ n : Nat, 6+n≠2 by omega] at eq <;> omega
    · have eq := perm.count_eq 2
      simp only [isolated, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> simp at eq <;> omega
  · rintro (five | six)
    · exact Or.inl five
    · exact Or.inr (Or.inl six)

/-- This sequence on the upper boundary has two entries of degree two,
satisfies neither of the two surviving count rules, and is nonplanaric. -/
theorem two_twos_sharp :
    let d : List Nat := [5,5,5,5,5,3,2,2]
    Graphic d ∧ d.sum + 2*d.count 1 = 4*d.length ∧ d.count 2 = 2 ∧
      highCount d = 6 ∧ d.count 3 = 1 ∧ ¬Planaric d := by
  dsimp only
  refine ⟨?_, by decide, by decide, by decide, by decide, Graph.FiveFiveThree_nonplanar⟩
  exact ErdosGallai.sparse_graphic (a:=5) (b:=5) (t:=2) [5,5,5,3]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem graphic_grow_apex {a : Nat} {tail : List Nat}
    (initial : Graphic (a :: tail)) (l : Nat) : Graphic (universals a tail l) := by
  induction l with
  | zero => simpa [universals] using initial
  | succ l ih =>
    let oldTail := tail ++ List.replicate l 1
    change Graphic ((a+l)::oldTail) at ih
    obtain ⟨G, deg⟩ := ih
    have more : Graphic (1 :: (a+l+1) :: oldTail) := by
      refine ⟨G.withLeaf 0, ?_⟩
      intro i
      refine Fin.cases (by simp) (fun j => ?_) i
      rw [Graph.withLeaf_old_degree, deg]
      refine Fin.cases (by simp) (fun k => ?_) j
      simp [Fin.ne_of_gt (Fin.succ_pos _)]
    have move := List.perm_middle (a := 1) (l₁ := (a+l+1)::tail) (l₂ := List.replicate l 1)
    simpa [universals, oldTail, List.replicate_succ, Nat.add_assoc] using
      (graphic_perm move.symm).mp more

/-- With eight or more high-degree vertices every positive graphic sequence
on the upper boundary is planaric, also in the presence of leaves. -/
theorem upper_eight_core (d : List Nat) (positive : ∀ x ∈ d, 1 ≤ x)
    (graphic : Graphic d) (boundary : d.sum + 2*d.count 1 = 4*d.length)
    (eight : 8 ≤ highCount d) : Planaric d := by
  have ne : d ≠ [] := by rintro rfl; simp [highCount] at eight
  by_contra no
  have bad := (second_boundary_invariant d ne positive graphic boundary).mp no
  rcases bad with five | ⟨six,_⟩ | ⟨e,mem,perm⟩ | ⟨e,mem,perm⟩
  · omega
  · omega
  · change 8 ≤ d.countP _ at eight
    rw [perm.countP_eq] at eight
    simp only [seeds, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;>
      simp [universals, List.countP_eq_length_filter, show ∀ n : Nat, 3 ≤ 5+n by omega,
        show ∀ n : Nat, 3 ≤ 6+n by omega] at eight
  · change 8 ≤ d.countP _ at eight
    rw [perm.countP_eq] at eight
    simp only [isolated, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> contradiction

/-- Seven high-degree vertices do not suffice, for each prescribed number of leaves. -/
theorem seven_core_obstruction (l : Nat) :
    let d := universals 6 [5,5,3,3,3,3] l
    Graphic d ∧ d.sum + 2*d.count 1 = 4*d.length ∧ d.count 1=l ∧
      highCount d=7 ∧ ¬Planaric d := by
  dsimp only
  refine ⟨graphic_grow_apex ?_ l, ?_, ?_, ?_, (Graph.upper_universal_exceptions l).2.2⟩
  · exact ErdosGallai.sparse_graphic (a:=6) (b:=5) (t:=0) [5,3,3,3,3]
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp [universals, show 6+l≠1 by omega]; omega
  · simp [universals, show 6+l≠1 by omega]
  · simp [universals, highCount, List.countP_eq_length_filter, show 3≤6+l by omega]

/-- The companion has the same order, degree sum, maximum and leaf and
core counts as the seven-core obstruction, and has a planar realization. -/
theorem seven_core_companion (l : Nat) :
    let d := universals 6 [4,4,4,4,3,3] l
    d.sum + 2*d.count 1 = 4*d.length ∧ d.count 1=l ∧ highCount d=7 ∧ Planaric d := by
  dsimp only
  let h := [6+l,4,4,4,4,3,3]
  let d := universals 6 [4,4,4,4,3,3] l
  have ones : d.count 1=l := by
    simp [d,universals,show 6+l≠1 by omega]
  have vol : d.sum+2*l=4*d.length := by
    simp [d,universals]; omega
  refine ⟨by rw [ones]; exact vol, ones, ?_, ?_⟩
  · simp [universals, highCount, List.countP_eq_length_filter, show 3≤6+l by omega]
  · have graphic : Graphic d := by
      apply graphic_grow_apex _ l
      exact ErdosGallai.sparse_graphic (a:=6) (b:=4) (t:=0) [4,4,4,3,3]
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have core : Core h := by simp [h,Core,List.pairwise_cons]; omega
    have P : d.Perm (profile h 0 l) := List.Perm.rfl
    by_contra no
    have bad := (second_boundary d h 0 l (by simp [d,universals]) core P graphic vol).mp no
    simp [UpperForbidden,profile,h] at bad

/-- The two examples agree in order, degree sum, numbers of leaves, twos
and core entries, and have the same largest degree. -/
theorem seven_core_same_statistics (l : Nat) :
    let bad := universals 6 [5,5,3,3,3,3] l
    let good := universals 6 [4,4,4,4,3,3] l
    bad.length = good.length ∧ bad.sum = good.sum ∧
      bad.count 1 = good.count 1 ∧ bad.count 2 = good.count 2 ∧
      highCount bad = highCount good ∧
      (6+l ∈ bad ∧ ∀ x ∈ bad, x ≤ 6+l) ∧
      (6+l ∈ good ∧ ∀ x ∈ good, x ≤ 6+l) := by
  dsimp only
  have apexBound (s : List Nat) (cap : ∀ x ∈ s, x ≤ 6) :
      6+l ∈ universals 6 s l ∧ ∀ x ∈ universals 6 s l, x ≤ 6+l := by
    refine ⟨by simp [universals], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | mem
    · omega
    rcases List.mem_append.mp mem with mem | one
    · have := cap x mem; omega
    · have := List.eq_of_mem_replicate one; omega
  refine ⟨by simp [universals], by simp [universals]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp [universals, show 6+l ≠ 1 by omega]
  · simp [universals, show 6+l ≠ 2 by omega]
  · simp [universals, highCount, List.countP_eq_length_filter, show 3 ≤ 6+l by omega]
  · apply apexBound
    decide
  · apply apexBound
    decide

end SparseBoundary
