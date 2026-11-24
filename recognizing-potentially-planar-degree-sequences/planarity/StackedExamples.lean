import StackedHistory
import IntervalExamples

namespace Recognition.StackedExamples
open StackedQuota StackedHistory

private theorem disk_leaf (t : Disk) : t = .empty ∨ 3 ∈ t.degrees := by
  induction t with
  | empty => exact Or.inl rfl
  | split l m r hl hm hr =>
    right
    rcases hl with rfl|hl <;> rcases hm with rfl|hm <;> rcases hr with rfl|hr <;>
      simp_all [Disk.degrees,Disk.quota]

theorem cubic {ds : Multiset Nat} (s : SequentialRealization ds) : 3 ∈ ds := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := (acceptance_iff _).1 ((accepts_iff_sequential _).2 s)
  rw [shell_degrees]
  rcases disk_leaf a with rfl|ha
  · rcases disk_leaf b with rfl|hb
    · rcases disk_leaf c with rfl|hc
      · rcases disk_leaf d with rfl|hd
        · decide
        · simp [Shell.profile,hd]
      · simp [Shell.profile,hc]
    · simp [Shell.profile,hb]
  · simp [Shell.profile,ha]

theorem two_faces : SequentialRealization ([5,5,4,4,3,3] : List Nat) := by
  apply (accepts_iff_sequential _).1
  apply (acceptance_iff _).2
  let leaf : Disk := .split .empty .empty .empty
  exact ⟨⟨leaf,leaf,.empty,.empty⟩,by rw [shell_degrees]; rfl⟩

theorem octahedral :
    SparseBoundary.Planaric [4,4,4,4,4,4] ∧
    ¬ SequentialRealization ([4,4,4,4,4,4] : List Nat) := by
  refine ⟨RowRecognition.trace_planaric IntervalExamples.octahedron_trace,fun h => ?_⟩
  simpa using cubic h

end Recognition.StackedExamples
