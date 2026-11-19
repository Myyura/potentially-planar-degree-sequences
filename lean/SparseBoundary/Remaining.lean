import SparseBoundary.ExactSeven
import SparseBoundary.FanUpperHigh
namespace SparseBoundary

/-- The two exact leaf-free layers restricted to cores of order at least eight. -/
def LargeExact : Prop :=
  ∀ (h : List Nat) (t j : Nat), Core h → 8≤h.length → j≤1 →
    Graphic (profile h t 0) →
    (profile h t 0).sum+2*j=4*(profile h t 0).length → Planaric (profile h t 0)

theorem high_profile {h : List Nat} (min : ∀ x∈h,3≤x) (t l : Nat) :
    highCount (profile h t l)=h.length := by
  have eq : h.filter (fun x => decide (3≤x))=h := List.filter_eq_self.mpr (by simpa using min)
  simp [highCount,List.countP_eq_length_filter,profile,eq]

theorem large_not_exceptional {d : List Nat} (large : 8≤highCount d) : ¬Exceptional d := by
  rintro (h|h|⟨e,he,pm⟩|⟨e,he,pm⟩)
  · omega
  · omega
  · have p := pm.countP_eq (fun x => decide (3≤x))
    unfold highCount at large
    rw [p] at large
    simp [seeds] at he
    rcases he with rfl|rfl|rfl <;>
      simp [universals,List.countP_cons,List.countP_replicate, Nat.le_add_right_of_le (by decide : 3≤5),Nat.le_add_right_of_le (by decide : 3≤6)] at large
  · have p := pm.countP_eq (fun x => decide (3≤x))
    unfold highCount at large
    rw [p] at large
    simp [isolated] at he
    rcases he with rfl|rfl|rfl <;> simp [List.countP_cons] at large

theorem upper_from_large (hL : LargeExact) : SecondBoundaryStatement := by
  apply upper_iff_without_leaves.mpr
  intro d ne min hg sum no
  have pos (x) (hx : x∈d) : 1≤x := Nat.le_trans (by decide) (min x hx)
  have l0 : d.count 1=0 := List.count_eq_zero.mpr (fun e => by have := min 1 e; omega)
  by_cases small : highCount d≤7
  · exact (exact_at_most_seven (j:=0) (by decide) ne pos hg (by omega) small).mpr (by simpa [exactBad] using no)
  obtain ⟨h,t,core,p⟩ := normalize_positive d pos
  rw [l0] at p
  apply (planaric_perm p).mpr
  have big : 8≤h.length := by
    have eq := p.countP_eq (fun x => decide (3≤x))
    change highCount d=highCount (profile h t 0) at eq
    rw [high_profile core.2] at eq
    omega
  apply hL h t 0 core big (by decide) ((graphic_perm p).mp hg)
  simpa [p.sum_nat,p.length_eq] using sum

end SparseBoundary
