import SparseBoundary.Boundary
import SparseBoundary.BranchDegree
import SparseBoundary.LeafReduction
import SparseBoundary.FanPlanar

namespace SparseBoundary

theorem leaf_reduction_head (x : Nat) (l : List Nat)
    (hg : Graphic (1 :: x :: l)) (positive : 1≤x) (maximum : ∀ y∈l,y≤x) :
    Graphic ((x-1)::l) ∧ (Planaric ((x-1)::l) → Planaric (1::x::l)) := by
  have h := leaf_reduction (d:=x::l) 0 hg (by
    intro i; refine Fin.cases (Nat.le_refl _) (fun j => ?_) i
    exact maximum _ (List.getElem_mem (n:=j.val) j.isLt)) positive
  have e : List.ofFn (fun i : Fin (x::l).length => (x::l)[i] - (if i=0 then 1 else 0)) =
      (x-1)::l := by
    rw [List.ofFn_succ]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hi'; simp [Fin.ne_of_gt (Fin.succ_pos _)]
  rwa [e] at h

private def lowerRepairBase : Graph 6 :=
  Graph.ofRelation (fun i j => decide (i ≠ j ∧
    (i.val=0 ∨ j.val=0 ∨ (i.val=1 ∧ 3≤j.val) ∨ (j.val=1 ∧ 3≤i.val) ∨
     (2≤i.val ∧ 2≤j.val ∧ i.val≤j.val+1 ∧ j.val≤i.val+1))))

/-- The unique possible predecessor of the lower exception is repaired by
    an explicit six-vertex two-apex path support and one pendant edge. -/
theorem lower_repair : Planaric [1,5,4,4,4,4,2] := by
  have h : Planaric [5,4,2,4,4,3] := ⟨lowerRepairBase,by unfold Graph.Realizes; decide,
    Fan.two_apex_path_planar (by unfold Fan.TwoApexPath; decide)⟩
  have h' := planaric_attach_leaf h (5 : Fin 6)
  exact (planaric_perm (d:=[1,5,4,2,4,4,4]) (e:=[1,5,4,4,4,4,2]) (by decide)).mp h'

/-- Leaf-free form of Theorem 3.2, including the previously published
    strictly sparser range. -/
def FirstWithoutLeaves : Prop :=
  ∀ d : List Nat, d≠[] → (∀ x∈d, 2≤x) → Graphic d → d.sum+2≤4*d.length →
    ¬ d.Perm lowerException → Planaric d

theorem lower_exception_predecessor {x : Nat} {L : List Nat} (hi : 3≤x) (hm : ∀ y∈L, y≤x)
    (res : ((x-1)::L).Perm lowerException) : Planaric (1::x::L) := by
  have hin : x-1 ∈ lowerException := res.mem_iff.mp (List.mem_cons_self ..)
  have h4 : 4∈(x-1)::L := res.mem_iff.mpr (by decide)
  simp [lowerException] at hin
  have hx : x=5 := by
    rcases List.mem_cons.mp h4 with h|h
    · omega
    · have he := hm 4 h; omega
  subst x
  have hL : L.Perm [4,4,4,4,2] := res.cons_inv
  exact (planaric_perm ((hL.cons 5).cons 1)).mpr lower_repair

/-- Every lower-boundary case with leaves reduces to the leaf-free theorem.
    This equivalence includes the strict inequality and proves all
    intermediate sequences stay in the correct positive domain. -/
theorem lower_iff_without_leaves : FirstBoundaryStatement ↔ FirstWithoutLeaves := by
  constructor
  · intro first d ne pos hg bound no
    have h1 : 1∉d := fun h => (by have := pos 1 h; omega)
    have hc : d.count 1=0 := List.count_eq_zero.mpr h1
    apply (first d ne (fun x hx => Nat.le_trans (by decide) (pos x hx)) hg (by omega)).mpr no
  · intro base
    let rec good (d : List Nat) (ne : d≠[]) (pos : ∀ x∈d,1≤x) (hg : Graphic d)
        (bound : d.sum+2+2*d.count 1≤4*d.length) (no : ¬ d.Perm lowerException) : Planaric d := by
      by_cases one : 1∈d
      · by_cases big : ∃ y∈d,3≤y
        · let tail := d.erase 1
          have P : d.Perm (1::tail) := List.perm_cons_erase one
          obtain ⟨y,hy,hy3⟩ := big
          have hy' : y∈tail := (List.mem_cons.mp (P.mem_iff.mp hy)).resolve_left (by omega)
          have hn : tail≠[] := fun e => by rw [e] at hy'; contradiction
          let x := tail.max hn
          let L := tail.erase x
          have P' : d.Perm (1::x::L) := P.trans ((List.perm_cons_erase (List.max_mem hn)).cons 1)
          have h3 : 3≤x := Nat.le_trans hy3 (List.le_max_of_mem hy')
          have hm (z) (hz : z∈L) : z≤x := List.le_max_of_mem (List.mem_of_mem_erase hz)
          have red := leaf_reduction_head x L ((graphic_perm P').mp hg) (by omega) hm
          apply (planaric_perm P').mpr
          by_cases exc : ((x-1)::L).Perm lowerException
          · exact lower_exception_predecessor h3 hm exc
          · apply red.2
            apply good ((x-1)::L) (by simp)
            · intro a ha; rcases List.mem_cons.mp ha with rfl|ha
              · omega
              · exact pos a (P'.mem_iff.mpr (by simp [ha]))
            · exact red.1
            · have cnt := P'.count_eq 1
              have len := P'.length_eq
              have sm := P'.sum_nat
              simp [show x≠1 by omega,show x-1≠1 by omega] at cnt len sm ⊢
              omega
            · exact exc
        · have nil (j : Nat) (hj : 3≤j) : d.filter (fun a => decide (j≤a))=[] := by
            apply List.filter_eq_nil_iff.mpr; intro y hy
            simp; have h : ¬ 3≤y := fun hh => big ⟨y,hy,hh⟩; omega
          exact planaric_of_small_core hg (by rw [nil 3 (by decide)]; decide)
            (by rw [nil 4 (by decide)]; decide)
      · exact base d ne (by intro x hx; have := pos x hx; have hg : x≠1 := fun e => one (e ▸ hx); omega)
          hg (by omega) no
      termination_by d.length
      decreasing_by
        change ((x-1)::L).length < d.length
        rw [P'.length_eq]
        simp
    exact fun d ne pos hg bound => ⟨lower_necessary,good d ne pos hg bound⟩

end SparseBoundary
