import SparseBoundary.GraphSixBoundary
import SparseBoundary.FiveSparse
import SparseBoundary.UpperLeaf

namespace SparseBoundary

/-- j=0 is the upper layer, j=1 the lower. -/
def exactBad (j : Nat) (d : List Nat) : Prop :=
  if j=0 then Exceptional d else d.Perm lowerException

private theorem bad_perm (j : Nat) {d e : List Nat} (p : d.Perm e) :
    exactBad j d ↔ exactBad j e := by
  by_cases eq : j=0
  · simp [exactBad,eq,exceptional_perm p]
  · simp [exactBad,eq]; exact ⟨p.symm.trans,p.trans⟩

/-- Leaf restoration preserves any prescribed upper bound on the number
    of high vertices. The leaf-free hypothesis is local to that range. -/
theorem exact_leaf_reduction (k j : Nat) (hj : j≤1)
    (base : ∀ d : List Nat, d≠[] → (∀ x∈d,2≤x) → Graphic d →
      d.sum+2*j=4*d.length → highCount d≤k → ¬exactBad j d → Planaric d)
    (d : List Nat) (ne : d≠[]) (pos : ∀ x∈d,1≤x) (hg : Graphic d)
    (sum : d.sum+2*j+2*d.count 1=4*d.length) (small : highCount d≤k)
    (no : ¬exactBad j d) : Planaric d := by
  by_cases one : 1∈d
  · by_cases big : ∃ y∈d,3≤y
    · let tail := d.erase 1
      have P : d.Perm (1::tail) := List.perm_cons_erase one
      obtain ⟨y,hy,hy3⟩ := big
      have hy' : y∈tail := (List.mem_cons.mp (P.mem_iff.mp hy)).resolve_left (by omega)
      have hn : tail≠[] := fun e => by rw [e] at hy'; contradiction
      let x := tail.max hn
      let L := tail.erase x
      have pm : d.Perm (1::x::L) := P.trans ((List.perm_cons_erase (List.max_mem hn)).cons 1)
      have hx : 3≤x := Nat.le_trans hy3 (List.le_max_of_mem hy')
      have hm (z) (hz : z∈L) : z≤x := List.le_max_of_mem (List.mem_of_mem_erase hz)
      have red := leaf_reduction_head x L ((graphic_perm pm).mp hg) (by omega) hm
      apply (planaric_perm pm).mpr
      by_cases exc : exactBad j ((x-1)::L)
      · by_cases zero : j=0
        · have five : 5≤x := by
            apply Classical.byContradiction; intro fail
            have upper := volume_if_small d (by
              intro z hz
              rcases List.mem_cons.mp (pm.mem_iff.mp hz) with rfl|hz; omega
              rcases List.mem_cons.mp hz with rfl|hz; omega
              have := hm _ hz; omega)
            have yes := List.count_pos_iff.mpr one
            omega
          have eq : x-1+1=x := by omega
          have res := upper_leaf_step (x:=x-1) (by omega) (by rwa [eq]) (by simpa [exactBad,zero] using exc)
          rw [eq] at res
          exact res.resolve_left (fun e => no ((bad_perm j pm).mpr (by simpa [exactBad,zero] using e)))
        · exact lower_exception_predecessor hx hm (by simpa [exactBad,zero] using exc)
      · apply red.2
        apply exact_leaf_reduction k j hj base ((x-1)::L) (by simp)
        · intro a ha; rcases List.mem_cons.mp ha with rfl|ha
          · omega
          · exact pos a (pm.mem_iff.mpr (by simp [ha]))
        · exact red.1
        · have cnt := pm.count_eq 1
          have len := pm.length_eq
          have sm := pm.sum_nat
          simp [show x≠1 by omega,show x-1≠1 by omega] at cnt len sm ⊢
          omega
        · have count := pm.countP_eq (fun x => decide (3≤x))
          unfold highCount at small ⊢
          rw [count] at small
          by_cases h3 : 3≤x-1 <;> simp_all <;> omega
        · exact exc
    · have nil (j : Nat) (hj : 3≤j) : d.filter (fun a => decide (j≤a))=[] := by
        apply List.filter_eq_nil_iff.mpr; intro y hy
        simp; have h : ¬ 3≤y := fun hh => big ⟨y,hy,hh⟩; omega
      exact planaric_of_small_core hg (by rw [nil 3 (by decide)]; decide)
        (by rw [nil 4 (by decide)]; decide)
  · apply base d ne (by intro x hx; have := pos x hx; have h : x≠1 := fun e => one (e ▸ hx); omega) hg _ small no
    simpa [List.count_eq_zero.mpr one] using sum
termination_by d.length
decreasing_by
  change ((x-1)::L).length < d.length
  rw [pm.length_eq]
  simp

private theorem small_base (j : Nat) (hj : j≤1) (d : List Nat) (_ne : d≠[])
    (min : ∀ x∈d,2≤x) (hg : Graphic d) (sum : d.sum+2*j=4*d.length)
    (few : highCount d≤6) (no : ¬exactBad j d) : Planaric d := by
  obtain ⟨h,t,core,pm⟩ := normalize_positive d (fun x hx => Nat.le_trans (by decide) (min x hx))
  have l0 : d.count 1=0 := List.count_eq_zero.mpr (fun h => by have := min 1 h; omega)
  rw [l0] at pm
  have gra := (graphic_perm pm).mp hg
  have cap : h.length≤6 := by
    have hi := pm.countP_eq (fun x => decide (3≤x))
    have filtereq : h.filter (fun x => decide (3≤x))=h := List.filter_eq_self.mpr (by simpa using core.2)
    simpa [highCount,hi,profile,List.countP_eq_length_filter,filtereq] using few
  rw [pm.sum_nat,pm.length_eq] at sum
  apply (planaric_perm pm).mpr
  by_cases top : j=0
  · have budget : (profile h t 0).sum=4*(profile h t 0).length := by simpa [top] using sum
    have nf : ¬ UpperForbidden h t 0 := fun e => no (by
      simpa [exactBad,top] using (exceptional_profile core pm).mpr e)
    by_cases six : h.length=6
    · exact (upper_six_classified core six gra budget).mpr nf
    have no5 : h.length≠5 := fun eq => nf (Or.inl eq)
    have small : h.length≤4 := by omega
    apply planaric_of_small_core gra <;> simp [profile] <;>
      exact Nat.le_trans (List.length_filter_le _ _) (by omega)
  · have one : j=1 := by omega
    have budget : (profile h t 0).sum+2=4*(profile h t 0).length := by simpa [one] using sum
    by_cases six : h.length=6
    · exact lower_six_classified core six gra budget
    apply (lower_sparse_at_most_five core (by omega) gra (Nat.le_of_eq budget)).mpr
    intro he
    exact no (by simpa [exactBad,top,he] using pm)

theorem exact_at_most_six {d : List Nat} {j : Nat} (hj : j≤1)
    (ne : d≠[]) (pos : ∀ x∈d,1≤x) (hg : Graphic d)
    (sum : d.sum+2*j+2*d.count 1=4*d.length) (few : highCount d≤6) :
    Planaric d ↔ ¬exactBad j d := by
  refine ⟨?_,exact_leaf_reduction 6 j hj (small_base j hj) d ne pos hg sum few⟩
  intro hp
  by_cases zero : j=0
  · obtain ⟨h,t,core,pm⟩ := normalize_positive d pos
    intro bad
    exact upper_obstructions_nonplanar pm (by simpa [zero] using sum)
      ((exceptional_profile core pm).mp (by simpa [exactBad,zero] using bad)) hp
  · simpa [exactBad,zero] using lower_necessary hp

end SparseBoundary
