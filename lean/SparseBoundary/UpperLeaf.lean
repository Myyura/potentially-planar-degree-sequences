import SparseBoundary.UpperLists
import SparseBoundary.LowerInduction
import SparseBoundary.LeafRepairs

namespace SparseBoundary

private def baseExceptions := seeds.map (fun e => e.1::e.2) ++ isolated
private def repairs : List (List Nat) :=
  [[1,5,5,4,4,4,3],[1,6,5,5,5,5,3,2,2],[1,5,4,4,4,4,4,4],
   [1,6,6,5,3,3,3,3],[1,7,6,6,3,3,3,3,2]]
private def nextExceptions := seeds.map (fun e => universals e.1 e.2 1) ++ repairs

private theorem next_count {e : Nat × List Nat} (he : e∈seeds) (k : Nat) :
    (universals e.1 e.2 k).count 1 = k := by
  simp [seeds] at he
  rcases he with rfl|rfl|rfl <;> simp [universals,show 5+k≠1 by omega,show 6+k≠1 by omega]

private theorem finite_step {x : Nat} {L b : List Nat} (max : ∀ y∈L,y≤x+1)
    (p : (x::L).Perm b) (mem : b∈baseExceptions) :
    Exceptional (1::(x+1)::L) ∨ Planaric (1::(x+1)::L) := by
  have ok : baseExceptions.all (fun b => b.all fun x =>
      !(b.all (fun v => decide (v≤x+1))) ||
        nextExceptions.any (fun e => ((1::(x+1)::b.erase x).isPerm e))) = true := by decide
  have H := List.all_eq_true.mp (List.all_eq_true.mp ok b mem) x (p.mem_iff.mp (by simp))
  have cap : b.all (fun v => decide (v≤x+1))=true := by
    apply List.all_eq_true.mpr
    intro y hy
    rcases List.mem_cons.mp (p.mem_iff.mpr hy) with rfl|h
    · simp
    · simpa using max y h
  simp only [cap,Bool.not_true,Bool.false_or] at H
  obtain ⟨e,he,pe⟩ := List.any_eq_true.mp H
  have P : (1::(x+1)::L).Perm e :=
    (((List.cons_perm_iff_perm_erase.mp p).2.cons (x+1)).cons 1).trans (List.isPerm_iff.mp pe)
  rcases List.mem_append.mp he with hs|hr
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hs
    apply Or.inl
    apply Or.inr; apply Or.inr; apply Or.inl
    refine ⟨v,hv,?_⟩
    have hc := (P.count_eq 1).trans (next_count hv 1)
    rw [hc]
    exact P
  · exact Or.inr ((planaric_perm P).mpr (leaf_predecessor_repaired hr))

private theorem universal_step {x k : Nat} {L : List Nat} {e : Nat × List Nat}
    (hs : e∈seeds) (p : (x::L).Perm (universals e.1 e.2 k))
    (max : ∀ y∈L,y≤x+1) : Exceptional (1::(x+1)::L) ∨ Planaric (1::(x+1)::L) := by
  cases k with
  | zero =>
    apply finite_step max (b:=e.1::e.2) (by simpa [universals] using p)
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e,hs,rfl⟩)
  | succ k =>
    have seed : 2≤e.1 ∧ ∀ z∈e.2, z<e.1 := by
      simp [seeds] at hs
      rcases hs with rfl|rfl|rfl <;> decide
    let top := e.1 + (k+1)
    have topmem : top∈x::L := p.mem_iff.mpr (List.mem_cons_self ..)
    have le : top≤x+1 := by rcases List.mem_cons.mp topmem with rfl|h; omega; exact max _ h
    have hx : x=top := by
      have hx := p.mem_iff.mp (List.mem_cons_self (a:=x) (l:=L))
      rcases List.mem_cons.mp hx with eq|other
      · exact eq
      · rcases List.mem_append.mp other with h|h
        · have := seed.2 _ h; dsimp [top] at le; omega
        · have := List.eq_of_mem_replicate h; dsimp [top] at le; omega
    subst x
    have tail : L.Perm (e.2++List.replicate (k+1) 1) := p.cons_inv
    have P : (1::(top+1)::L).Perm (universals e.1 e.2 (k+2)) := by
      have perm := (List.Perm.swap (top+1) 1 L).trans ((tail.cons 1).cons (top+1))
      have mv := (List.perm_middle (a:=1) (l₁:=e.2) (l₂:=List.replicate (k+1) 1)).symm
      exact perm.trans (mv.cons (top+1))
    apply Or.inl; apply Or.inr; apply Or.inr; apply Or.inl
    refine ⟨e,hs,?_⟩
    rw [(P.count_eq 1).trans (next_count hs (k+2))]
    exact P

/-- All possible successors of a nonplanaric exception under the inverse
    of the maximum-degree leaf deletion are accounted for. -/
theorem upper_leaf_step {x : Nat} {L : List Nat} (hi : 4≤x) (max : ∀ y∈L,y≤x+1)
    (bad : Exceptional (x::L)) : Exceptional (1::(x+1)::L) ∨ Planaric (1::(x+1)::L) := by
  have hx : 3≤x := by omega
  have h1 : 3≤x+1 := by omega
  have h2 : x≠3 := by omega
  have h3 : x+1≠3 := by omega
  rcases bad with five|six|univ|isol
  · exact Or.inl (Or.inl (by simpa [highCount,List.countP_cons,hx,h1] using five))
  · apply Or.inl; apply Or.inr; apply Or.inl
    simpa [highCount,List.countP_cons,List.count_cons,hx,h1,h2,h3] using six
  · obtain ⟨e,hs,p⟩ := univ
    exact universal_step hs p max
  · obtain ⟨e,hs,p⟩ := isol
    exact finite_step max p (List.mem_append_right _ hs)

/-- Leaf-free sufficiency on the upper boundary, in arbitrary label order. -/
def SecondWithoutLeaves : Prop :=
  ∀ d : List Nat, d≠[] → (∀ x∈d,2≤x) → Graphic d → d.sum=4*d.length →
    ¬ Exceptional d → Planaric d

theorem volume_if_small (d : List Nat) (small : ∀ x∈d, x≤4) :
    d.sum+3*d.count 1≤4*d.length := by
  induction d with
  | nil => decide
  | cons a d ih =>
    have ha := small a (by simp)
    have h := ih fun y hy => small y (by simp [hy])
    by_cases one : a=1 <;> simp [one] <;> omega

private theorem upper_from_base (base : SecondWithoutLeaves) (d : List Nat) (ne : d≠[])
    (pos : ∀ x∈d,1≤x) (hg : Graphic d) (sum : d.sum+2*d.count 1=4*d.length)
    (no : ¬ Exceptional d) : Planaric d := by
  by_cases one : 1∈d
  · have big : ∃ y∈d,5≤y := by
      apply Classical.byContradiction; intro fail
      have small := volume_if_small d (by intro y hy; have na : ¬ 5≤y := fun h => fail ⟨y,hy,h⟩; omega)
      have yes := List.count_pos_iff.mpr one
      omega
    let tail := d.erase 1
    have P : d.Perm (1::tail) := List.perm_cons_erase one
    obtain ⟨y,hy,hy5⟩ := big
    have hy' : y∈tail := (List.mem_cons.mp (P.mem_iff.mp hy)).resolve_left (by omega)
    have hn : tail≠[] := fun e => by rw [e] at hy'; contradiction
    let x := tail.max hn
    let L := tail.erase x
    have P' : d.Perm (1::x::L) := P.trans ((List.perm_cons_erase (List.max_mem hn)).cons 1)
    have h5 : 5≤x := Nat.le_trans hy5 (List.le_max_of_mem hy')
    have hm (z) (hz : z∈L) : z≤x := List.le_max_of_mem (List.mem_of_mem_erase hz)
    have red := leaf_reduction_head x L ((graphic_perm P').mp hg) (by omega) hm
    apply (planaric_perm P').mpr
    by_cases exc : Exceptional ((x-1)::L)
    · have eq : x-1+1=x := by omega
      have result := upper_leaf_step (x:=x-1) (by omega) (by rwa [eq]) exc
      rw [eq] at result
      exact result.resolve_left (fun e => no ((exceptional_perm P').mpr e))
    · apply red.2
      apply upper_from_base base ((x-1)::L) (by simp)
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
  · apply base d ne (by intro x hx; have := pos x hx; have h : x≠1 := fun e => one (e ▸ hx); omega) hg _ no
    simpa [List.count_eq_zero.mpr one] using sum
termination_by d.length
decreasing_by
  change ((x-1)::L).length < d.length
  rw [P'.length_eq]
  simp

/-- The full upper boundary is equivalent to sufficiency on the leaf-free
    boundary. The necessity direction and every leaf attachment are closed. -/
theorem upper_iff_without_leaves : SecondBoundaryStatement ↔ SecondWithoutLeaves := by
  constructor
  · intro main d ne min hg sum no
    have pos (x) (hx : x∈d) : 1≤x := Nat.le_trans (by decide) (min x hx)
    obtain ⟨h,t,core,pm⟩ := normalize_positive d pos
    have l0 : d.count 1=0 := List.count_eq_zero.mpr (fun w => by have := min 1 w; omega)
    have bounded := main d h t (d.count 1) ne core pm hg (by omega)
    apply Classical.byContradiction
    exact fun non => no ((exceptional_profile core pm).mpr (bounded.mp non))
  · intro base d h t l ne core pm hg sum
    constructor
    · intro non
      apply Classical.byContradiction
      intro outside
      have hc : 1∉h := fun e => by have := core.2 1 e; omega
      have leaves := pm.count_eq 1
      simp [profile,List.count_replicate,List.count_eq_zero.mpr hc] at leaves
      have pos (a) (ha : a∈d) : 1≤a := by
        have hx := pm.mem_iff.mp ha
        rcases List.mem_append.mp hx with hh|hl
        · have := core.2 a hh; omega
        · rcases List.mem_append.mp hl with h|h <;> have := List.eq_of_mem_replicate h <;> omega
      exact non (upper_from_base base d ne pos hg (by omega) (fun e => outside ((exceptional_profile core pm).mp e)))
    · exact upper_obstructions_nonplanar pm sum

end SparseBoundary
