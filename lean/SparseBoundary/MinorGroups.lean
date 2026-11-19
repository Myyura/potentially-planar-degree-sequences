import SparseBoundary.MinorBits

namespace SparseBoundary.MinorSearch

open Graph

/-- A sorted search uses each ordering of equal-role branch sets just once.
    Its two domains are held as bit fields indexed by vertex masks. -/
def groupedSearch (R : Bool → Bool → Bool) (t : CompatTable) :
    List Bool → Nat → Nat → Bool
  | [], _, _ => true
  | c :: cs, l, r =>
    let v := if c then r else l
    visitBits (fun m =>
      let l' := l &&& rowFor t m (R c false)
      let r' := r &&& rowFor t m (R c true)
      if c then groupedSearch R t cs l' (r' % (2^(m+1)))
      else groupedSearch R t cs (l' % (2^(m+1))) r')
      (v.log2+1) v

private theorem sortedOrder {α} (s : List α) (weight : α → Nat) :
    ∃ u : List α, u.Perm s ∧ u.Pairwise (fun i j => weight j ≤ weight i) := by
  let cmp := fun i j => decide (weight j ≤ weight i)
  refine ⟨s.mergeSort cmp,List.mergeSort_perm ..,?_⟩
  have tr : ∀ a b c, cmp a b = true → cmp b c = true → cmp a c = true := by
    simp only [cmp,decide_eq_true_eq]; omega
  have tot : ∀ a b, (cmp a b || cmp b a) = true := by
    simp only [cmp,decide_eq_true_eq,Bool.or_eq_true]; omega
  simpa [cmp] using List.pairwise_mergeSort tr tot s

theorem forbidden_of_groups {n k : Nat} (g : Graph n)
    (color : Fin k → Bool) (R : Bool → Bool → Bool)
    (cat : Array (Option Nat)) (initial : Nat) (t : CompatTable)
    (left right : List (Fin k)) (ho : (left ++ right).Nodup)
    (hl : ∀ x ∈ left, color x = false) (hr : ∀ x ∈ right, color x = true)
    (hc : covers g cat = true) (ht : validTable cat initial t = true)
    (hn : groupedSearch R t (List.replicate left.length false ++ List.replicate right.length true)
      initial initial = false) :
    ¬ ∃ bags, g.minorTest (fun i j => i != j && R (color i) (color j)) bags = true := by
  rintro ⟨bags, h⟩
  let w := fun i => (encode g (bags i)).verts
  have rr i := List.all_eq_true.mp h i (List.mem_finRange i)
  simp only [Bool.and_eq_true] at rr
  have hin i := in_pool (covered hc _ (rr i).1)
  have rrow i := List.all_eq_true.mp ht _ (hin i)
  simp only [Bool.and_eq_true] at rrow
  have complete : ∀ (is : List (Fin k)), is.Nodup →
      is.Pairwise (fun i j => color i = color j → w j ≤ w i) → ∀ l r,
      (∀ i ∈ is, (if color i then r else l).testBit (w i) = true) →
      groupedSearch R t (is.map color) l r = true := by
    intro is
    induction is with
    | nil => intros; rfl
    | cons i is ih =>
      intro hnod hp l r hm
      have nd := List.nodup_cons.mp hnod
      have pw := List.pairwise_cons.mp hp
      simp only [List.map_cons,groupedSearch]
      apply visit_complete (m:=w i) _ _ _ Nat.lt_log2_self (hm i (List.mem_cons_self ..))
      have full (j) (hj : j ∈ is) :
          (rowFor t (w i) (R (color i) (color j))).testBit (w j) = true := by
        have tj := List.all_eq_true.mp (rrow i).2 _ (hin j)
        simp only [Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at tj
        have cell := List.all_eq_true.mp (rr i).2 j (List.mem_finRange j)
        have ne : i ≠ j := by rintro rfl; exact nd.1 hj
        simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at cell
        have hd := distinct_of (g:=g) (cell.1.resolve_left ne)
        simp only [bne_iff_ne.mpr ne,Bool.true_and] at cell
        cases he : R (color i) (color j) with
        | false => exact tj.1.resolve_left (by simp [hd])
        | true =>
          have hh := touch_of (g:=g) (cell.2.resolve_left (by simp [he]))
          exact tj.2.resolve_left (by simp [compat,hd,hh])
      cases ci : color i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
        apply ih nd.2 pw.2 <;> intro j hj <;>
        have hjm := hm j (List.mem_cons_of_mem _ hj) <;>
        have hrow := full j hj <;>
        have hjw := pw.1 j hj <;> cases cj : color j <;>
        simp [ci,cj,Nat.testBit_and,Nat.testBit_mod_two_pow] at hjw hjm hrow ⊢ <;> simp [hjm,hrow] <;> omega
  obtain ⟨ls,pl,sl⟩ := sortedOrder left w
  obtain ⟨rs,pr,sr⟩ := sortedOrder right w
  have lp i (hi : i ∈ ls) := hl i (pl.mem_iff.mp hi)
  have rp i (hi : i ∈ rs) := hr i (pr.mem_iff.mp hi)
  have lmap : ls.map color = List.replicate left.length false := by
    rw [← pl.length_eq,← List.length_map (f:=color) (as:=ls)]
    apply List.eq_replicate_of_mem
    simpa [List.mem_map] using lp
  have rmap : rs.map color = List.replicate right.length true := by
    rw [← pr.length_eq,← List.length_map (f:=color) (as:=rs)]
    apply List.eq_replicate_of_mem
    simpa [List.mem_map] using rp
  have hh := complete (ls++rs) ((pl.append pr).nodup_iff.mpr ho)
    (List.pairwise_append.mpr ⟨sl.imp (S:=fun i j => color i = color j → w j ≤ w i) (fun h _ => h),
      sr.imp (S:=fun i j => color i = color j → w j ≤ w i) (fun h _ => h),
      fun i hi j hj h => by simp [lp i hi,rp j hj] at h⟩)
    initial initial (fun i _ => by simpa using (rrow i).1)
  simp [List.map_append,lmap,rmap,hn] at hh
/-- The eleven named branch positions reduce to a clique and two
    interchangeable triples. -/
theorem planar_of_groups {n : Nat} (g : Graph n) (cat : Array (Option Nat))
    (initial : Nat) (t : CompatTable) (hc : covers g cat = true)
    (ht : validTable cat initial t = true)
    (hk : groupedSearch (fun _ _ => true) t (List.replicate 5 false) initial initial = false)
    (hb : groupedSearch (fun i j => i != j) t
      (List.replicate 3 false ++ List.replicate 3 true) initial initial = false) :
    g.Planar := by
  constructor
  · have hh := forbidden_of_groups g (fun _ : Fin 5 => false) (fun _ _ => true)
      cat initial t [0,1,2,3,4] [] (by decide) (by decide) (by decide) hc ht hk
    have heq : (fun i j : Fin 5 => i != j && true) = clique5 := by
      funext i j; simp [clique5]
    rwa [heq] at hh
  · let color := fun i : Fin 6 => decide (i.val ≥ 3)
    have hh := forbidden_of_groups g color (fun a b => a != b)
      cat initial t [0,1,2] [3,4,5] (by decide) (by decide) (by decide) hc ht hb
    have heq : (fun i j => i != j && (color i != color j)) = biclique33 := by
      funext i j
      have h : ∀ i j : Fin 6, (i != j && (color i != color j)) = biclique33 i j := by decide
      apply h
    rwa [heq] at hh

end SparseBoundary.MinorSearch
