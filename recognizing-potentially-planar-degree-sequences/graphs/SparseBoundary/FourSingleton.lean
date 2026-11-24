import SparseBoundary.FanPromote
import SparseBoundary.GraphFourReduction

namespace SparseBoundary.FourCore
open Graph

private theorem promote_twice {a t : Nat} (rs : List Nat)
    (hp : Planaric (a::(rs++List.replicate t 2))) (high : rs.length<a) :
    Planaric (2::4::(a+2)::(rs++List.replicate t 2)) := by
  let xs := rs++List.replicate t 2
  obtain ⟨G,hd,hp⟩ := hp
  obtain ⟨i,loc,edge⟩ := Fan.exists_two_neighbor rs hd high
  have hi : xs[i.val]'(i.isLt)=2 := by dsimp [xs]; rw [List.getElem_append_right loc]; simp
  let es := List.replicate 2 ((0 : Fin (a::xs).length),i.succ)
  let Y := xs.set i.val 4
  have plan := expanded_planaric hp es (by intro e he; exact List.eq_of_mem_replicate he ▸ edge)
  have row : List.ofFn (fun v => G.degree v+increments es v)=(a+2)::Y := by
    rw [List.ofFn_succ]
    congr 1
    · have root : G.degree 0=a := hd 0
      simp [root,es,increments,pairRow]
    · apply List.ext_getElem
      · simp [Y,xs]
      · intro j hj hy
        have jlt : j<xs.length := by simpa [Y] using hy
        let v : Fin xs.length := ⟨j,jlt⟩
        have dg : G.degree v.succ=xs[j] := hd v.succ
        simp only [List.getElem_ofFn]
        change G.degree v.succ+increments es v.succ=Y[j]'(hy)
        by_cases eq : v=i
        · have e : j=i.val := congrArg Fin.val eq
          subst j
          simp [es,increments,pairRow,eq,Y,Fin.succ_ne_zero]
          exact (hd i.succ).trans hi
        · have ne : i.val≠j := fun e => eq (Fin.ext e.symm)
          simp [es,increments,pairRow,Y,dg,Fin.succ_ne_zero,List.getElem_set_ne ne,eq]
  rw [row] at plan
  change Planaric (2::2::(a+2)::Y) at plan
  apply (planaric_perm (d:=2::2::(a+2)::Y) (e:=2::4::(a+2)::xs) _).mp plan
  apply List.perm_iff_count.mpr; intro v
  have occurs : 0<xs.count 2 := List.count_pos_iff.mpr (hi ▸ List.getElem_mem i.isLt)
  have ixs : i.val<xs.length := i.isLt
  simp only [Y,List.count_cons,List.count_set ixs,hi,beq_iff_eq]
  have occ : 2=v → 0<xs.count v := fun e => e ▸ occurs
  by_cases e : 2=v <;> by_cases f : 4=v <;> simp (disch := omega) only [ite_eq_left,ite_eq_right] <;> omega

private theorem cost_lower (xs : List Nat) (lo : ∀ x∈xs,4≤x) :
    5*xs.length≤xs.sum+xs.count 4 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have := lo x (by simp)
    have := ih (fun y hy=>lo y (by simp [hy]))
    by_cases e : x=4 <;> simp [e] <;> omega

private theorem high_case (a : Nat) (u : List Nat) (t : Nat) (size : 8≤(a::u).length)
    (budget : 2≤t) (single : (a::u).count 4=1) (inp : Input (a::u) t)
    (hi : (a::u).length<a) (away : ∀x∈a::u,x+2<(a::u).length+t) :
    Planaric (List.replicate t 2++a::u) := by
  have not4 : a≠4 := by omega
  have count : u.count 4=1 := by simpa [not4] using single
  have mem : 4∈u := List.count_pos_iff.mp (by omega)
  let r := u.erase 4
  have pm : u.Perm (4::r) := List.perm_cons_erase mem
  have len := pm.length_eq
  have sm := pm.sum_nat
  have cnt := pm.count_eq 4
  have vol := inp.2.2.1
  simp only [List.length_cons,List.sum_cons,List.count_cons_self] at len sm size hi cnt vol
  have l5 (x) (hx : x∈r) : 5≤x := by
    have l := inp.2.1 x (List.mem_cons_of_mem _ (List.mem_of_mem_erase hx))
    by_cases e : x=4
    · subst x; have := List.count_pos_iff.mpr hx; omega
    · omega
  let rest := (a-2)::r
  let descending := fun x y : Nat => decide (x≥y)
  let sorted := rest.mergeSort descending
  have ps : sorted.Perm rest := List.mergeSort_perm ..
  have hsort : sorted.Pairwise (·≥·) := by
    simpa [descending,sorted] using List.pairwise_mergeSort (le:=descending) (by simp [descending]; omega) (by simp [descending]; omega) rest
  have input : Fan.UpperHigh sorted (t-1) := by
    refine ⟨hsort,?_,?_,?_⟩
    · intro x hx
      rcases List.mem_cons.mp (ps.mem_iff.mp hx) with rfl|hx
      · omega
      · exact l5 x hx
    · rw [ps.sum_nat,ps.length_eq]
      simp [rest]; omega
    · intro x hx
      rw [ps.length_eq]
      have ax := away a (by simp)
      rcases List.mem_cons.mp (ps.mem_iff.mp hx) with rfl|hx
      · simp [rest] at ax ⊢; omega
      · have above := away x (List.mem_cons_of_mem _ (List.mem_of_mem_erase hx))
        simp [rest] at above ⊢; omega
  have hp := Fan.upper_min_five sorted (t-1) (by rw [ps.length_eq]; simp [rest]; omega) input
  have hp' := (planaric_perm ((ps.append_left _).trans List.perm_append_comm)).mp hp
  have q := promote_twice (a:=a-2) r (by simpa [rest] using hp') (by omega)
  have e : a-2+2=a := by omega
  rw [e] at q
  apply (planaric_perm (d:=2::4::a::(r++List.replicate (t-1) 2)) _).mp q
  apply List.perm_iff_count.mpr; intro x
  have ct := pm.count_eq x
  simp only [List.count_append,List.count_cons,List.count_replicate,beq_iff_eq] at ct ⊢
  by_cases k : 2=x <;> simp [k] <;> omega

/-- The upper boundary with exactly one four is constructive at every
core order at least six and every available budget of at least two. -/
theorem single_four {h : List Nat} {t : Nat} (hn : 6≤h.length) (budget : 2≤t)
    (single : h.count 4=1) (input : Input h t) : Planaric (List.replicate t 2++h) := by
  generalize hlen : h.length=n at *
  induction n using Nat.strongRecOn generalizing h t with
  | ind n ih =>
    by_cases small : n≤7
    · exact upper_small ⟨by omega,by omega⟩ budget input
    have big : 8≤h.length := by omega
    by_cases top : ∃x∈h,h.length+t≤x+2
    · exact near big input top
    have away (x) (hx : x∈h) : x+2<h.length+t := by
      apply Nat.lt_of_not_ge; exact fun bad => top ⟨x,hx,bad⟩
    match h with
    | [] => simp at big
    | a::u =>
      by_cases high : (a::u).length<a
      · exact high_case a u t big budget single input high away
      have max (x) (hx : x∈a::u) : x≤n := by
        rcases List.mem_cons.mp hx with rfl|hx
        · omega
        · have := List.rel_of_pairwise_cons input.1 hx; omega
      have dup : ∃ g,2≤(a::u).count g := by
        apply Classical.byContradiction; intro no
        have nod : (a::u).Nodup := List.nodup_iff_count.mpr (fun x => by
          have neg : ¬2≤(a::u).count x := fun v => no ⟨x,v⟩; omega)
        have sub : a::u ⊆ List.range' 4 (n-3) := by
          intro x hx
          have := input.2.1 x hx
          have := max x hx
          simp only [List.mem_range',Nat.one_mul]; exact ⟨x-4,by omega,by omega⟩
        have := nod.length_le_of_subset sub
        simp only [List.length_range'] at this; omega
      obtain ⟨g,two⟩ := dup
      obtain ⟨r,sub,pm⟩ := erase_copies (a::u) g 2 two
      have ln := pm.length_eq
      have sm := pm.sum_nat
      have cnt := pm.count_eq 4
      have vol := input.2.2.1
      have g4 : g≠4 := by rintro rfl; omega
      have gl := input.2.1 g (List.count_pos_iff.mp (by omega))
      have lo (x) (hx : x∈r) := input.2.1 x (sub.subset hx)
      have rl := cost_lower r lo
      simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
        List.length_cons,List.sum_cons,List.count_cons] at ln sm cnt
      have rc : r.count 4=1 := by
        have cc := pm.count_eq 4
        simp [g4] at cc
        omega
      simp only [List.sum_cons,List.length_cons] at vol hlen big
      let s := t+4-g
      have sb : 2≤s := by dsimp only [s]; omega
      have back : s+g-4=t := by dsimp [s]; omega
      have rin : Input r s := by
        refine ⟨input.1.sublist sub,lo,?_,?_⟩
        · dsimp only [s]; omega
        · intro x hx; have := max x (sub.subset hx)
          dsimp only [s]; omega
      have pl := ih r.length (by omega) (h:=r) (t:=s) sb rc rin rfl (by omega)
      have pair := restore_equal_pair sb (by omega : 3≤g) pl
      rw [back] at pair
      exact (planaric_perm (pm.append_left _)).mpr pair

/-- Positive budget, large upper cores of minimum four. -/
theorem upper_fours {h : List Nat} {t : Nat} (size : 8≤h.length) (budget : 2≤t)
    (inp : Input h t) : Planaric (List.replicate t 2++h) :=
  upper_of_single_four size budget inp (fun _ h _ c _ i => single_four (by omega) budget c i)

end SparseBoundary.FourCore
