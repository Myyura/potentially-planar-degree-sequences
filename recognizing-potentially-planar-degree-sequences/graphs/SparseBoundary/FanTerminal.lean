import SparseBoundary.FanCone
import SparseBoundary.FanRealization

namespace SparseBoundary.Fan

open Graph

private def rimBase (q i : Nat) : Nat := 2+(if 0<i then 1 else 0)+
  (if i+1<q then 1 else 0)+(if 1≤i ∧ i<4 then 1 else 0)

private theorem rim_sum (q : Nat) (hq : 4≤q) :
    ((List.range q).map (rimBase q)).sum=4*q+1 := by
  have boost (k : Nat) :
      ((List.range (k+4)).map (fun i => if 1≤i ∧ i<4 then 1 else 0)).sum=3 := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+4=k+4+1 by omega,List.range_succ,List.map_append,List.sum_append,ih]
      simp [show ¬k+4<4 by omega]
  have plus := boost (q-4)
  rw [Nat.sub_add_cancel hq] at plus
  change ((List.range q).map (fun i => 2+(if 0<i then 1 else 0)+
    (if i+1<q then 1 else 0)+(if 1≤i ∧ i<4 then 1 else 0))).sum=_
  have conv (i : Nat) : i+1<q ↔ i<q-1 := by omega
  simp only [conv,show ∀i : Nat, 0<i ↔ 1≤i by omega]
  repeat' rw [sum_maps]
  rw [(indicators q 1).1,(indicators q (q-1)).2,plus]
  simp [List.map_const',List.sum_replicate_nat]; omega

private theorem erase_degree {q : Nat} (H : Graph q) (a b i : Fin q) (e : H.adj a b=true) :
    (H.eraseEdge a b).degree i+(pairRow a b i).toNat=H.degree i := by
  simpa only [subdivide,degree_adjoin_succ] using subdivide_old_degree e i

/-- For the terminal upper-layer case, erase one edge from the second hub
of the double fan and duplicate two disjoint rim edges. All further
demand is then supplied on the first hub's spokes. -/
theorem near_cone_planaric {a b t : Nat} (hs : List Nat) (hq : 5≤hs.length) (hb : hs.length≤b)
    (ht : a=t+4) (vol : a+b+hs.sum=4*(hs.length+2)+2*t)
    (hmin : ∀d∈hs,5≤d) :
    Planaric (List.replicate t 2 ++ a::b::hs) := by
  let q := hs.length
  let x1 : Fin (q+2) := ⟨1,by omega⟩
  let x2 : Fin (q+2) := ⟨2,by dsimp [q]; omega⟩
  let x3 : Fin (q+2) := ⟨3,by dsimp [q]; omega⟩
  let x4 : Fin (q+2) := ⟨4,by dsimp [q]; omega⟩
  let x5 : Fin (q+2) := ⟨5,by dsimp [q]; omega⟩
  let G := (support q).eraseEdge x1 x2
  let es := [(x2,x3),(x4,x5)]
  have edge : (support q).adj x1 x2=true := (support_adjacent_iff ..).mpr (by simp [x1,x2])
  have sub (i j : Fin (q+2)) (e : G.adj i j=true) : (support q).adj i j=true := by
    rw [show G.adj i j=_ from erase_adj ..] at e
    exact (Bool.and_eq_true_iff.mp e).1
  have planar : G.Planar := by
    apply two_apex_path_planar
    intro i j hi hj he
    have := (support_adjacent_iff ..).mp (sub i j he); omega
  have er (i : Fin (q+2)) := erase_degree (support q) x1 x2 i edge
  have spoke (i : Fin (q+1)) : G.adj 0 i.succ=true := by
    rw [show G.adj 0 i.succ=_ from erase_adj ..]
    have h := (support_adjacent_iff q 0 i.succ).mpr (by simp)
    have x10 : (0 : Fin (q+2))≠x1 := by intro e; have := congrArg Fin.val e; contradiction
    have x20 : (0 : Fin (q+2))≠x2 := by intro e; have := congrArg Fin.val e; contradiction
    simp only [eraseRel,h,beq_eq_false_iff_ne.mpr x10,beq_eq_false_iff_ne.mpr x20]
    simp
  have valid : ∀ e∈es, G.adj e.1 e.2=true := by
    intro e he
    simp only [es,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · rw [show G.adj x2 x3=_ from erase_adj ..]
      have h := (support_adjacent_iff q x2 x3).mpr (by simp [x2,x3])
      simp [eraseRel,h,x1,x2,x3,Fin.ext_iff]
    · rw [show G.adj x4 x5=_ from erase_adj ..]
      have h := (support_adjacent_iff q x4 x5).mpr (by simp [x4,x5])
      simp [eraseRel,h,x1,x2,x4,x5,Fin.ext_iff]
  have zeroDeg : G.degree 0=q+1 := by
    have he := er 0
    rw [support_hub _ (by simp)] at he
    simpa [G,pairRow,x1,x2,Bool.beq_eq_decide_eq,Fin.ext_iff] using he
  have zeroInc : incidents 0 es=0 := by simp [es,incidents,hit,x2,x3,x4,x5,Fin.ext_iff]
  have sec : G.degree (Fin.succ 0)+incidents (Fin.succ 0) es=q := by
    have he := er (Fin.succ 0)
    rw [support_hub _ (by simp)] at he
    have id : (Fin.succ (0 : Fin (q+1)))=x1 := Fin.ext rfl
    rw [id] at he ⊢
    simpa [G,pairRow,es,incidents,hit,x1,x2,x3,x4,x5,Fin.ext_iff] using he
  have rim (j : Fin q) : G.degree j.succ.succ+incidents j.succ.succ es=rimBase q j.val := by
    have he := er j.succ.succ
    rw [support_path _ (by simp)] at he
    change G.degree j.succ.succ+_= _ at he
    simp only [pairRow,es,incidents,hit,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Bool.beq_eq_decide_eq,Fin.ext_iff,Fin.val_succ,x1,x2,x3,x4,x5] at he ⊢
    simp only [rimBase]
    by_cases h0 : j.val=0 <;> by_cases h1 : j.val=1 <;>
      by_cases h2 : j.val=2 <;> by_cases h3 : j.val=3 <;>
      by_cases hl : j.val+1<q <;>
      simp (disch := omega) only [ite_eq_left,ite_eq_right,decide_eq_true,decide_eq_false,
        Bool.or_true,Bool.or_false,Bool.toNat_true,Bool.toNat_false] at he ⊢ <;> omega
  have tgt (i : Fin (q+1)) : G.degree i.succ+incidents i.succ es≤(b::hs)[i.val]'(by change i.val<q+1; exact i.isLt) := by
    refine Fin.cases (sec.symm ▸ hb) (fun j => ?_) i
    rw [rim]; change rimBase q j.val≤hs[j.val]'(j.isLt)
    have h := hmin (hs[j.val]'(j.isLt)) (List.getElem_mem j.isLt)
    unfold rimBase
    repeat' split
    all_goals omega
  obtain ⟨m,mEq,hp⟩ := expand_spokes_with_edges (b::hs) G planar spoke es valid tgt
  have total : ((List.finRange (q+1)).map (fun i => G.degree i.succ+incidents i.succ es)).sum=5*q+1 := by
    rw [List.finRange_succ,List.map_cons,List.map_map,List.sum_cons,sec]
    have vals : (List.finRange q).map Fin.val=List.range q := by apply List.ext_getElem <;> simp
    have eqn : (List.finRange q).map ((fun i : Fin (q+1) => G.degree i.succ+incidents i.succ es) ∘ Fin.succ) =
        (List.range q).map (rimBase q) := by
      rw [← vals,List.map_map]
      apply List.map_congr_left; intro i _; exact rim i
    rw [eqn,rim_sum _ (by dsimp [q]; omega)]; omega
  change m+((List.finRange (q+1)).map (fun i => G.degree i.succ+incidents i.succ es)).sum=b+hs.sum at mEq
  rw [total] at mEq
  rw [zeroDeg,zeroInc,Nat.add_zero] at hp
  have hub : q+1+m=a := by dsimp [q] at *; omega
  have budget : 2+m≤t := by dsimp [q] at *; omega
  rw [hub] at hp
  have hp' : Planaric (List.replicate (2+m) 2 ++ a::b::hs) := (planaric_perm List.perm_middle).mpr hp
  have hpos : ∃ x∈(List.replicate (2+m) 2 ++ a::b::hs), 0<x :=
    ⟨a,List.mem_append_right _ (by simp),by omega⟩
  have extra := planaric_add_twos hp' hpos (t-(2+m))
  have cat : List.replicate (t-(2+m)) 2 ++ List.replicate (2+m) 2=List.replicate t 2 := by
    apply List.eq_replicate_iff.mpr; exact ⟨by simp; omega,by simp⟩
  simpa only [← List.append_assoc,cat] using extra


theorem terminal_planaric {a t : Nat} (hs : List Nat) (hq : 6≤hs.length)
    (ht : a=t+4) (vol : a+hs.length+hs.sum=4*(hs.length+2)+2*t)
    (hmin : ∀d∈hs,5≤d) :
    Planaric (List.replicate t 2 ++ a::hs.length::hs) :=
  near_cone_planaric hs (by omega) (Nat.le_refl _) ht vol hmin

/-- For both boundaries, a large minimum-five instance is planaric or has
an equal pair whose removal satisfies the residual maximum-degree bound. -/
theorem min_five_planar_or_pair {a b c p t k : Nat} (us : List Nat)
    (hp : p=us.length+3) (hp8 : 8≤p) (hk : k≤1)
    (hs : (a::b::c::us).Pairwise (· ≥ ·))
    (hmin : ∀ d ∈ a::b::c::us, 5 ≤ d)
    (hvol : (a::b::c::us).sum+2*k=4*p+2*t) (cap : a+1≤p+t) :
    Planaric (List.replicate t 2 ++ a::b::c::us) ∨ Deletable (a::b::c::us) p t := by
  rcases min_five_graph_cases us hp hp8 hk hs hmin hvol with hc|hd|hp'|⟨rfl,hEq,hb⟩
  · left
    apply cone_range_planaric (b::c::us) (by simp) (fun v hv => hmin v (by simp [hv]))
      (j:=k) _ hc (by simp; omega)
    simp only [List.sum_cons,List.length_cons] at *; omega
  · exact .inr hd
  · exact .inl hp'
  · left
    apply near_cone_planaric (c::us) (by simp; omega) (by simp; omega) hEq
    · simp only [List.sum_cons,List.length_cons] at *; omega
    · intro v hv; exact hmin v (by simp [hv])

end SparseBoundary.Fan
