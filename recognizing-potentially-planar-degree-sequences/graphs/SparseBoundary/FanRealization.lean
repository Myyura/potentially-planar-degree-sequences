import SparseBoundary.FanWeights
import SparseBoundary.GraphPerm
import SparseBoundary.GraphSeries

namespace SparseBoundary.Fan

open Graph

private def neighbours (v w : Nat) : Bool :=
  decide (v≠w ∧ (v≤1 ∨ w≤1 ∨ v+1=w ∨ w+1=v))

/-- The double fan on q ordered path vertices, with hubs labelled zero and one. -/
def support (q : Nat) : Graph (q+2) := ofRelation (fun v w => neighbours v.val w.val)

private theorem support_adj (q : Nat) (v w : Fin (q+2)) :
    (support q).adj v w = neighbours v.val w.val := by
  apply adj_ofRelation
  · intro i j; apply Bool.eq_iff_iff.mpr; simp only [neighbours,decide_eq_true_eq]; omega
  · intro i; simp [neighbours]

theorem support_adjacent_iff (q : Nat) (v w : Fin (q+2)) :
    (support q).adj v w=true ↔ v.val≠w.val ∧
      (v.val≤1 ∨ w.val≤1 ∨ v.val+1=w.val ∨ w.val+1=v.val) := by
  simp [support_adj,neighbours]

theorem support_planar (q : Nat) : (support q).Planar := by
  apply two_apex_path_planar
  intro u v hu hv he
  simp only [support_adj,neighbours,decide_eq_true_eq] at he
  omega

private theorem finvals (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem <;> simp

private theorem support_count (q : Nat) (v : Fin (q+2)) :
    (support q).degree v=(List.range (q+2)).countP (neighbours v.val) := by
  rw [← finvals, List.countP_eq_length_filter, List.filter_map, List.length_map]
  unfold degree
  congr 2
  funext w
  apply support_adj

private theorem hub_count (n v : Nat) (h : v≤1) :
    (List.range n).countP (neighbours v) = n - (if v<n then 1 else 0) := by
  induction n with
  | zero => simp <;> omega
  | succ n ih =>
    rw [List.range_succ,List.countP_append,ih]
    simp only [List.countP_cons,List.countP_nil,neighbours,decide_eq_true_eq]
    split <;> split <;> split <;> omega

private theorem path_count (n v : Nat) (h : 2≤v) :
    (List.range n).countP (neighbours v) = min n 2 +
      (if 2<v ∧ v≤n then 1 else 0) + (if v+1<n then 1 else 0) := by
  induction n with
  | zero => simp <;> omega
  | succ n ih =>
    rw [List.range_succ,List.countP_append,ih]
    simp only [List.countP_cons,List.countP_nil,neighbours,decide_eq_true_eq]
    repeat' split <;> try omega

theorem support_hub {q : Nat} (v : Fin (q+2)) (h : v.val≤1) :
    (support q).degree v=q+1 := by
  rw [support_count,hub_count _ _ h,ite_eq_left v.isLt]; omega

theorem support_path {q : Nat} (v : Fin (q+2)) (h : 2≤v.val) :
    (support q).degree v=2+(if 2<v.val then 1 else 0)+
      (if v.val+1<q+2 then 1 else 0) := by
  rw [support_count,path_count _ _ h]
  simp [show v.val≤q+2 by omega]


private def forgetPair (e : Fin n × Fin n) : Nat × Nat := (e.1.val,e.2.val)

private theorem lift_edges (q : Nat) (es : ExtraEdges)
    (h : ∀ e ∈ es, e.1<e.2 ∧ e.2<q+2 ∧ (e.1≤1 ∨ e.2=e.1+1)) :
    ∃ fs : List (Fin (q+2) × Fin (q+2)), fs.map forgetPair=es ∧
      ∀ f ∈ fs, (support q).adj f.1 f.2=true := by
  induction es with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons e es ih =>
    obtain ⟨hl,hr,ok⟩ := h e (by simp)
    obtain ⟨fs,he,hg⟩ := ih (fun v m => h v (by simp [m]))
    let f : Fin (q+2) × Fin (q+2) := (⟨e.1,by omega⟩,⟨e.2,hr⟩)
    refine ⟨f::fs,by simp [f,forgetPair,he],?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl|hu
    · rw [support_adj]
      simp only [neighbours,decide_eq_true_eq,f]
      omega
    · exact hg u hu

private theorem incidents_forget (fs : List (Fin n × Fin n)) (v : Fin n) :
    incidents v fs=extraDegree (fs.map forgetPair) v.val := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change hit v f+incidents v fs = (if v.val=f.1.val ∨ v.val=f.2.val then 1 else 0)+_
    rw [ih]; simp [hit,Fin.ext_iff,extraDegree,List.sum]

/-- Path degrees after an allocation cs, excluding the two hub entries. -/
def pathProfile (cs : List Nat) : List Nat :=
  (List.finRange cs.length).map (fun j =>
    2+(if 0<j.val then 1 else 0)+(if j.val+1<cs.length then 1 else 0)+cs[j])

/-- A filled allocation gives a planar simple graph with exactly one vertex
of degree two per extra edge copy; both hub degrees and all path degrees
are stated in the natural order of the support. -/
theorem filled_planaric {cs : List Nat} {a b : Nat} (h : Filled cs a b) :
    ∃ k, 2*k=a+b+cs.sum ∧ Planaric (List.replicate k 2 ++
      (cs.length+1+a)::(cs.length+1+b)::pathProfile cs) := by
  obtain ⟨es,hv,h0,h1,hp,hn⟩ := filled_edge_list h
  obtain ⟨fs,hfs,ok⟩ := lift_edges cs.length es hv
  have hk : fs.length=es.length := by simpa using congrArg List.length hfs
  have deg (v : Fin (cs.length+2)) : incidents v fs=extraDegree es v.val := by
    rw [incidents_forget,hfs]
  have he := expand (support cs.length) (support_planar _) fs ok
  refine ⟨es.length,hn,?_⟩
  rw [hk] at he
  have eqn : (List.finRange (cs.length+2)).map
      (fun v => (support cs.length).degree v+incidents v fs) =
      (cs.length+1+a)::(cs.length+1+b)::pathProfile cs := by
    rw [List.finRange_succ (n:=cs.length+1), List.finRange_succ (n:=cs.length)]
    simp only [List.map_cons,List.map_map]
    congr 1
    · rw [support_hub _ (by simp),deg]; exact congrArg _ h0
    congr 1
    · rw [support_hub _ (by simp),deg]; exact congrArg _ h1
    apply List.map_congr_left
    intro j _
    change (support cs.length).degree j.succ.succ + incidents j.succ.succ fs = _
    rw [support_path _ (by simp),deg]
    change 2+(if 2<j.val+2 then 1 else 0)+(if j.val+2+1<cs.length+2 then 1 else 0)+
      extraDegree es (j.val+2) = _
    rw [hp,List.getElem?_eq_getElem j.isLt]
    simp [show 2<j.val+2 ↔ 0<j.val by omega,show j.val+2+1<cs.length+2 ↔ j.val+1<cs.length by omega]
  rw [eqn] at he; exact he


private theorem bump_length (cs : List Nat) : (bumpLast cs).length=cs.length := by
  match cs with
  | [] | [_] => rfl
  | a::b::rs => simpa only [bumpLast,List.length_cons,Nat.succ.injEq] using bump_length (b::rs)

private theorem ends_length (cs : List Nat) : (ends cs).length=cs.length := by
  cases cs with
  | nil => rfl
  | cons a cs => exact bump_length ((a+1)::cs)

private theorem bump_get (cs : List Nat) (j : Nat) :
    (bumpLast cs)[j]? = cs[j]?.map (fun u => u + if j+1=cs.length then 1 else 0) := by
  match cs with
  | [] => simp [bumpLast]
  | [a] => cases j <;> simp [bumpLast]
  | a::b::rs =>
    cases j with
    | zero => simp [bumpLast]
    | succ j => simpa [bumpLast,List.length_cons] using bump_get (b::rs) j

private theorem ends_get (cs : List Nat) (j : Nat) :
    (ends cs)[j]? = cs[j]?.map (fun u => u+(if j=0 then 1 else 0)+
      (if j+1=cs.length then 1 else 0)) := by
  cases cs with
  | nil => simp [ends]
  | cons a cs =>
    unfold ends
    rw [bump_get]
    cases j <;> simp

private theorem profile_ends (xs : List Nat) : pathProfile (ends xs)=xs.map (·+4) := by
  apply List.ext_getElem
  · simp [pathProfile,ends_length]
  · intro i l r
    have hi : i<xs.length := by simpa using r
    have hends : i<(ends xs).length := by simpa [ends_length] using hi
    have hh := ends_get xs i
    rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hends] at hh
    simp only [Option.map_some,Option.some.injEq] at hh
    simp only [pathProfile,List.getElem_map,List.getElem_finRange,Fin.val_cast]
    change 2+(if 0<i then 1 else 0)+(if i+1<(ends xs).length then 1 else 0)+(ends xs)[i] = xs[i]+4
    rw [hh,ends_length]
    by_cases h0 : i=0 <;> by_cases hl : i+1=xs.length <;>
      simp (disch := omega) only [ite_eq_left,ite_eq_right] <;> omega

private theorem residual_sum {us : List Nat} (h : ∀ d∈us, 4≤d) :
    (us.map (·-4)).sum+4*us.length=us.sum := by
  induction us with
  | nil => simp
  | cons d us ih =>
    have hd := h d (by simp)
    have hh := ih (fun i m => h i (by simp [m]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]; omega

/-- A degree-weight certificate on a double fan produces a planar graph
with precisely the indicated hub and path degrees and the minimum number
of subdivision vertices for this construction. -/
theorem degree_weights_planaric {a b : Nat} {us : List Nat}
    (w : DegreeWeights a b us) (hne : us≠[]) (ha : us.length+1≤a)
    (hb : us.length+1≤b) (hm : ∀ d∈us, 4≤d) :
    ∃ k, 2*k+6*us.length=a+b+us.sum ∧
      Planaric (List.replicate k 2 ++ a::b::us) := by
  obtain ⟨ord,perm,filled⟩ := w
  obtain ⟨k,hs,hp⟩ := filled_planaric filled
  have hn : ord.length=us.length := by simpa using perm.length_eq.symm
  have ho : ord≠[] := by intro h; rw [h] at hn; exact hne (List.length_eq_zero_iff.mp hn.symm)
  have ht := ends_sum ho
  have total := residual_sum hm
  have hpSum := perm.sum_nat
  refine ⟨k,by omega,?_⟩
  rw [profile_ends,ends_length,hn,Nat.add_sub_of_le ha,Nat.add_sub_of_le hb] at hp
  have hp' := perm.map (·+4)
  have back : (us.map (·-4)).map (·+4) = us := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id us]
    apply List.map_congr_left
    intro d hd
    change d-4+4=d
    have := hm d hd; omega
  rw [back] at hp'
  apply (planaric_perm ((List.Perm.cons a (List.Perm.cons b hp'.symm)).append_left _)).mp hp


/-- Extra subdivisions spend every unused degree-two vertex, so the
constructed realization applies to the prescribed sequence itself. -/
theorem degree_weights_planaric_with_twos {a b t : Nat} {us : List Nat}
    (w : DegreeWeights a b us) (hne : us≠[]) (ha : us.length+1≤a)
    (hb : us.length+1≤b) (hm : ∀ d∈us, 4≤d)
    (budget : a+b+us.sum≤6*us.length+2*t) :
    Planaric (List.replicate t 2 ++ a::b::us) := by
  obtain ⟨k,hk,hp⟩ := degree_weights_planaric w hne ha hb hm
  have hmem : a∈(List.replicate k 2 ++ a::b::us) := List.mem_append_right _ (by simp)
  have hp' := planaric_add_twos hp ⟨a,hmem,by omega⟩ (t-k)
  have eqn : List.replicate (t-k) 2 ++ List.replicate k 2 = List.replicate t 2 := by
    apply (List.eq_replicate_iff).mpr
    exact ⟨by simp; omega,by simp⟩
  simpa only [← List.append_assoc,eqn] using hp'

/-- The branch using the double fan now concludes actual planarity, in both
boundary layers and for every core order at least eight. -/
theorem min_five_graph_cases {a b c p t k : Nat} (us : List Nat)
    (hp : p=us.length+3) (hp8 : 8≤p) (hk : k≤1)
    (hs : (a::b::c::us).Pairwise (· ≥ ·))
    (hmin : ∀ d ∈ a::b::c::us, 5 ≤ d)
    (hvol : (a::b::c::us).sum+2*k=4*p+2*t) :
    t+5 ≤ a+k ∨ Deletable (a::b::c::us) p t ∨
      Planaric (List.replicate t 2 ++ a::b::c::us) ∨
      (k=0 ∧ a=t+4 ∧ b=p-2) := by
  rcases min_five_cases_with_hub_bound us hp hp8 hk hs hmin hvol with h|h|⟨hb,w⟩|h
  · exact .inl h
  · exact .inr (.inl h)
  · apply Or.inr; apply Or.inr; apply Or.inl
    have hab := List.rel_of_pairwise_cons hs (by simp : b∈b::c::us)
    apply degree_weights_planaric_with_twos w (by simp) (by simp; omega) (by simp; omega)
    · intro d hd; have := hmin d (by simp [hd]); omega
    · simp only [List.length_cons,List.sum_cons] at *; omega
  · exact .inr (.inr (.inr h))

end SparseBoundary.Fan
