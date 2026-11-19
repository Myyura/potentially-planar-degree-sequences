import SparseBoundary.Fan
import SparseBoundary.FanExpansion

namespace SparseBoundary.Fan

/-- Edge labels before conversion to the finite vertex set. -/
abbrev ExtraEdges := List (Nat × Nat)

private def atV (v atIndex x : Nat) : Nat := if v=atIndex then x else 0
private def natHit (v : Nat) (e : Nat × Nat) : Nat :=
  if v=e.1 ∨ v=e.2 then 1 else 0
def extraDegree (es : ExtraEdges) (v : Nat) := (es.map (natHit v)).sum

private theorem copies_hits (s t k v : Nat) (hst : s<t) :
    extraDegree (List.replicate k (s,t)) v=atV v s k+atV v t k := by
  by_cases a : v=s <;> by_cases b : v=t <;> simp_all [extraDegree,atV,natHit,
    List.map_replicate,List.sum_replicate_nat] <;> omega

private theorem append_hits (es fs : ExtraEdges) (v : Nat) :
    extraDegree (es++fs) v=extraDegree es v+extraDegree fs v := by simp [extraDegree]

private def Valid (n : Nat) (e : Nat × Nat) : Prop :=
  e.1<e.2 ∧ e.2<n ∧ (e.1≤1 ∨ e.2=e.1+1)

private def slot (start : Nat) (cs : List Nat) (v : Nat) : Nat :=
  if start≤v then cs[v-start]?.getD 0 else 0

private theorem slot_cons (s c v : Nat) (cs : List Nat) :
    slot s (c::cs) v = atV v s c + slot (s+1) cs v := by
  by_cases hl : v<s
  · simp [slot,atV,show ¬s≤v by omega,show ¬s+1≤v by omega,show v≠s by omega]
  by_cases he : v=s
  · subst v; simp [slot,atV,show ¬s+1≤s by omega]
  · have h : v-s=(v-(s+1))+1 := by omega
    simp [slot,atV,he,show s≤v by omega,show s+1≤v by omega,h]

private theorem realize_tail (p : Packing i cs x ds) (h : Spokes ds a b) (s : Nat) (hs : 2≤s) :
    ∃ es : ExtraEdges, es.length=x+a+b ∧ (∀ e ∈ es, Valid (s+cs.length) e) ∧
      ∀ v, extraDegree es v+atV v s i=atV v 0 a+atV v 1 b+slot s cs v := by
  induction p generalizing a b s with
  | nil =>
    cases h
    refine ⟨[],by simp,by simp,?_⟩
    intro v; simp [extraDegree,atV,slot]
  | @cons i o d c m cs ds hc ht ih =>
    cases h with
    | cons l r tail =>
      obtain ⟨rest,hlen,valid,count⟩ := ih tail (s+1) (by omega)
      let path := List.replicate o (s,s+1)
      let left := List.replicate l (0,s)
      let right := List.replicate r (1,s)
      refine ⟨path++left++right++rest,?_,?_,?_⟩
      · simp [path,left,right,hlen]; omega
      · intro e he
        simp only [List.mem_append] at he
        rcases he with ((he|he)|he)|he
        · obtain ⟨hn,rfl⟩ := List.mem_replicate.mp he
          have hpos : cs≠[] := by rintro rfl; cases ht; omega
          have hlen' : 0<cs.length := List.length_pos_iff.mpr hpos
          simp [Valid]; omega
        · obtain ⟨_,rfl⟩ := List.mem_replicate.mp he
          simp [Valid]; omega
        · obtain ⟨_,rfl⟩ := List.mem_replicate.mp he
          simp [Valid]; omega
        · simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using valid e he
      · intro v
        have hcnt := count v
        simp only [append_hits,path,left,right,copies_hits _ _ _ _ (by omega : s<s+1),
          copies_hits _ _ _ _ (by omega : 0<s),copies_hits _ _ _ _ (by omega : 1<s),
          slot_cons]
        unfold atV at *
        by_cases hv0 : v=0 <;> by_cases hv1 : v=1 <;> by_cases hvs : v=s <;>
          by_cases hvt : v=s+1 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right] at hcnt ⊢ <;> omega

/-- Produce all extra copies on the labelled double fan from its integral
weight certificate. The load on hub 0 is a, that on hub 1 is b, and the
path loads are the individual capacities in their indicated order. -/
theorem filled_edge_list {cs : List Nat} {a b : Nat} (h : Filled cs a b) :
    ∃ es : ExtraEdges, (∀ e ∈ es, e.1<e.2 ∧ e.2<cs.length+2 ∧
      (e.1≤1 ∨ e.2=e.1+1)) ∧ extraDegree es 0=a ∧ extraDegree es 1=b ∧
      (∀ j, extraDegree es (j+2)=cs[j]?.getD 0) ∧
      2*es.length=a+b+cs.sum := by
  obtain ⟨z,x,ds,l,r,p,hs,ha,hb⟩ := h
  obtain ⟨es,hn,hv,hc⟩ := realize_tail p hs 2 (by decide)
  let centre := List.replicate z (0,1)
  have degrees (v : Nat) :
      extraDegree (centre++es) v=atV v 0 a+atV v 1 b+slot 2 cs v := by
    have he := hc v
    rw [append_hits,copies_hits _ _ _ _ (by decide : 0<1)]
    unfold atV at *
    by_cases h0 : v=0 <;> by_cases h1 : v=1 <;> by_cases h2 : v=2 <;>
      simp_all <;> omega
  refine ⟨centre++es,?_,?_,?_,?_,?_⟩
  · intro e he
    rcases List.mem_append.mp he with he|he
    · obtain ⟨_,rfl⟩ := List.mem_replicate.mp he
      simp
    · simpa [Valid,Nat.add_comm] using hv e he
  · simpa [atV,slot] using degrees 0
  · simpa [atV,slot] using degrees 1
  · intro j
    simpa [atV,slot,show j+2 ≠ 0 by omega,show j+2≠1 by omega,
      show 2≤j+2 by omega] using degrees (j+2)
  · have hp := p.total
    have sumSpokes {ss L R} (h : Spokes ss L R) : ss.sum=L+R := by
      induction h with
      | nil => simp
      | cons l r _ ih => simp only [List.sum_cons]; omega
    have := sumSpokes hs
    simp [centre,hn]; omega

end SparseBoundary.Fan
