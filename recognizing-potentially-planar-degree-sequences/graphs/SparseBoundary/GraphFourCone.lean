import SparseBoundary.FanOuter
import SparseBoundary.FanSpokes
import SparseBoundary.GraphSeries
import SparseBoundary.GraphPerm

namespace SparseBoundary
namespace FourCone
open Graph

/-- The rim labels are 1,...,q. Besides the two fixed disjoint chords,
    the optional chord (4,8) encloses (5,7). -/
private def forward (q j x y : Nat) : Prop :=
  y=x+1 ∨ (x=1 ∧ y=q) ∨ (x=1 ∧ y=3) ∨ (x=5 ∧ y=7) ∨ (j=1 ∧ x=4 ∧ y=8)
private instance (q j x y : Nat) : Decidable (forward q j x y) := by unfold forward; infer_instance
private def relation (q j x y : Nat) := decide (x≠y ∧ (x=0 ∨ y=0 ∨ forward q j x y ∨ forward q j y x))
private def support (q j : Nat) : Graph (q+1) := ofRelation fun x y => relation q j x.val y.val

private theorem adjacent (q j : Nat) (x y : Fin (q+1)) :
    (support q j).adj x y=relation q j x.val y.val := by
  apply adj_ofRelation
  · intro x y; simp only [relation,decide_eq_decide]; grind
  · intro i; simp [relation]

set_option maxHeartbeats 2800000 in
private theorem planar (q j : Nat) (_size : 7+j≤q) : (support q j).Planar := by
  apply Fan.outer_order_planar (v:=0)
  refine ⟨Fin.val,fun _ _ e => Fin.ext e,?_⟩
  intro u v x y u0 v0 x0 y0 ux uy vx vy uv xy
  have nz {z : Fin (q+1)} (h : z≠0) : z.val≠0 := fun e => h (Fin.ext e)
  have ne {z w : Fin (q+1)} (h : z≠w) : z.val≠w.val := fun e => h (Fin.ext e)
  have hu := nz u0; have hv := nz v0; have hx := nz x0; have hy := nz y0
  have hux := ne ux; have huy := ne uy; have hvx := ne vx; have hvy := ne vy
  simp only [adjacent,relation,decide_eq_true_eq,hu,hv,hx,hy,false_or,forward] at uv xy
  simp only [decide_eq_decide]
  by_cases s1 : u.val≤v.val <;> by_cases s2 : x.val≤y.val <;>
    simp (disch := omega) only [Nat.min_def,Nat.max_def,ite_eq_left,ite_eq_right] <;> omega

private theorem spoke (q j : Nat) (i : Fin q) : (support q j).adj 0 i.succ=true := by
  simp [adjacent,relation]

private theorem pole (q j : Nat) : (support q j).degree 0=q := by
  simp [degree,List.finRange_succ,List.filter_eq_self.mpr,spoke]

private def chordList (j x : Nat) : List Nat :=
  if x=1 then [3] else if x=3 then [1] else if x=5 then [7] else if x=7 then [5]
  else if j=1 ∧ x=4 then [8] else if j=1 ∧ x=8 then [4] else []

private def ring (q j x : Nat) : List Nat :=
  [0,if x=1 then q else x-1,if x=q then 1 else x+1] ++ chordList j x

private theorem positions (x : Nat) :
    x=1 ∨ x=3 ∨ x=5 ∨ x=7 ∨ x=4 ∨ x=8 ∨ (x≠1 ∧ x≠3 ∧ x≠5 ∧ x≠7 ∧ x≠4 ∧ x≠8) := by omega

private theorem chord_bound (x j : Nat) : (chordList j x).length≤1 := by
  rcases positions x with h|h|h|h|h|h|h <;> by_cases jj : j=1 <;>
    simp (disch := omega) [*,chordList]

private theorem ring_degree (q j : Nat) (size : 7+j≤q) (i : Fin q) :
    (support q j).degree i.succ=3+(chordList j (i.val+1)).length := by
  let verts := ((List.finRange (q+1)).filter ((support q j).adj i.succ)).map Fin.val
  have nod : verts.Nodup := List.Pairwise.map Fin.val (fun _ _ he eq => he (Fin.ext eq)) (List.Pairwise.filter _ (List.nodup_finRange _))
  have rn : (ring q j (i.val+1)).Nodup := by
    rcases positions (i.val+1) with h|h|h|h|h|h|h <;> by_cases top : i.val+1=q <;>
      by_cases jj : j=1 <;> simp (disch := omega) [*,ring,chordList,ite_eq_left,ite_eq_right] <;> omega
  have eqv : verts.Perm (ring q j (i.val+1)) := by
    apply (List.perm_ext_iff_of_nodup nod rn).mpr
    intro y
    have hva : y∈verts ↔ y≤q ∧ relation q j (i.val+1) y=true := by
      simp only [verts,List.mem_map,List.mem_filter,List.mem_finRange,true_and,adjacent,Fin.val_succ]
      constructor
      · rintro ⟨x,hx,rfl⟩; exact ⟨by omega,hx⟩
      · rintro ⟨h,hx⟩; exact ⟨⟨y,by omega⟩,hx,rfl⟩
    rw [hva]
    rcases positions (i.val+1) with h|h|h|h|h|h|h <;> by_cases top : i.val+1=q <;>
      by_cases jj : j=1 <;> simp (disch := omega) [*,ring,chordList,relation,forward,ite_eq_left,ite_eq_right] <;> omega
  have h := eqv.length_eq
  simp [verts,ring,degree] at h ⊢; omega

private theorem total_chords (q j : Nat) (size : 7+j≤q) (small : j≤1) :
    ((List.finRange q).map (fun i => (chordList j (i.val+1)).length)).sum=4+2*j := by
  have rg : (List.finRange q).map Fin.val=List.range q := by apply List.ext_getElem <;> simp
  have tt : (List.range q).map (fun i => (chordList j (i+1)).length) =
      (List.finRange q).map (fun i => (chordList j (i.val+1)).length) := by rw [← rg,List.map_map]; rfl
  rw [← tt]
  have bump (m : Nat) (h : 8≤m) : (chordList j (m+1)).length=0 := by
    simp (disch := omega) [*,chordList,ite_eq_right]
  by_cases s : j=0
  · subst j
    have grow (k) : ((List.range (7+k)).map (fun i => (chordList 0 (i+1)).length)).sum=4 := by
      induction k with
      | zero => decide
      | succ k ih =>
        rw [Nat.add_succ,List.range_succ,List.map_append,List.sum_append,ih]
        simp (disch := omega) [*,chordList,ite_eq_right]
    have hq : q=7+(q-7) := by omega
    rw [hq]; exact grow _
  · have sj : j=1 := by omega
    subst j
    have grow (k) : ((List.range (8+k)).map (fun i => (chordList 1 (i+1)).length)).sum=6 := by
      induction k with
      | zero => decide
      | succ k ih =>
        rw [Nat.add_succ,List.range_succ,List.map_append,List.sum_append,ih]
        simp [bump (8+k) (by omega)]
    have hq : q=8+(q-8) := by omega
    rw [hq]; exact grow _

/-- For an upper-layer core of minimum four, the two hub degrees nearest
    the universal bound are constructive. The next-to-universal case
    needs eight rim vertices. -/
theorem near_universal {a t j : Nat} (us : List Nat) (small : j≤1) (size : 7+j≤us.length)
    (minimum : ∀ x∈us,4≤x) (vol : a+us.sum=4*(us.length+1)+2*t)
    (hub : a+j=us.length+t) :
    Planaric (List.replicate t 2 ++ a::us) := by
  let q := us.length
  let H := support q j
  have tgt (i : Fin q) : H.degree i.succ≤us[i] := by
    rw [show H.degree i.succ=_ from ring_degree q j size i]
    have h := minimum us[i] (List.getElem_mem _)
    have cap := chord_bound (i.val+1) j; omega
  obtain ⟨m,hs,pl⟩ := Fan.expand_spokes us H (planar q j size) (spoke q j) tgt
  have row : ((List.finRange q).map (fun i => H.degree i.succ)).sum=3*q+(4+2*j) := by
    have sumadd (l : List (Fin q)) : (l.map (fun i => H.degree i.succ)).sum =
        3*l.length+(l.map (fun i => (chordList j (i.val+1)).length)).sum := by
      induction l with
      | nil => simp
      | cons i l ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
        rw [show H.degree i.succ=_ from ring_degree q j size i]; omega
    simpa [total_chords q j size small] using sumadd (List.finRange q)
  change m+((List.finRange q).map (fun i => H.degree i.succ)).sum=us.sum at hs
  rw [row] at hs
  have ha : H.degree 0+m=a := by rw [show H.degree 0=q from pole ..]; dsimp [q] at *; omega
  have hm : m+j=t := by dsimp [q] at *; omega
  rw [ha] at pl
  have p := (planaric_perm List.perm_middle).mpr pl
  have e := planaric_add_twos p ⟨a,List.mem_append_right _ (by simp),by dsimp [q] at *; omega⟩ j
  have eqn : List.replicate j 2 ++ List.replicate m 2=List.replicate t 2 := by
    apply List.eq_replicate_iff.mpr; exact ⟨by simp; omega,by simp⟩
  rwa [← List.append_assoc,eqn] at e

end FourCone
end SparseBoundary
