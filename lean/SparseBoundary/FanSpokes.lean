import SparseBoundary.FanExpansion
import SparseBoundary.GraphPerm

namespace SparseBoundary.Fan

open Graph

private def spokeEdges {q} (w : Fin q → Nat) (xs : List (Fin q)) :
    List (Fin (q+1) × Fin (q+1)) :=
  xs.flatMap fun i => List.replicate (w i) (0,i.succ)

private theorem spoke_len {q} (w : Fin q → Nat) (xs : List (Fin q)) :
    (spokeEdges w xs).length=(xs.map w).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [spokeEdges]

private theorem spoke_inc_zero {q} (w : Fin q → Nat) (xs : List (Fin q)) :
    incidents 0 (spokeEdges w xs)=(xs.map w).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change incidents 0 (List.replicate (w i) (0,i.succ) ++ spokeEdges w xs)= w i+(xs.map w).sum
    simpa only [incidents,List.map_append,List.map_replicate,List.sum_append,
      List.sum_replicate_nat,hit,eq_self, true_or,ite_true,Nat.mul_one] using congrArg (w i+·) ih

private theorem spoke_inc_succ {q} (w : Fin q → Nat) (xs : List (Fin q)) (u : Fin q) :
    incidents u.succ (spokeEdges w xs)=xs.count u * w u := by
  induction xs with
  | nil => simp [spokeEdges,incidents]
  | cons i xs ih =>
    change incidents u.succ (List.replicate (w i) (0,i.succ) ++ spokeEdges w xs)= _
    have e : ∀ as bs : List (Fin (q+1) × Fin (q+1)), incidents u.succ (as++bs)=
        incidents u.succ as+incidents u.succ bs := by simp [incidents]
    rw [e,ih,List.count_cons]
    by_cases h : i=u
    · subst i; simp [incidents,hit,List.map_replicate,List.sum_replicate_nat,Nat.add_mul,Nat.add_comm]
    · have h' : u.val≠i.val := fun e => h (Fin.ext e).symm
      simp [incidents,hit,h,h',Fin.ext_iff,List.map_replicate,List.sum_replicate_nat]

private theorem spokes_valid {G : Graph (q+1)} (e : ∀ i : Fin q, G.adj 0 i.succ=true)
    (w : Fin q → Nat) (xs : List (Fin q)) :
    ∀ p∈spokeEdges w xs, G.adj p.1 p.2=true := by
  intro p hp
  obtain ⟨i,_,h⟩ := List.mem_flatMap.mp hp
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp h
  exact e i

/-- Raise all nonhub degrees independently by expanding existing spokes.
The hub gains exactly the number of new degree-two vertices. -/
theorem expand_spokes_with_edges (us : List Nat) (G : Graph (us.length+1)) (hg : G.Planar)
    (e : ∀ i : Fin us.length, G.adj 0 i.succ=true)
    (other : List (Fin (us.length+1) × Fin (us.length+1)))
    (valid : ∀ e∈other, G.adj e.1 e.2=true)
    (target : ∀ i : Fin us.length, G.degree i.succ+incidents i.succ other≤us[i]) :
    ∃ m, m+((List.finRange us.length).map (fun i => G.degree i.succ+incidents i.succ other)).sum = us.sum ∧
      Planaric ((G.degree 0+incidents 0 other+m)::(List.replicate (other.length+m) 2 ++ us)) := by
  let w := fun i : Fin us.length => us[i]-(G.degree i.succ+incidents i.succ other)
  let vs := List.finRange us.length
  let es := spokeEdges w vs
  have hp := expand G hg (other++es) (by
    intro p mem
    exact (List.mem_append.mp mem).elim (valid p) (spokes_valid e w vs p))
  have inc (v : Fin (us.length+1)) : incidents v (other++es)=incidents v other+incidents v es := by
    simp [incidents]
  have non (i : Fin us.length) : incidents i.succ es=w i := by
    rw [show incidents i.succ es=_ from spoke_inc_succ w vs i]
    simp [vs,(List.nodup_finRange _).count_of_mem (List.mem_finRange i)]
  have centre : incidents 0 es=es.length := (spoke_inc_zero w vs).trans (spoke_len w vs).symm
  have eqn : (List.finRange (us.length+1)).map (fun v => G.degree v+incidents v (other++es)) =
      (G.degree 0+incidents 0 other+es.length)::us := by
    rw [List.finRange_succ,List.map_cons,List.map_map,inc,centre,← Nat.add_assoc]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_finRange,Function.comp_apply,inc,non,w,← Nat.add_assoc]
      exact Nat.add_sub_of_le (target _)
  rw [eqn,List.length_append] at hp
  refine ⟨es.length,?_,(planaric_perm List.perm_middle).mp hp⟩
  have total (xs : List (Fin us.length)) :
      (xs.map w).sum + (xs.map (fun i => G.degree i.succ+incidents i.succ other)).sum =
        (xs.map (fun i => us[i])).sum := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      have h : w i+(G.degree i.succ+incidents i.succ other)=us[i] := Nat.sub_add_cancel (target i)
      simp only [List.map_cons,List.sum_cons]; omega
  have orig : vs.map (fun i => us[i])=us := by
    apply List.ext_getElem <;> simp [vs]
  rw [show es.length=_ from spoke_len w vs]
  simpa only [orig] using total vs

theorem expand_spokes (us : List Nat) (G : Graph (us.length+1)) (hg : G.Planar)
    (e : ∀ i : Fin us.length, G.adj 0 i.succ=true)
    (target : ∀ i : Fin us.length, G.degree i.succ≤us[i]) :
    ∃ m, m+((List.finRange us.length).map (fun i => G.degree i.succ)).sum = us.sum ∧
      Planaric ((G.degree 0+m)::(List.replicate m 2 ++ us)) := by
  simpa [incidents] using expand_spokes_with_edges us G hg e [] (by simp)
    (by simpa [incidents] using target)

end SparseBoundary.Fan
