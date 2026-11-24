import SparseBoundary.GraphUnion
import SparseBoundary.GraphEnumeration
import SparseBoundary.BranchDegree
import SparseBoundary.Boundary

namespace SparseBoundary.ZeroPadding
open Graph

private theorem delete_isolated {d : List Nat} {G : Graph (0::d).length}
    (row : G.Realizes (0::d)) : (G.restrict Fin.succ).Realizes d := by
  have deg : G.degree 0=0 := row 0
  have empty : (List.finRange (d.length+1)).filter (G.adj 0)=[] := List.length_eq_zero_iff.mp deg
  have absent (i : Fin d.length) : G.adj i.succ 0=false := by
    rw [G.adj_comm]
    exact Bool.eq_false_iff.mpr (List.filter_eq_nil_iff.mp empty _ (List.mem_finRange _))
  intro i
  have eq : (G.restrict Fin.succ).adj i=G.adj i.succ ∘ Fin.succ := funext (restrict_adj G Fin.succ i)
  have sd := row i.succ
  change G.degree i.succ=d[i] at sd
  have drop : G.degree i.succ=(G.restrict Fin.succ).degree i := by
    unfold degree
    simp only [List.length_cons]
    rw [List.finRange_succ]
    simp [absent, List.filter_map,eq]
  exact drop.symm.trans sd

private theorem zero_graphic (d : List Nat) : Graphic (0::d) ↔ Graphic d := by
  constructor
  · rintro ⟨G,row⟩
    exact ⟨_,delete_isolated row⟩
  · rintro ⟨G,row⟩
    refine ⟨adjoinRow (fun _=>false) G,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [degree_adjoin_zero]
    · simpa [degree_adjoin_succ] using row j

private theorem zero_planaric (d : List Nat) : Planaric (0::d) ↔ Planaric d := by
  constructor
  · rintro ⟨G,row,pg⟩
    exact ⟨_,delete_isolated row, planar_restrict pg Fin.succ (fun _ _ => Fin.succ_inj.mp)⟩
  · intro h
    let Z : Graph 1 := ⟨0⟩
    have z : Planaric [0] := ⟨Z,by unfold Graph.Realizes; decide,planar_of_few_high Z (by decide)⟩
    exact planaric_append z h

/-- Appending isolated vertices preserves and reflects ordinary graphicality. -/
theorem graphic (d : List Nat) (k : Nat) : Graphic (d++List.replicate k 0) ↔ Graphic d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ',← List.append_assoc]
    exact (graphic_perm (List.perm_append_singleton 0 _)).trans ((zero_graphic _).trans ih)

/-- Appending isolated vertices preserves and reflects potential planarity. -/
theorem planaric (d : List Nat) (k : Nat) : Planaric (d++List.replicate k 0) ↔ Planaric d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ',← List.append_assoc]
    exact (planaric_perm (List.perm_append_singleton 0 _)).trans ((zero_planaric _).trans ih)

private theorem split (d : List Nat) :
    d.Perm (d.filter (·!=0) ++ List.replicate (d.count 0) 0) := by
  apply List.perm_iff_count.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have no : (d.filter (·!=0)).count 0=0 := List.count_eq_zero.mpr (by simp)
    simp [no]
  · have pos : (x != 0)=true := bne_iff_ne.mpr hx
    simpa [List.count_replicate,Ne.symm hx] using
      (List.count_filter (l:=d) (p:=fun v : Nat => v != 0) pos).symm

/-- Remove all zero entries in their original positions. -/
theorem filter_positive (d : List Nat) :
    (Graphic d ↔ Graphic (d.filter (·!=0))) ∧ (Planaric d ↔ Planaric (d.filter (·!=0))) :=
  ⟨(graphic_perm (split d)).trans (graphic _ _),(planaric_perm (split d)).trans (planaric _ _)⟩

/-- Counting an isolated vertex in n makes the literal lower-bound assertion false. -/
theorem literal_counterexample :
    let d : List Nat := [4,4,4,4,4,0]
    Graphic d ∧ d.sum+2+2*d.count 1≤4*d.length ∧ ¬d.Perm lowerException ∧ ¬Planaric d := by
  let k : List Nat := [4,4,4,4,4]
  have complete : Graphic k := ⟨⟨1023⟩,by unfold Graph.Realizes; decide⟩
  have no : ¬Planaric k := Graph.five_core_obstruction k [] (by decide) (by decide)
  exact ⟨(graphic k 1).mpr complete,by decide,by decide, fun hp => no ((planaric k 1).mp hp)⟩

end SparseBoundary.ZeroPadding
