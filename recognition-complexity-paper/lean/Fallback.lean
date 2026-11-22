import Transfer

namespace Recognition
open SparseBoundary SparseBoundary.Graph Reduction Layers Rigidity Transfer

/-- In the malformed output, each of the three cubic stars would need to
supply a different face on the same edge. Every map has just two sides. -/
theorem malformed_no_map : ¬ Nonempty (Model malformedOutput) := by
  classical
  rintro ⟨R⟩
  let g := graph R
  let z (i : Fin 6) := Classical.choose ((R.hits i.val).mp i.isLt)
  have name (i : Fin 6) : R.label (z i) = i.val := Classical.choose_spec ((R.hits i.val).mp i.isLt)
  have names (a b : Fin 6) : z a = z b ↔ a = b := by
    constructor
    · intro h
      exact Fin.ext ((name a).symm.trans ((congrArg R.label h).trans (name b)))
    · intro h; rw [h]
  let p (i j : Fin 6) := decide (i ≠ j ∧ (i.val < 3 ∨ j.val < 3))
  have test : (candidates 6 (fun i => malformedOutput[i.val]'i.isLt)).all
      (fun G => (List.finRange 6).all fun i => (List.finRange 6).all fun j => G.adj i j == p i j)
      = true := by decide +kernel
  have ag (i j : Fin 6) : g.adj i j = p i j :=
    beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp test g
      (candidates_complete g _ (graph_realizes R))) i (List.mem_finRange i)) j (List.mem_finRange j))
  have adj (i j : Fin 6) : R.map.adj (z i) (z j) ↔ i ≠ j ∧ (i.val < 3 ∨ j.val < 3) := by
    have named : R.map.adj (z i) (z j) ↔ R.edge i.val j.val := by
      constructor
      · intro h; exact ⟨_,_,name i,name j,h⟩
      · rintro ⟨x,y,hx,hy,h⟩
        exact R.inj _ _ (hx.trans (name i).symm) ▸ R.inj _ _ (hy.trans (name j).symm) ▸ h
    rw [named,same_edges R i j,show (graph R).adj i j = p i j from ag i j]
    simp [p]
  have face (k : Fin 6) (lo : 3 ≤ k.val) : R.map.face (z 0) (z 1) (z k) := by
    apply R.map.rot
    apply (cubic_faces R.map (x := z k) (a := z 0) (b := z 1) (c := z 2) ?_).1
    refine ⟨fun e => (by decide : (0:Fin 6) ≠ 1) ((names _ _).mp e),
      fun e => (by decide : (1:Fin 6) ≠ 2) ((names _ _).mp e),
      fun e => (by decide : (0:Fin 6) ≠ 2) ((names _ _).mp e),?_⟩
    intro v
    let j : Fin 6 := ⟨R.label v,bound R v⟩
    have nv : v = z j := R.inj _ _ (name j).symm
    rw [nv,adj,names,names,names]
    simp only [ne_eq,Fin.ext_iff]
    change (k.val ≠ j.val ∧ (k.val < 3 ∨ j.val < 3)) ↔ j.val = 0 ∨ j.val = 1 ∨ j.val = 2
    omega
  obtain ⟨w,_,_,two⟩ := R.map.twoSides (face 3 (by decide))
  have a := two _ (face 4 (by decide))
  have b := two _ (face 5 (by decide))
  have a3 : z 4 ≠ z 3 := fun e => (by decide : (4:Fin 6) ≠ 3) ((names _ _).mp e)
  have b3 : z 5 ≠ z 3 := fun e => (by decide : (5:Fin 6) ≠ 3) ((names _ _).mp e)
  have ab : z 4 ≠ z 5 := fun e => (by decide : (4:Fin 6) ≠ 5) ((names _ _).mp e)
  exact ab ((a.resolve_left a3).trans (b.resolve_left b3).symm)

end Recognition
