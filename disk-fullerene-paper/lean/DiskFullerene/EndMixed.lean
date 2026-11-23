import DiskFullerene.EndEuler

namespace DiskFullerene.EndEuler
open Dual

noncomputable def mixedDart {M : MapData} (G : IsDiskFullerene M h) (P : Face M → Bool) (d : Dart) :=
  P (owner G d) != P (owner G d.swap)

private theorem mixed_swap {M : MapData} (G : IsDiskFullerene M h) (P : Face M → Bool) (d : Dart) :
    mixedDart G P d.swap = mixedDart G P d := by simp [mixedDart,bne_comm]

private theorem rotation_mixed {M : MapData} (G : IsDiskFullerene M h) (P : Face M → Bool)
    {u : Nat} {r : List Nat} (hr : (r,u) ∈ M.rows.zipIdx) :
    (r.map (u,·)).countP (mixedDart G P) =
      2*(if r.any (fun a => mixedDart G P (u,a)) then 1 else 0) := by
  have eqr := List.mk_mem_zipIdx_iff_getElem?.mp hr
  have hlen := G.cubic r (by rw [(List.mem_zipIdx' hr).2]; exact List.getElem_mem _)
  have full := List.all_eq_true.mp G.simpleRotation (r,u) hr
  have nd : r.Nodup := by simpa [MapData.rotationOK] using (Bool.and_eq_true_iff.mp full).1
  obtain ⟨a,b,c,er⟩ : ∃ a b c, r=[a,b,c] := ⟨_,_,_,List.eq_getElem_of_length_eq_three r hlen⟩
  subst r
  simp at nd
  have row : M.rows[u]?.getD [] = [a,b,c] := by simp [eqr]
  have turn (i j : Nat) (m : i∈[a,b,c]) (t : M.turn (i,u)=(u,j)) :
      owner G (i,u) = owner G (u,j) := by
    have e : (u,i) ∈ M.darts := dart_iff.mpr (by simp [MapData.adj,row,m])
    exact (owner_eq G (t ▸ incident_turn G (owner_incident G (dart_reverse G e)))).symm
  have t1 := turn a b (by simp) (by simp [MapData.turn,row])
  have t2 := turn b c (by simp) (by simp [MapData.turn,row,nd,List.idxOf_cons])
  have t3 := turn c a (by simp) (by simp [MapData.turn,row,nd,List.idxOf_cons])
  cases p₁ : P (owner G (u,a)) <;> cases p₂ : P (owner G (u,b)) <;> cases p₃ : P (owner G (u,c)) <;>
    simp [mixedDart,t1,t2,t3,p₁,p₂,p₃]

noncomputable def mixedVertex {M : MapData} (G : IsDiskFullerene M h) (P : Face M → Bool)
    (u : Fin M.ord) : Bool := (M.rows[u.val]'u.isLt).any (fun a => mixedDart G P (u.val,a))

private theorem sum_indicators {α} (xs : List α) (p : α → Bool) (f : α → Nat)
    (eq : ∀ x ∈ xs, f x = 2*(if p x then 1 else 0)) :
    (xs.map f).sum = 2*xs.countP p := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    have hl := ih (fun x hx => eq x (by simp [hx]))
    have ha := eq a (by simp)
    simp only [List.map_cons,List.sum_cons,List.countP_cons,hl,ha]
    split <;> omega

private theorem mixed_stars {M} (G : IsDiskFullerene M h) (P : Face M → Bool) :
    M.darts.countP (mixedDart G P) = 2*num (mixedVertex G P) := by
  let ids := (List.finRange M.ord).map (fun u => (M.rows[u.val]'u.isLt,u.val))
  have listEq : ids = M.rows.zipIdx := by
    apply List.ext_getElem <;> simp [ids,MapData.ord]
  unfold MapData.darts
  rw [List.countP_flatMap]
  let marked : List Nat × Nat → Bool := fun (r,u) => r.any (fun a => mixedDart G P (u,a))
  rw [sum_indicators _ marked _ (fun ⟨r,u⟩ mem => rotation_mixed G P mem)]
  rw [←listEq]
  simp [ids,num,List.countP_map,Function.comp_def,marked]
  rfl

private theorem swap_upper {M : MapData} (G : IsDiskFullerene M h) :
    ((edges M).map Prod.swap).Perm (M.darts.filter (fun d => !(decide (d.1<d.2)))) := by
  have nd := dart_nodup G
  apply (List.perm_ext_iff_of_nodup _ _).mpr
  · rintro ⟨a,b⟩
    constructor
    · rintro hd
      obtain ⟨⟨u,v⟩,hu,e⟩ := List.mem_map.mp hd; cases e
      have ⟨m,lt⟩ := List.mem_filter.mp hu
      have ul := of_decide_eq_true lt
      apply List.mem_filter.mpr
      exact ⟨dart_reverse G m,by simp; omega⟩
    · intro h
      obtain ⟨m,le⟩ := List.mem_filter.mp h
      have diff := (dart_info G m).2.2
      exact List.mem_map.mpr ⟨(b,a),List.mem_filter.mpr ⟨dart_reverse G m,by simp at le ⊢; omega⟩,rfl⟩
  · exact List.pairwise_map.mpr ((List.filter_sublist.nodup nd).imp
      (fun ne eq => ne (by simpa using congrArg (fun d : Dart => d.swap) eq)))
  · exact List.filter_sublist.nodup nd

/-- Color the faces of any valid cubic map arbitrarily. The number of
primal edges separating colors equals the number of primal vertices
incident with both colors. Both counts come directly from the map. -/
theorem mixed_count {M : MapData} (G : IsDiskFullerene M h) (P : Face M → Bool) :
    num (fun e : Edge M => P (dual G e).1 != P (dual G e).2) = num (mixedVertex G P) := by
  let up : Dart → Bool := fun d => d.1<d.2
  have p := (List.filter_append_perm up M.darts).countP_eq (mixedDart G P)
  have q := (swap_upper G).countP_eq (mixedDart G P)
  simp only [List.countP_map,Function.comp_def,mixed_swap] at q
  change (edges M).countP _ = (M.darts.filter (fun d => !(up d))).countP _ at q
  simp only [List.countP_append] at p
  change (edges M).countP _ + _ = _ at p
  rw [← q,mixed_stars] at p
  have e : num (fun e : Edge M => P (dual G e).1 != P (dual G e).2) = (edges M).countP (mixedDart G P) := by
    have allEdges : (List.finRange (edges M).length).map (fun e => (edges M)[e.val]) = edges M := by
      apply List.ext_getElem <;> simp
    have mapEq := congrArg (List.countP (mixedDart G P)) allEdges
    rw [← mapEq,List.countP_map]
    apply List.countP_congr
    intro i _
    have a := owner_eq G (left_incident G (endpoints_mem i))
    have b := owner_eq G (left_incident G (dart_reverse G (endpoints_mem i)))
    change (P (leftFace G (endpoints i) (endpoints_mem i)) != P (leftFace G (endpoints i).swap (dart_reverse G (endpoints_mem i)))) = true ↔
      (P (owner G (endpoints i)) != P (owner G (endpoints i).swap)) = true
    change owner G (endpoints i).swap = leftFace G (endpoints i).swap (dart_reverse G (endpoints_mem i)) at b
    rw [a,b]
  rw [e]
  change (edges M).countP (mixedDart G P) + (edges M).countP (mixedDart G P) = _ at p
  omega

end DiskFullerene.EndEuler
