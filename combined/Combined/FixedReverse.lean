import Combined.FixedBudget
import Combined.FixedCut

/-! Recover the source from a realization at the prescribed subdivision budget. -/
namespace Combined.FixedReverse
open Recognition SparseBoundary LeanPool.K5MinorFreeChoosability Combined.FixedBudget Combined.FixedCut
open scoped BigOperators

private theorem row_of_tight {V : Type} [Fintype V] (K : SimpleGraph V) (e : Fin n ≃ V)
    (hp : IsPlanar K) (size : 5 ≤ n) (tight : Nat.card K.edgeSet+6=3*n) :
    let g := List.ofFn (fun i => valency K (e i))
    Reduction.TableValid g ∧ Planaric g := by
  classical
  let rel (x y : Fin n) := decide (K.Adj (e x) (e y))
  let H := Graph.ofRelation rel
  have ed (x y : Fin n) : H.adj x y = rel x y := Graph.adj_ofRelation rel
    (fun a b => decide_eq_decide.mpr (K.adj_comm _ _))
    (fun a => decide_eq_false_iff_not.mpr (K.irrefl (v := e a))) x y
  let iso : Wagner.toSimple H ≃g K := { e with
    map_rel_iff' := by
      intro x y
      rw [Wagner.toSimple_adj,ed]
      exact decide_eq_true_iff.symm }
  have deg (i : Fin n) : H.degree i = valency K (e i) := by
    rw [← Wagner.neighbor_count]
    exact Nat.card_congr (iso.mapNeighborSet i)
  have card : Nat.card V = n := by simpa using (Nat.card_congr e).symm
  let g := List.ofFn (fun i => valency K (e i))
  have len : g.length=n := List.length_ofFn
  have order (i : V) : valency K i < n := by
    rw [as_degree, ← card, Nat.card_eq_fintype_card]
    exact K.degree_lt_card_verts i
  have total : g.sum = 2*Nat.card K.edgeSet := by
    change (List.ofFn _).sum = _
    rw [List.sum_ofFn, Fintype.sum_equiv e (fun i=>valency K (e i)) (valency K) (fun _=>rfl)]
    simp_rw [as_degree]
    rw [edge_count]
    exact K.sum_degrees_eq_twice_card_edges
  change Reduction.TableValid g ∧ Planaric g
  refine ⟨⟨by simpa only [len] using size, by rw [len,total]; omega, ?_⟩,?_⟩
  · intro d hd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    rw [len]
    exact ⟨PlanarBounds.simple_tight_degree hp (by omega) (by omega) _,order _⟩
  · have flat := (Wagner.planar_iff_rotation H).mpr (isPlanar_of_iso hp iso)
    have row : List.ofFn H.degree = g := by exact congrArg List.ofFn (funext deg)
    rw [← row]
    exact Graph.planaric_profile flat

private def oldPart (k n : Nat) := (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)

private def prefixEquiv {k n : Nat} (bound : k ≤ n) : Fin k ≃ ↑(oldPart k n) where
  toFun i := ⟨⟨i.val,Nat.lt_of_lt_of_le i.isLt bound⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.isLt⟩⟩
  invFun x := ⟨x.val.val,(Finset.mem_filter.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Any planar realization uses at least the prescribed number of twos. At
exactly that number a realizing graph yields a planar realization of the source. -/
theorem reverse {d : List Nat} {r s : Nat} (dv : Reduction.TableValid d) (fit : r+3 ≤ d.length)
    (p : Planaric (core d r ++ List.replicate s 2)) : r ≤ s ∧ (s=r → Planaric d) := by
  classical
  let a := full (full d)
  let old := oldRow a (marks d.length r)
  let b := 2*a.length-4+2*r
  let ds := core d r ++ List.replicate s 2
  have lenOld : old.length=a.length := by simp [old,oldRow]
  have len : ds.length=a.length+b+s := by simp [ds,core,oldRow,a,b,Nat.add_assoc]
  have av := full_valid (full_valid dv)
  have al : 5 ≤ a.length := av.1
  have prior := full_length d
  have next := full_length (full d)
  have boundMarks (i) (hi : i ∈ marks d.length r) : i<a.length := by
    have := marks_bounded (by omega : r≤d.length) hi
    change i<(full (full d)).length
    omega
  have rowSum : old.sum + 24 = 12*a.length+6*r := by
    have z := oldRow_sum (marks_nodup (by omega : r≤d.length)) boundMarks
    have m : (marks d.length r).length = 2*r := by simp [marks,Nat.two_mul]
    rw [m] at z
    have ev : a.sum+12=6*a.length := av.2.1
    dsimp only [old]
    omega
  obtain ⟨G,values,plan⟩ := p
  let J := Wagner.toSimple G
  let S := oldPart a.length ds.length
  let e : Fin a.length ≃ ↑S := prefixEquiv (by omega)
  have num : S.card = a.length := by simpa using (Nat.card_congr e).symm
  have flat := (Wagner.planar_iff_rotation G).mp plan
  have oldDeg (i : Fin a.length) : valency J (e i).val = old[i.val]?.getD 0 := by
    change valency (Wagner.toSimple G) (e i).val = _
    rw [valency,Wagner.neighbor_count,values]
    have ho : i.val < old.length := by rw [lenOld]; exact i.isLt
    have hc : i.val < (old ++ List.replicate b 3).length := by simp; omega
    have hi : i.val < ((old ++ List.replicate b 3) ++ List.replicate s 2).length := by simp; omega
    change ((old ++ List.replicate b 3) ++ List.replicate s 2)[i.val] = _
    rw [List.getElem_append_left hc,List.getElem_append_left ho,List.getElem?_eq_getElem ho]
    rfl
  have sum : (∑ x : S, valency J x.val) = old.sum := by
    rw [← Fintype.sum_equiv e (fun i=>valency J (e i).val) (fun x=>valency J x.val) (fun _=>rfl)]
    simp_rw [oldDeg]
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · simp [lenOld]
    · intro i hi hj
      simp [List.getElem?_eq_getElem hj]
  have total : Nat.card (Fin ds.length)=S.card+b+s := by simpa [num] using len
  have cubes : b+4=2*S.card+2*r := by dsimp [b]; omega
  obtain ⟨least,both⟩ := saturation J flat S r s b (by omega) total cubes (by rw [sum]; omega)
  refine ⟨least,?_⟩
  intro hit
  obtain ⟨tK,tC,_⟩ := both hit
  let K := J.induce (S : Set (Fin ds.length))
  have kp := PlanarBounds.planar_subgraph J K Subtype.val Subtype.val_injective (fun _ _ h => h) flat
  obtain ⟨gv,gp⟩ := row_of_tight K e kp al (tK.trans (congrArg (3*·) num))
  apply recover_source dv fit gv gp List.length_ofFn
  intro i hi
  have ord : i<a.length := by simpa using hi
  have flip := max_cut_flip J flat S (by rw [total]; omega) tC (e ⟨i,ord⟩)
  rw [oldDeg] at flip
  simpa [List.getElem?_ofFn,ord,K,old,a] using flip

end Combined.FixedReverse
