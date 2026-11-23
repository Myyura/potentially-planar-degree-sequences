import DiskFullerene.TerminalRuns
import DiskFullerene.EndSix
import DiskFullerene.EndGeometry

namespace DiskFullerene.EndSix
open Dual Separation EndEuler EndGeometry

private theorem freePositions : ∀ (d : Fin 7) (a b : Fin 6),
    (d.val=5 ∨ d.val=6) → a.val<d.val → b.val<d.val →
    (a=b ∨ consecutive d.val a.val b.val) → ∃ i : Fin 6, i.val<d.val ∧
      ∀ j : Fin 3, (i.val+j.val)%d.val ≠ a.val ∧ (i.val+j.val)%d.val ≠ b.val := by
  set_option maxRecDepth 8192 in unfold consecutive; decide +kernel

theorem run_of_ear {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M → Bool)
    (K : List (Face M)) (selected : ∀ f, f∈K ↔ A f=true) (off : apex M∉K)
    (exposed : ∀ c∈K, ∃ z∈dualRow G c, z∉K)
    (conn : ∀ x∉K, ∀ y∉K, OutsideWalk G K x y) {c a b : Face M}
    (hc : c∈K) (ha : a∈K) (hb : b∈K) (ea : a∈dualRow G c) (eb : b∈dualRow G c)
    (together : a=b ∨ b∈dualRow G a) (only : ∀ z∈dualRow G c, z∈K → z=a ∨ z=b) :
    BoundaryRun G A c := by
  let R := dualRow G c
  obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp ea
  obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp eb
  have d := inner_degree G (fun eq=>off (eq ▸ hc))
  change R.length=5 ∨ R.length=6 at d
  change i<R.length at hi; change j<R.length at hj
  have nd := row_nodup G (noRepeatOnSphere G hh) c
  change R.Nodup at nd
  have inj {i j} (hi : i<R.length) (hj : j<R.length) (eq : R[i]=R[j]) : i=j := by
    have same := congrArg (fun q=>R.idxOf q) eq
    simpa only [List.Nodup.idxOf_getElem nd] using same
  have n : R.length=M.faces[c.val].length := row_length G c
  let I : Fin M.faces[c.val].length := ⟨i,by omega⟩
  let J : Fin M.faces[c.val].length := ⟨j,by omega⟩
  have atI : atSide G c I=a := (atSide_eq G c I).trans ei
  have atJ : atSide G c J=b := (atSide_eq G c J).trans ej
  have ord : i=j ∨ consecutive R.length i j := by
    rcases together with same|edge
    · exact Or.inl (inj hi hj (ei.trans (same.trans ej.symm)))
    right
    by_cases lt : i<j
    · have f := openRim G hh K exposed conn c hc I J lt (atI ▸ ha) (atJ ▸ hb) (by rwa [atI,atJ])
      change j=i+1 ∨ (i=0 ∧ j+1=_) at f; unfold consecutive; omega
    · have ne : i≠j := by rintro rfl; exact row_no_loop G hh b (ei.symm.trans ej ▸ edge)
      have f := openRim G hh K exposed conn c hc J I (by change j<i; omega) (atJ ▸ hb) (atI ▸ ha) (by rw [atI,atJ]; exact (dual_adj_symmetric G ..).mp edge)
      change i=j+1 ∨ (j=0 ∧ i+1=_) at f; unfold consecutive; omega
  let p : Fin 6 := ⟨i,by omega⟩
  let q : Fin 6 := ⟨j,by omega⟩
  have changeIndex : p=q ∨ consecutive R.length p.val q.val := ord.imp Fin.ext id
  obtain ⟨t,ht,free⟩ := freePositions ⟨R.length,by omega⟩ p q d hi hj changeIndex
  have ip (l : Nat) : (t.val+l)%R.length < R.length := Nat.mod_lt _ (by omega)
  let get (l : Nat) := R[(t.val+l)%R.length]'(ip l)
  have outside (j : Fin 3) : A (get j.val)=false := by
    cases e : A (get j.val) with
    | false => rfl
    | true =>
      have o := only (get j.val) (List.getElem_mem _) ((selected _).mpr e)
      obtain ⟨f,g⟩ := free j
      rcases o with eq|eq
      · exact False.elim (f (inj (ip _) hi (eq.trans ei.symm)))
      · exact False.elim (g (inj (ip _) hj (eq.trans ej.symm)))
  have side (j : Nat) : (get j,get (j+1))∈sides R := by
    have e := side_at R ((t.val+j)%R.length) (ip j)
    have nextIndex : next R.length ((t.val+j)%R.length)=(t.val+(j+1))%R.length := by
      unfold next; rcases d with e|e <;> simp only [e] <;> split <;> omega
    exact List.mem_iff_getElem.mpr ⟨_,by simpa [sides_size] using ip j,by simpa only [get,nextIndex] using e⟩
  have different : get 0≠get 2 := by
    intro eq; have same := inj (ip 0) (ip 2) eq
    rcases d with e|e <;> simp only [e] at same <;> omega
  exact ⟨get 0,get 1,get 2,different,outside 0,outside 1,outside 2,side 0,side 1⟩

end DiskFullerene.EndSix
