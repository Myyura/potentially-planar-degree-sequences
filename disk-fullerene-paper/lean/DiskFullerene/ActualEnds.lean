import DiskFullerene.ActualChords
import DiskFullerene.Laminar

namespace DiskFullerene.Dual
open Dissection

private theorem atSide_surj {M} (G : IsDiskFullerene M h) (w : Face M) {x}
    (hx : x ∈ dualRow G w) : ∃ i, atSide G w i = x := by
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hx
  have ok : k < M.faces[w.val].length := by simpa [row_length] using hk
  exact ⟨⟨k,ok⟩,(atSide_eq G w _).trans eq⟩

private theorem atSide_succ {M} (G : IsDiskFullerene M h) (w : Face M)
    (i j : Fin M.faces[w.val].length) (step : next M.faces[w.val].length i.val=j.val) :
    (atSide G w i, atSide G w j) ∈ sides (dualRow G w) := by
  let r := dualRow G w
  have hi : i.val<r.length := by simp [r,row_length]
  have hj : next r.length i.val=j.val := by simpa [r,row_length] using step
  have e := side_at r i.val hi
  have mem := List.getElem_mem (l:=sides r) (n:=i.val) (by rwa [sides_size])
  rw [e] at mem
  have hjBound : j.val<r.length := by simp [r,row_length]
  have nxt : r[next r.length i.val]'(next_bound hi) = r[j.val] := congrArg (fun k : Fin r.length => r[k.val]) (show (⟨_,next_bound hi⟩ : Fin r.length)=⟨_,hjBound⟩ from Fin.ext hj)
  rw [nxt] at mem
  simpa [atSide_eq,r] using mem

/-- Every boundary chord is in the dissection with its actual endpoints. -/
theorem indexed_chord {M} (G : IsDiskFullerene M h) (hh : 3≤h) {x y}
    (hx : IsBoundary G x) (hy : IsBoundary G y) (e : y∈dualRow G x)
    (xy : (x,y)∉sides (dualRow G (apex M))) (yx : (y,x)∉sides (dualRow G (apex M))) :
    ∃ i j : Fin M.faces[(apex M).val].length, Chord.mk i.val j.val ∈ chords G ∧
      ((atSide G (apex M) i=x ∧ atSide G (apex M) j=y) ∨
       (atSide G (apex M) i=y ∧ atSide G (apex M) j=x)) := by
  let w := apex M
  let n := M.faces[w.val].length
  let N := atSide G w
  obtain ⟨i,rfl⟩ := atSide_surj G w hx
  obtain ⟨j,rfl⟩ := atSide_surj G w hy
  have ne : i≠j := fun eq => row_no_loop G hh _ (eq ▸ e)
  have orient (a b : Fin n) (lt : a.val<b.val) (edge : N b∈dualRow G (N a))
      (fwd : (N a,N b)∉sides (dualRow G w)) (back : (N b,N a)∉sides (dualRow G w)) :
      Chord.mk a.val b.val ∈ chords G := by
    have ab := a.isLt
    have bb := b.isLt
    have gap : a.val+1<b.val := by
      apply Classical.byContradiction; intro fail
      exact fwd (atSide_succ G w a b (by change (if a.val+1<n then a.val+1 else 0)=b.val; split <;> omega))
    have wrap : a.val≠0 ∨ b.val+1<n := by
      by_cases zero : a.val=0
      · right
        apply Classical.byContradiction; intro fail
        exact back (atSide_succ G w b a (by change (if b.val+1<n then b.val+1 else 0)=a.val; simp [fail,zero]))
      · exact Or.inl zero
    have outside : ∃ t, t<n ∧ (t<a.val ∨ b.val<t) := by
      rcases wrap with nz|more
      · exact ⟨0,by omega,Or.inl (by omega)⟩
      · exact ⟨b.val+1,more,Or.inr (by omega)⟩
    exact (mem_chords G _).mpr
      ⟨a,b,rfl,rfl,⟨lt,ab,bb,⟨a.val+1,Nat.lt_trans gap bb,Nat.lt_succ_self _,gap⟩,outside⟩,edge⟩
  by_cases lt : i.val < j.val
  · exact ⟨i,j,orient i j lt e xy yx,Or.inl ⟨rfl,rfl⟩⟩
  · have neq : i.val≠j.val := fun q => ne (Fin.ext q)
    exact ⟨j,i,orient j i (by omega) ((dual_adj_symmetric G _ _).mp e) yx xy,Or.inr ⟨rfl,rfl⟩⟩

theorem chords_nonempty {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : HasChord G) :
    ∃ c, c∈chords G := by
  obtain ⟨_,hx,_,hy,e,xy,yx⟩ := hc
  obtain ⟨_,_,c,_⟩ := indexed_chord G hh hx hy e xy yx
  exact ⟨_,c⟩

theorem multiple_regions {M} (G : IsDiskFullerene M h) (hh : 22≤h) (hs : M.hexagons≤6) :
    2 ≤ cellCount (chordCuts G (by omega)) := by
  obtain ⟨_,hm⟩ := chords_nonempty G (by omega) (chord_above_twenty_one G hh hs)
  have pos := List.length_pos_of_mem hm
  rw [number_of_regions]
  omega

end DiskFullerene.Dual
