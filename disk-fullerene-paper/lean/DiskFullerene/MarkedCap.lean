import DiskFullerene.FanPentagon

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels Separation

private theorem cofacial_neighbor {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u : Fin M.ord} {a b : Face M}
    (ai : a∈triangle u) (bi : b∈triangle u) (ne : a≠b) : b∈dualRow G a := by
  obtain ⟨y,z,C,_,_,_,fs⟩ := corners_at G hh ((mem_triangle u a).mp ai)
  have side := C.step
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp side; rw [sides_size] at hk; rw [side_at _ _ hk] at eq
  rcases (fs b).mp ((mem_triangle u b).mp bi) with q|rfl|rfl
  · exact False.elim (ne q.symm)
  · exact (Prod.mk.inj eq).1 ▸ List.getElem_mem _
  · exact (Prod.mk.inj eq).2 ▸ List.getElem_mem _

namespace TerminalAnnulus
variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

/-- The marked edge is one of the two segments in the unique split fan. -/
theorem seam_segment (T : TerminalAnnulus d) (hh : 3≤h) {i z} (split : (T.fans.arc i).mid=some z) :
    ∃ s : Bool, let strong := if s then T.junction (after i) else T.junction i
               let x := atSide G (apex M) d.i; let y := atSide G (apex M) d.j
               (z=x ∧ strong=y) ∨ (z=y ∧ strong=x) := by
  let W := T.W
  let r := W.rim i; let x := atSide G (apex M) d.i; let y := atSide G (apex M) d.j
  obtain ⟨ne,af,bf,cf,l₁,l₂⟩ := T.fans.fan_run hh split
  obtain ⟨mark,v,_,_,vr,allv⟩ := terminal_run hh d.seam d.side d.terminal (T.rim_in i) ne af bf cf l₁ l₂
  have poleNb (a : OuterIndex M) : IsBoundary G (atSide G (apex M) a) := by unfold IsBoundary; rw [atSide_eq]; exact List.getElem_mem _
  have xB := poleNb d.i; have yB := poleNb d.j
  have dis (q : Face M) (b : IsBoundary G q) : q≠r := by intro eq; change q=T.W.rim i at eq; exact (mem_diskInterior G _).mp (core_disk (T.rim_in i)) |>.2 (eq ▸ b)
  have xy : x≠y := fun e=> (Nat.ne_of_lt d.proper.1) (congrArg Fin.val (atSide_inj G hh _ e))
  have mx : x∈triangle v := by
    apply Classical.byContradiction; intro missing
    have sub : triangle v⊆[r,y] := by intro f m; have f3 := allv f ((mem_triangle v f).mp m); change f=r ∨ f=x ∨ f=y at f3; simp; grind
    have le := (show (triangle v).Nodup from (List.nodup_finRange _).filter _).length_le_of_subset sub
    rw [triangle_three G hh] at le; simp at le
  have my : y∈triangle v := by
    apply Classical.byContradiction; intro missing
    have sub : triangle v⊆[r,x] := by intro f m; have f3 := allv f ((mem_triangle v f).mp m); change f=r ∨ f=x ∨ f=y at f3; simp; grind
    have le := (show (triangle v).Nodup from (List.nodup_finRange _).filter _).length_le_of_subset sub
    rw [triangle_three G hh] at le; simp at le
  have inArc (q : Face M) (b : IsBoundary G q) (touch : q ∈triangle v) : q=T.junction i ∨ q=z ∨ q=T.junction (after i) := by
    have qr := cofacial_neighbor G hh ((mem_triangle _ _).mpr vr) touch (Ne.symm (dis q b))
    have u := (T.fans.neighbors i).mem_iff.mpr qr
    have off (f : Face M) (h : sectorCore d.seam d.side f=true) : q≠f := fun eq=>(mem_diskInterior G _).mp (core_disk h) |>.2 (eq ▸ b)
    have c0 := off W.center ((W.chosen _).mpr (.inl rfl)); have c1 := off _ (T.rim_in (after i)); have c2 := off _ (T.rim_in (before i))
    have joined := T.fans.joined hh i
    change q=(T.fans.arc i).first ∨ q=z ∨ q=(T.fans.arc (after i)).first
    simp only [Arc.word,split,Option.toList_some,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at u
    change q=T.W.rim (after i) ∨ q=T.W.center ∨ q=T.W.rim (before i) ∨ q=(T.fans.arc i).first ∨ q=z ∨ q=(T.fans.arc i).last at u
    change q≠T.W.center at c0; grind
  have xa := inArc x xB mx; have ya := inArc y yB my
  change z=x ∨ z=y at mark
  change ∃ s : Bool, (z=x ∧ (if s then T.junction (after i) else T.junction i)=y) ∨
    (z=y ∧ (if s then T.junction (after i) else T.junction i)=x)
  rcases mark with zx|zy
  · rcases ya with ya|ya|ya
    · exact ⟨false,Or.inl ⟨zx,ya.symm⟩⟩
    · exact False.elim (xy (zx.symm.trans ya.symm))
    · exact ⟨true,Or.inl ⟨zx,ya.symm⟩⟩
  · rcases xa with xa|xa|xa
    · exact ⟨false,Or.inr ⟨zy,xa.symm⟩⟩
    · exact False.elim (xy (xa.trans zy))
    · exact ⟨true,Or.inr ⟨zy,xa.symm⟩⟩

end TerminalAnnulus

/-- The cap is indexed using its actual center rotation; the split index
and the strong endpoint record its two possible plane orientations. -/
structure Cap {M} {G : IsDiskFullerene M h} (d : EndPiece M G) extends TerminalAnnulus d where
  index : I
  middle : Face M
  split : (fans.arc index).mid=some middle
  second : Bool
  seam : let strong := if second then toTerminalAnnulus.junction (after index) else toTerminalAnnulus.junction index
         let x := atSide G (apex M) d.i; let y := atSide G (apex M) d.j
         (middle=x ∧ strong=y) ∨ (middle=y ∧ strong=x)

noncomputable def markedCap {M} {G : IsDiskFullerene M h} {d : EndPiece M G} (hh : 7≤h) (T : TerminalAnnulus d) : Cap d := by
  let ex := T.has_subdivision hh; let k:=ex.choose; let z:=ex.choose_spec.choose
  let split : (T.fans.arc k).mid=some z := ex.choose_spec.choose_spec
  let choice := T.seam_segment (by omega) split
  exact ⟨T,k,z,split,choice.choose,choice.choose_spec⟩

namespace Cap
variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

/-- The entire triangular strip around the physical wheel is represented
by a single subdivision bit. Each physical rim row is oriented. -/
theorem rim_arc (C : Cap d) (hh : 3≤h) (j : I) :
    (C.fans.arc j).word=C.junction j :: (if j=C.index then [C.middle] else []) ++ [C.junction (after j)] := by
  have same (j : I) : (C.fans.arc j).mid=if j=C.index then some C.middle else none := by
    by_cases eq : j=C.index
    · simp [eq,C.split]
    · cases e : (C.fans.arc j).mid with
      | none => simp [eq]
      | some z => exact False.elim (eq (C.unique_split hh e C.split))
  have joined := C.fans.joined hh j; unfold Arc.word; rw [same,joined]; split <;> rfl

end Cap
end DiskFullerene.EndFans
