import DiskFullerene.Extremal

namespace DiskFullerene.Dual
open EndEuler

/-- All actual ends of an equality graph with a chord. Every chord
separates these same two ends, including chords meeting at a vertex. -/
theorem equality_chain {M} (G : IsDiskFullerene M h) (hh : 3≤h) (chord : HasChord G)
    (six : M.hexagons=6) :
    ∃ d e : EndPiece M G,
      let p := vertexSide d.seam d.side
      let q := vertexSide e.seam e.side
      (∀ f, f∈diskInterior G ↔ sectorCore d.seam d.side f=true ∨ sectorCore e.seam e.side f=true) ∧
      (∀ r, TerminalHalf G r ↔ r=p ∨ r=q) ∧
      (∀ f, ChordHalf G f → ∃ s : Bool, (∀ v, p v=true → f v=s) ∧ (∀ v, q v=true → f v= !s)) := by
  classical
  obtain ⟨d,e,A,ds,es⟩ := equality_ends G hh chord six
  let p := vertexSide d.seam d.side
  let q := vertexSide e.seam e.side
  have cover := exact_end_cover hh d e A ds es six
  have all (r) (R : TerminalHalf G r) : r=p ∨ r=q := by
    obtain ⟨t,rfl⟩ := EndPiece.of_half R
    obtain ⟨j,hit⟩ := t.nonempty hh
    have core : j∈diskInterior G := of_decide_eq_true (Bool.and_eq_true_iff.mp hit).1
    obtain ⟨u,v,corner⟩ := face_dart G hh j
    let vtx : Fin M.ord := ⟨u,(dart_info G (incident_dart G corner)).1⟩
    have touch : vtx.val∈M.faces[j.val] := (sideEnds corner).1
    have yes := core_corner_selected t.seam hit vtx touch
    rcases (cover j).mp core with left|right
    · exact Or.inl (R.eq_of_overlap d.terminal yes (core_corner_selected d.seam left vtx touch))
    · exact Or.inr (R.eq_of_overlap e.terminal yes (core_corner_selected e.seam right vtx touch))
  refine ⟨d,e,cover,fun r => ⟨all r,?_⟩,?_⟩
  · rintro (rfl|rfl)
    · exact d.terminal
    · exact e.terminal
  · intro f F
    obtain ⟨a,left⟩ := d.terminal.2 f F
    obtain ⟨b,right⟩ := e.terminal.2 f F
    change ∀ v, p v=true → f v=a at left
    change ∀ v, q v=true → f v=b at right
    have witness (r) (R : TerminalHalf G r) (bound : ∀ v, r v=true → f v≠a) : b≠a := by
      obtain ⟨k,yes⟩ := R.1.some_vertex
      have no := bound k yes
      rcases all r R with eq|eq <;> subst r
      · exact False.elim (no (left k yes))
      · exact fun h => no ((right k yes).trans h)
    have diff : b≠a := by
      cases a
      · obtain ⟨r,R,incl⟩ := F.contains_terminal hh
        obtain ⟨v,rv⟩ := R.1.some_vertex
        have fv := incl v rv
        rcases all r R with eq|eq <;> subst r
        · have off := left v rv; grind
        · have bv := right v rv; grind
      · obtain ⟨r,R,incl⟩ := F.complement.contains_terminal hh
        obtain ⟨v,rv⟩ := R.1.some_vertex
        have fv := incl v rv
        rcases all r R with eq|eq <;> subst r
        · have off := left v rv; simp_all
        · have bv := right v rv; simp_all
    refine ⟨a,left,?_⟩
    have opp : b= !a := by cases b <;> cases a <;> simp_all
    simpa only [opp] using right

end DiskFullerene.Dual
