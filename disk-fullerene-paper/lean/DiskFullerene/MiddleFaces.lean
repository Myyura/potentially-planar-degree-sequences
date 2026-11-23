import DiskFullerene.Middle

namespace DiskFullerene.Dual
open EndLabels Separation

theorem link_triangle_length {α : Type} {row : List α} (nd : row.Nodup) (sz : 3≤row.length)
    {a b c : α} (ab : a≠b) (bc : b≠c) (ca : c≠a) (A : a∈row)
    (one : OnCycle row a b) (two : OnCycle row b c) (three : OnCycle row c a) : row.length≤3 := by
  have member {a b} (e : OnCycle row a b) : a∈row ∧ b∈row := by
    rcases e with d|d
    · exact endsOfWordSide d
    · exact (endsOfWordSide d).symm
  have atMost {v x y z} (vx : OnCycle row v x) (vy : OnCycle row v y) (vz : OnCycle row v z) :
      x=y ∨ x=z ∨ y=z := by
    obtain ⟨_,_,_,_,_,_,_,lim⟩ := cycle_at nd sz (member vx).1
    have := lim _ vx; have := lim _ vy; have := lim _ vz
    grind
  apply nd.length_le_of_subset (l₂:=[a,b,c])
  intro x xmem
  have walk := traverseWord row id (OnCycle row) (fun _ _ e => e.symm)
    (fun _ _ e => Walk.step .refl (Or.inl e)) A xmem
  change Walk (OnCycle row) a x at walk
  induction walk with
  | refl => simp
  | @step i j _ edge ih =>
    have choices := ih (member edge).1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at choices ⊢
    rcases choices with rfl|rfl|rfl
    · have := atMost one three.symm edge; grind
    · have := atMost one.symm two edge; grind
    · have := atMost two.symm three edge; grind

private theorem corner_across_link {M} (G : IsDiskFullerene M h) {v a b : Face M}
    (p : OnCycle (dualRow G v) a b) : OnCycle (dualRow G a) v b := by
  rcases p with f|f
  · exact Or.inr (turn_triangle G f).1
  · exact Or.inl (turn_triangle G f).2

/-- An ordinary triangular face with three boundary vertices cannot
use two consecutive edges of the outer neighbor cycle. They and the
apex would close the full neighbor cycle at the middle vertex at degree 3. -/
theorem no_two_outer_sides {M} (G : IsDiskFullerene M h) (hh : 3≤h) (u : Fin M.ord)
    {a b c : Face M} (au : a∈triangle u) (bu : b∈triangle u) (cu : c∈triangle u)
    (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (A : IsBoundary G a) (B : IsBoundary G b) (C : IsBoundary G c)
    (one : OnCycle (dualRow G (apex M)) a b) (two : OnCycle (dualRow G (apex M)) b c) : False := by
  obtain ⟨l,r,K,lr,lb,rb,marks⟩ := corners_at G hh ((mem_triangle _ _).mp bu)
  have step := K.step
  have am := (marks a).mp ((mem_triangle _ _).mp au)
  have cm := (marks c).mp ((mem_triangle _ _).mp cu)
  have mid : OnCycle (dualRow G b) a c := by
    rcases am with no|rfl|rfl <;> rcases cm with no'|eq|eq <;> first | contradiction | exact eq ▸ Or.inl step | exact eq ▸ Or.inr step | grind [OnCycle]
  have aW : a≠apex M := fun eq => row_no_loop G hh _ (eq ▸ A)
  have cW : c≠apex M := fun eq => row_no_loop G hh _ (eq ▸ C)
  have degree := inner_degree G (show b≠apex M from fun eq => row_no_loop G hh _ (eq ▸ B))
  have corner1 := corner_across_link G one.symm
  have corner2 := corner_across_link G two
  have start : a∈dualRow G b := by
    rcases mid with m|m
    · exact (endsOfWordSide m).1
    · exact (endsOfWordSide m).2
  have short := link_triangle_length (row_nodup G (noRepeatOnSphere G hh) b) (by omega)
    aW (Ne.symm cW) ac.symm start corner1.symm corner2 mid.symm
  omega

end DiskFullerene.Dual
