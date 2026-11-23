import Std

namespace DiskFullerene.Lower

/-- A polygon cut at the triangle on its base. A side with no triangle
attached is just an edge. Labels run consecutively from left to right.
The outer base joins the two extreme labels. -/
inductive Polygon where
  | edge
  | triangle (left right : Polygon)
  deriving DecidableEq

namespace Polygon

def width : Polygon → Nat
  | .edge => 1
  | .triangle l r => l.width + r.width

theorem width_pos (p : Polygon) : 0 < p.width := by
  induction p with
  | edge => decide
  | triangle l r hl hr => simp only [width]; omega

private def join (a b x y : Nat) : Prop :=
  (x = a ∧ y = b) ∨ (x = b ∧ y = a)

/-- The actual edges, including the base; the two subpolygons share a vertex. -/
def adj : Polygon → Nat → Nat → Nat → Prop
  | .edge, a, x, y => join a (a+1) x y
  | .triangle l r, a, x, y =>
    join a (a + (l.width + r.width)) x y ∨ l.adj a x y ∨ r.adj (a+l.width) x y

theorem base (p : Polygon) (a : Nat) : p.adj a a (a+p.width) := by
  cases p <;> simp [adj, width, join]

theorem bounds (p : Polygon) (a x y : Nat) (e : p.adj a x y) :
    a ≤ x ∧ x ≤ a + p.width ∧ a ≤ y ∧ y ≤ a + p.width := by
  induction p generalizing a with
  | edge => simp [adj, join] at e; simp only [width]; omega
  | triangle l r ihl ihr =>
    simp only [adj, join] at e
    simp only [width]
    rcases e with e | el | er
    · omega
    · have := ihl a el; omega
    · have := ihr (a+l.width) er; omega

/-- A vertex with two distinct adjacent neighbors and no other neighbor. -/
def IsEar (p : Polygon) (a v : Nat) : Prop :=
  ∃ x y, x ≠ y ∧ p.adj a x y ∧ ∀ w, p.adj a v w ↔ w = x ∨ w = y

private theorem lift_left {l : Polygon} (r : Polygon) {a v : Nat}
    (left : a < v) (right : v < a + l.width) (ear : l.IsEar a v) :
    (triangle l r).IsEar a v := by
  obtain ⟨x,y,ne,xy,whole⟩ := ear
  refine ⟨x,y,ne, Or.inr (Or.inl xy), fun w => ⟨?_,?_⟩⟩
  · intro e
    rcases e with base | el | er
    · unfold join at base; omega
    · exact (whole w).1 el
    · have := r.bounds _ _ _ er; omega
  · intro hw; exact Or.inr (Or.inl ((whole w).2 hw))

private theorem lift_right (l : Polygon) {r : Polygon} {a v : Nat}
    (left : a+l.width < v) (right : v < a+l.width+r.width) (ear : r.IsEar (a+l.width) v) :
    (triangle l r).IsEar a v := by
  obtain ⟨x,y,ne,xy,whole⟩ := ear
  refine ⟨x,y,ne, Or.inr (Or.inr xy), fun w => ⟨?_,?_⟩⟩
  · intro e
    rcases e with base | el | er
    · unfold join at base; omega
    · have := l.bounds _ _ _ el; omega
    · exact (whole w).1 er
  · intro hw; exact Or.inr (Or.inr ((whole w).2 hw))

private theorem left_tip (r : Polygon) (a : Nat) :
    (triangle edge r).IsEar a a := by
  refine ⟨a+1, a+(1+r.width), by have := r.width_pos; omega, ?_, fun w => ?_⟩
  · exact Or.inr (Or.inr (by simpa [width, Nat.add_assoc] using r.base (a+1)))
  have rwid := r.width_pos
  constructor
  · intro e
    rcases e with b | el | er
    · unfold join at b; simp only [width] at b; omega
    · change join a (a+1) a w at el; unfold join at el; omega
    · have h := r.bounds _ _ _ er; simp only [width] at h; omega
  · intro e; rcases e with rfl | rfl
    · exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)

private theorem right_tip (l : Polygon) (a : Nat) :
    (triangle l edge).IsEar a (a+(l.width+1)) := by
  refine ⟨a, a+l.width, by have := l.width_pos; omega, Or.inr (Or.inl (l.base a)), fun w => ?_⟩
  have lwid := l.width_pos
  constructor
  · intro e
    rcases e with b | el | er
    · unfold join at b; simp only [width] at b; omega
    · have := l.bounds _ _ _ el; omega
    · change join (a+l.width) (a+l.width+1) _ w at er; unfold join at er; omega
  · intro e; rcases e with rfl | rfl
    · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))

/-- Every triangulated polygon has an ear different from both endpoints of
any designated base edge. -/
theorem ear_off_base (p : Polygon) (a : Nat) (nonempty : p ≠ edge) :
    ∃ v, a < v ∧ v < a + p.width ∧ p.IsEar a v := by
  induction p generalizing a with
  | edge => exact False.elim (nonempty rfl)
  | triangle l r ihl ihr =>
    have hl := l.width_pos
    have hr := r.width_pos
    by_cases ln : l = edge
    · subst l
      by_cases rn : r = edge
      · subst r
        refine ⟨a+1, by omega, by simp [width], a, a+2, by omega, ?_, ?_⟩
        · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        · intro w
          simp [adj, width, join]
      · obtain ⟨v,lo,hi,ear⟩ := ihr (a+1) rn
        refine ⟨v, by omega, by simp only [width]; omega, lift_right edge (by exact lo) hi ear⟩
    · obtain ⟨v,lo,hi,ear⟩ := ihl a ln
      exact ⟨v, lo, by simp only [width]; omega, lift_left r lo hi ear⟩

/-- Two distinct ears, including the case of a single triangular face. -/
theorem two_distinct_ears (p : Polygon) (a : Nat) (nonempty : p ≠ edge) :
    ∃ u v, u ≠ v ∧ p.IsEar a u ∧ p.IsEar a v := by
  cases p with
  | edge => exact False.elim (nonempty rfl)
  | triangle l r =>
    obtain ⟨u, hu, eu⟩ : ∃ u, u < a+l.width ∧ (triangle l r).IsEar a u := by
      by_cases l0 : l = edge
      · subst l; exact ⟨a, by simp [width], left_tip r a⟩
      · obtain ⟨u,lo,hi,ear⟩ := ear_off_base l a l0
        exact ⟨u, hi, lift_left r lo hi ear⟩
    obtain ⟨v, hv, ev⟩ : ∃ v, a+l.width < v ∧ (triangle l r).IsEar a v := by
      by_cases r0 : r = edge
      · subst r; exact ⟨_, by omega, right_tip l a⟩
      · obtain ⟨v,lo,hi,ear⟩ := ear_off_base r (a+l.width) r0
        exact ⟨v, lo, lift_right l lo hi ear⟩
    exact ⟨u,v,by omega, eu,ev⟩

theorem IsEar.degree_two {p : Polygon} {a v : Nat} (h : p.IsEar a v)
    (row : List Nat) (nd : row.Nodup) (neighbors : ∀ w, w ∈ row ↔ p.adj a v w) :
    row.length = 2 := by
  obtain ⟨x,y,ne,_,adjacent⟩ := h
  have equiv (w : Nat) : w ∈ row ↔ w ∈ [x,y] := by simpa using (neighbors w).trans (adjacent w)
  have yin : ([x,y] : List Nat).Nodup := by simpa using ne
  have lo := yin.length_le_of_subset (fun w hw => (equiv w).2 hw)
  have hi := nd.length_le_of_subset (fun w hw => (equiv w).1 hw)
  simp at lo hi
  omega

/-- An outer-triangulated leaf of the induced graph cannot occur when the
whole-disk degree is at least five and at most two exterior neighbors occur
at an ear other than the single attachment vertex. -/
theorem exclude_polygon_leaf (p : Polygon) (a cut : Nat) (nonempty : p ≠ edge)
    (rows : Nat → List Nat) (outside : Nat → Nat)
    (rowOK : ∀ v, p.IsEar a v → v ≠ cut →
      (rows v).Nodup ∧ ∀ w, w ∈ rows v ↔ p.adj a v w)
    (degree : ∀ v, p.IsEar a v → v ≠ cut → 5 ≤ (rows v).length + outside v)
    (runBound : ∀ v, p.IsEar a v → v ≠ cut → outside v ≤ 2) : False := by
  obtain ⟨u,v,ne,eu,ev⟩ := two_distinct_ears p a nonempty
  obtain ⟨w,ew,hc⟩ : ∃ w, p.IsEar a w ∧ w ≠ cut := by
    by_cases h : u = cut
    · exact ⟨v,ev,by omega⟩
    · exact ⟨u,eu,h⟩
  obtain ⟨nd,spec⟩ := rowOK w ew hc
  have := ew.degree_two (rows w) nd spec
  have := degree w ew hc
  have := runBound w ew hc
  omega

end Polygon
end DiskFullerene.Lower
