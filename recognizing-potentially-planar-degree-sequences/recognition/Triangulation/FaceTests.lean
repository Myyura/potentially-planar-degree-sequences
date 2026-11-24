import Triangulation.Stacking

/-! Geometric choices for a forward test. Both the omitted faces from the
preceding test and the test edges may be chosen in the same actual map. -/
namespace Recognition.FaceTests
open Rigidity Stacking

private theorem has_star {V : Type} (M : Map V) (fill : Choice V)
    (disjoint : ∀ a b c d e, vacant M fill a b c → vacant M fill a d e →
      (b=d ∧ c=e) ∨ (b=e ∧ c=d)) {x y : V} (adj : M.adj x y) :
    ∃ s : Star M fill, (stack M fill).face (.inl x) (.inl y) (.inr s) := by
  obtain ⟨c,f⟩ := adj
  obtain ⟨d,dc,g,_⟩ := M.twoSides f
  have pick : fill (corners x y c) ∨ fill (corners x y d) := by
    apply Classical.byContradiction
    intro both
    have hc : ¬fill (corners x y c) := fun h => both (Or.inl h)
    have hd : ¬fill (corners x y d) := fun h => both (Or.inr h)
    have two := disjoint x y c y d ⟨f,hc⟩ ⟨g,hd⟩
    have ne := M.distinct (M.rot f)
    grind
  rcases pick with h|h
  · exact ⟨⟨corners x y c,⟨x,y,c,f,rfl⟩,h⟩,M.distinct f,Or.inl rfl,Or.inr (Or.inl rfl)⟩
  · exact ⟨⟨corners x y d,⟨x,y,d,g,rfl⟩,h⟩,M.distinct g,Or.inl rfl,Or.inr (Or.inl rfl)⟩

/-- A matching of old test edges can be covered by disjoint current faces,
one latest-generation auxiliary per edge, after any disjoint-face omission. -/
theorem matching_faces {V I : Type} (M : Map V) (fill : Choice V)
    (previous : ∀ a b c d e, vacant M fill a b c → vacant M fill a d e →
      (b=d ∧ c=e) ∨ (b=e ∧ c=d))
    (x y : I → V) (edge : ∀ i, M.adj (x i) (y i))
    (separate : ∀ i j, i≠j →
      x i≠x j ∧ x i≠y j ∧ y i≠x j ∧ y i≠y j) :
    ∃ h : I → Star M fill,
      (∀ i, (stack M fill).face (.inl (x i)) (.inl (y i)) (.inr (h i))) ∧
      ∀ i j, h i = h j → i=j := by
  classical
  let choose i := has_star M fill previous (edge i)
  let h i := (choose i).choose
  have existsFace i := (choose i).choose_spec
  refine ⟨h,existsFace,?_⟩
  intro i j eq
  apply Classical.byContradiction
  intro ne
  have ⟨xx,xy,yx,yy⟩ := separate i j ne
  have a := existsFace i
  have b := existsFace j
  change x i ≠ y i ∧ (h i).val (x i) ∧ (h i).val (y i) at a
  change x j ≠ y j ∧ (h j).val (x j) ∧ (h j).val (y j) at b
  rw [← eq] at b
  obtain ⟨u,v,w,_,key⟩ := (h i).property.1
  rw [key] at a b
  simp only [corners] at a b
  grind

/-- The three preparation layers may name a distinct generation-two vertex
for every original edge, even if many of the edges share an endpoint. -/
theorem prepare_markers {V I : Type} (M : Map V) (x y : I → V)
    (edge : ∀ i, M.adj (x i) (y i))
    (distinctEdges : ∀ i j, ((x i=x j ∧ y i=y j) ∨ (x i=y j ∧ y i=x j)) → i=j) :
    let M₁ := stack M (fun _ => True)
    let M₂ := stack M₁ (fun _ => True)
    ∃ marker : I → Star M₁ (fun _ => True),
      (∀ i j, marker i = marker j → i=j) ∧
      ∀ i v, M₂.adj (.inr (marker i)) (.inl (.inl v)) ↔ v=x i ∨ v=y i := by
  classical
  intro M₁ M₂
  have all (a b c d e : V) (g : vacant M (fun _ => True) a b c) :
      vacant M (fun _ => True) a d e → (b=d ∧ c=e) ∨ (b=e ∧ c=d) := False.elim (g.2 trivial)
  let select i := has_star M (fun _ => True) all (edge i)
  let aux i := (select i).choose
  let key i : Vertex M (fun _ => True) → Prop :=
    corners (.inl (x i)) (.inl (y i)) (.inr (aux i))
  let marker i : Star M₁ (fun _ => True) :=
    ⟨key i,⟨_,_,_,(select i).choose_spec,rfl⟩,trivial⟩
  have read (i : I) (v : V) :
      M₂.adj (.inr (marker i)) (.inl (.inl v)) ↔ v=x i ∨ v=y i := by
    rw [star_neighbors M₁ (fun _ => True)]
    simp [marker,key,corners]
  refine ⟨marker,?_,read⟩
  intro i j same
  have member (v : V) : (v=x i ∨ v=y i) ↔ (v=x j ∨ v=y j) := by
    rw [← read i, ← read j, same]
  have diff (a : I) : x a≠y a := by obtain ⟨_,f⟩ := edge a; exact M.distinct f
  apply distinctEdges
  have a := member (x i)
  have b := member (y i)
  have := diff i
  grind

end Recognition.FaceTests
