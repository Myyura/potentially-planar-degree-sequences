import FlagRotation
import Overlay
import LeanPool.K5MinorFreeChoosability.Planar.MinorClosed

/-! Place the computed patch overlay in the incidence graph using permanent
corner names, edge names, and read-row indices. Only cells occurring in the
prefix need names in the ambient finite incidence table. -/
namespace Recognition.OverlayMinor
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep Recognition.Overlay
open LeanPool.K5MinorFreeChoosability

private def seen (fs : List Face) (e : Edge) := ∃ i : Id fs, e∈flags fs i

def observed (fs : List Face) : Node (Id fs) → Prop
  | .vertex v => ∃ e, seen fs e ∧ touches e v
  | .point e => seen fs e
  | .centre _ => True

private theorem has_seen {fs : List Face} {e : Edge} (h : 0 < occurrences (fs.flatMap Face.sides) e) : seen fs e := by
  obtain ⟨a,m,eq⟩ := List.mem_map.mp (List.count_pos_iff.mp h)
  obtain ⟨f,hf,sa⟩ := List.mem_flatMap.mp m
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hf
  exact ⟨i,List.mem_map.mpr ⟨a,hi ▸ sa,eq⟩⟩

private theorem real_cell (fs : List Face) (s : Inventory) (ok : replay (fs.flatMap Face.sides)=some s)
    {x a} (m : a∈vertices fs s) (assigned : site fs (retained s) x = some a) : observed fs x := by
  have acc := replay_accurate ok
  have pend (e) (h : e∈s.pending) : seen fs e := has_seen (by have := (acc.pending e).mp h; omega)
  have kept (e) (h : e∈retained s) : seen fs e := by
    simp only [retained,List.mem_eraseDups,List.mem_append] at h
    rcases h with h|h
    · exact pend _ h
    · have h' := (acc.sealed e).mp (List.mem_filter.mp h).1
      exact has_seen (by omega)
  cases x with
  | centre i => trivial
  | point e =>
    by_cases h : e∈retained s
    · exact kept _ h
    by_contra! no
    change ¬∃ i, e∈flags fs i at no
    simp [site,h,no] at assigned
  | vertex v =>
    have eq : a = .vertex v := Option.some.inj assigned.symm
    subst a
    simp [vertices,activeNames,List.mem_flatMap] at m
    obtain ⟨e,he,eq⟩ := m
    exact ⟨e,pend _ he,by simpa [touches] using eq⟩

def shadow (fs : List Face) (s : Inventory) : SimpleGraph {a // a∈vertices fs s} where
  Adj a b := a ≠ b ∧ ((a.val,b.val)∈edges fs s ∨ (b.val,a.val)∈edges fs s)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A permanent-name embedding of the read cells into a host. Edges outside
the triangular trace need no witnesses. -/
structure Placement (fs : List Face) (H : SimpleGraph U) where
  name : Node (Id fs) → U
  injective : ∀ x y, observed fs x → observed fs y → name x=name y → x=y
  incident : ∀ x y, observed fs x → observed fs y → flagAdj fs x y → H.Adj (name x) (name y)

theorem shadow_planar [Finite U] (fs : List Face) (s : Inventory) (ok : replay (fs.flatMap Face.sides)=some s)
    (H : SimpleGraph U) (flat : IsPlanar H) (place : Placement fs H) : IsPlanar (shadow fs s) := by
  classical
  let _ := Fintype.ofFinite U
  let M := branchModel fs s
  let vs := vertices fs s
  let W := {a // a∈vs}
  let bags (a : W) := Finset.univ.filter (fun u : U => ∃ x, M.branch x=some a.val ∧ place.name x=u)
  have bag (a : W) (u : U) : u∈bags a ↔ ∃ x, M.branch x=some a.val ∧ place.name x=u := by simp [bags]
  have member (a : W) {x} (h : M.branch x=some a.val) : place.name x∈bags a := (bag ..).mpr ⟨x,h,rfl⟩
  have valid (a : W) {x} (h : M.branch x=some a.val) : observed fs x :=
    real_cell fs s ok a.property (by simpa only [M,branch_assignment] using h)
  have nonempty (a : W) : (bags a).Nonempty := by
    obtain ⟨x,h⟩ := M.nonempty _ a.property
    exact ⟨_,member a h⟩
  apply isPlanar_of_minorModel flat
  refine ⟨bags,nonempty,?_,?_,?_⟩
  · intro a
    apply (connSet_iff_induce_connected ..).mp
    refine ⟨nonempty a,?_⟩
    intro x hx y hy
    obtain ⟨u,hu,rfl⟩ := (bag a x).mp hx
    obtain ⟨v,hv,rfl⟩ := (bag a y).mp hy
    have walk := M.connected a.val a.property u v hu hv
    clear hv hy
    induction walk with
    | refl => exact RIn.refl _
    | step _ step ih =>
      exact Relation.ReflTransGen.tail ih ⟨place.incident _ _ (valid a step.2.1) (valid a step.2.2) step.1,
        member a step.2.1,member a step.2.2⟩
  · intro a b ne
    apply Finset.disjoint_left.mpr
    intro z za zb
    obtain ⟨x,hx,px⟩ := (bag a _).mp za
    obtain ⟨y,hy,py⟩ := (bag b _).mp zb
    have eq := place.injective _ _ (valid a hx) (valid b hy) (px.trans py.symm)
    subst y
    exact ne (Subtype.ext (Option.some.inj (hx.symm.trans hy)))
  · intro a b adj
    have realize (i j : W) (h : (i.val,j.val)∈edges fs s) :
        ∃ x∈bags i, ∃ y∈bags j, H.Adj x y := by
      obtain ⟨u,v,hu,hv,edge⟩ := M.realize _ _ h
      exact ⟨_,member i hu,_,member j hv,place.incident _ _ (valid i hu) (valid j hv) edge⟩
    rcases adj.2 with dir|rev
    · exact realize a b dir
    · obtain ⟨y,hy,x,hx,h⟩ := realize b a rev
      exact ⟨x,hx,y,hy,h.symm⟩

#print axioms shadow_planar
end Recognition.OverlayMinor
