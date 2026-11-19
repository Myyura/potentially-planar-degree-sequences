import SparseBoundary.Cut
import SparseBoundary.GraphException
import SparseBoundary.GraphPerm
import SparseBoundary.GraphUniversalBases
import SparseBoundary.GraphFourRegularSeven
import SparseBoundary.GraphFiveFiveThree
import SparseBoundary.GraphThreeSixes

namespace SparseBoundary

/-- A normalized degree sequence. The parameters count entries of degree two and one. -/
def profile (h : List Nat) (t l : Nat) : List Nat :=
  h ++ (List.replicate t 2 ++ List.replicate l 1)

def Core (h : List Nat) : Prop :=
  h.Pairwise (· ≥ ·) ∧ ∀ x ∈ h, 3 ≤ x

def lowerException : List Nat := [4,4,4,4,4,2]

/-- The four alternatives of Theorem 2, for a normalized profile. -/
def UpperForbidden (h : List Nat) (t l : Nat) : Prop :=
  h.length = 5 ∨
  (∃ a b c, 4 ≤ c ∧ h = [a,b,c,3,3,3]) ∨
  profile h t l = (5+l)::([4,4,4,4,3] ++ List.replicate l 1) ∨
  profile h t l = (6+l)::([4,4,4,4,4,2] ++ List.replicate l 1) ∨
  profile h t l = (6+l)::([5,5,3,3,3,3] ++ List.replicate l 1) ∨
  profile h t l = [5,5,5,5,5,3,2,2] ∨
  profile h t l = [4,4,4,4,4,4,4] ∨
  profile h t l = [6,6,6,3,3,3,3,2]

/-- Full theorem statements, kept distinct from their proved directions. -/
def FirstBoundaryStatement : Prop :=
  ∀ d : List Nat, d ≠ [] → (∀ x ∈ d, 1 ≤ x) → Graphic d →
    d.sum + 2 + 2 * d.count 1 ≤ 4 * d.length →
    (Planaric d ↔ ¬ d.Perm lowerException)

def SecondBoundaryStatement : Prop :=
  ∀ (d h : List Nat) (t l : Nat), d ≠ [] → Core h → d.Perm (profile h t l) →
    Graphic d → d.sum + 2*l = 4*d.length →
    (¬ Planaric d ↔ UpperForbidden h t l)

/-- The lower exception is graphic, has the claimed sum, and is nonplanaric
    under every permutation of the labels. -/
theorem lower_exception_verified {d : List Nat} (hp : d.Perm lowerException) :
    Graphic d ∧ d.sum + 2 + 2 * d.count 1 = 4 * d.length ∧ ¬ Planaric d := by
  have he : d.count 1 = lowerException.count 1 := (List.perm_iff_count.mp hp) 1
  refine ⟨(graphic_perm hp).mpr Graph.exceptional_graphic,?_,?_⟩
  · rw [hp.sum_nat, hp.length_eq, he]; decide
  · exact fun h => Graph.exceptional_nonplanar ((planaric_perm hp).mp h)

theorem lower_necessary {d : List Nat} (hp : Planaric d) : ¬ d.Perm lowerException :=
  fun he => (lower_exception_verified he).2.2 hp

/-- The complete obstruction direction of Theorem 2. This stronger version
    does not need graphicness or a lower bound on the entries of h. -/
theorem upper_obstructions_nonplanar {d h : List Nat} {t l : Nat}
    (hp : d.Perm (profile h t l)) (sum : d.sum + 2*l = 4*d.length)
    (hf : UpperForbidden h t l) : ¬ Planaric d := by
  let low := List.replicate t 2 ++ List.replicate l 1
  have hs : h.sum = low.sum + 4*h.length := by
    rw [hp.sum_nat,hp.length_eq] at sum
    simp [profile, List.sum_replicate_nat, Nat.mul_comm] at sum
    simp [low, List.sum_replicate_nat, Nat.mul_comm]
    omega
  suffices obs : ¬ Planaric (profile h t l) from fun pl => obs ((planaric_perm hp).mp pl)
  rcases hf with h5|⟨a,b,c,_,rfl⟩|h1|h2|h3|h4|h6|h7
  · apply Graph.five_core_obstruction h low h5
    omega
  · apply Graph.six_core_obstruction a b c low
    simp at hs
    omega
  · rw [h1]; exact (Graph.upper_universal_exceptions l).1
  · rw [h2]; exact (Graph.upper_universal_exceptions l).2.1
  · rw [h3]; exact (Graph.upper_universal_exceptions l).2.2
  · rw [h4]; exact Graph.FiveFiveThree_nonplanar
  · rw [h6]; exact Graph.FourRegularSeven_nonplanar
  · rw [h7]; exact Graph.ThreeSixes_nonplanar

end SparseBoundary
