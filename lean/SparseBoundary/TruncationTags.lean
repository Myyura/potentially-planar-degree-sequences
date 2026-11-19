import SparseBoundary.Graph

namespace SparseBoundary.Truncation

abbrev Roles (k : Nat) := Fin 3 → Fin (k+1)
def hit (r : Roles k) (s : Fin 3) (i : Fin k) : Prop := (r s).val=i.val

/-- A site whose external neighbor is absent from its bag, and which is
    the only triangle site in that bag, must see every neighboring bag
    on the triangle itself, except possibly the bag at its one port. -/
def Admissible (R : Fin k → Fin k → Bool) (r : Roles k) (a : Fin 3 → Bool) : Prop :=
  ∀ s i, hit r s i → a s=false → (∀ t, hit r t i → t=s) →
    ∃ j : Fin (k+1), ∀ u, R i u=true → (∃ t, hit r t u) ∨ j.val=u.val

/-- Every triangle edge crossing between two required bags is incident
    with the bag assigned the old central vertex. -/
def Centered (R : Fin k → Fin k → Bool) (r : Roles k) (a : Fin 3 → Bool) (c : Fin (k+1)) : Prop :=
  (∀ s i, hit r s i → i.val ≠ c.val → a s=true ∧ ∀ t, hit r t i → t=s) ∧
  (∀ s t i j, hit r s i → hit r t j → R i j=true → i.val=c.val ∨ j.val=c.val)

def SplitFive (r : Roles 5) (a : Fin 3 → Bool) : Prop :=
  (∀ s, (r s).val<5 ∧ a s=true) ∧
  (∀ s t, r s=r t → s=t) ∧
  ∃ i j : Fin 5, i ≠ j ∧ ∀ s, ¬hit r s i ∧ ¬hit r s j

private instance (r : Roles k) (s : Fin 3) (i : Fin k) : Decidable (hit r s i) := by
  unfold hit; infer_instance
private instance (R : Fin k → Fin k → Bool) (r : Roles k) (a : Fin 3→Bool) :
    Decidable (Admissible R r a) := by unfold Admissible; infer_instance
private instance (R : Fin k → Fin k → Bool) (r : Roles k) (a : Fin 3→Bool) (c : Fin (k+1)) :
    Decidable (Centered R r a c) := by unfold Centered; infer_instance
private instance (r : Roles 5) (a : Fin 3→Bool) : Decidable (SplitFive r a) := by
  unfold SplitFive; infer_instance

def triple (x y z : α) : Fin 3 → α := Fin.cases x (Fin.cases y (fun _ => z))

private theorem eta (f : Fin 3 → α) : triple (f 0) (f 1) (f 2)=f := by
  funext i
  have c : ∀ i : Fin 3, i=0 ∨ i=1 ∨ i=2 := by decide
  rcases c i with rfl|rfl|rfl <;> rfl

set_option maxHeartbeats 0
set_option maxRecDepth 32768

theorem tags_five (r : Roles 5) (a : Fin 3 → Bool) (h : Admissible Graph.clique5 r a) :
    (∃ c, Centered Graph.clique5 r a c) ∨ SplitFive r a := by
  have all : ∀ x y z : Fin 6, ∀ p q w : Bool, let v := triple x y z; let f := triple p q w
      Admissible Graph.clique5 v f → (∃ c,Centered Graph.clique5 v f c) ∨ SplitFive v f := by decide +kernel
  simpa only [eta] using all (r 0) (r 1) (r 2) (a 0) (a 1) (a 2) (by simpa only [eta] using h)

theorem tags_six (r : Roles 6) (a : Fin 3 → Bool) (h : Admissible Graph.biclique33 r a) :
    ∃ c, Centered Graph.biclique33 r a c := by
  have all : ∀ x y z : Fin 7, ∀ p q w : Bool, let v := triple x y z; let f := triple p q w
      Admissible Graph.biclique33 v f → ∃ c,Centered Graph.biclique33 v f c := by decide +kernel
  simpa only [eta] using all (r 0) (r 1) (r 2) (a 0) (a 1) (a 2) (by simpa only [eta] using h)

end SparseBoundary.Truncation
