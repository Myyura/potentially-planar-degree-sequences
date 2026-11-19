import Std

namespace SparseBoundary

/-- Number of unordered pairs on n labelled vertices. -/
def pairCount : Nat → Nat
  | 0 => 0
  | n+1 => pairCount n + n

/-- A labelled simple graph. One bit is reserved for each unordered pair.
    The bits for pairs with larger endpoint j form a block of length j. -/
structure Graph (n : Nat) where
  bits : BitVec (pairCount n)
deriving DecidableEq

namespace Graph
def adj {n : Nat} (G : Graph n) (v w : Fin n) : Bool :=
  let j := max v.val w.val
  v != w && G.bits.getLsbD (pairCount j + min v.val w.val)

@[simp] theorem adj_self {n : Nat} (G : Graph n) (v : Fin n) :
    G.adj v v = false := by simp [adj]

theorem adj_comm {n : Nat} (G : Graph n) (v w : Fin n) :
    G.adj v w = G.adj w v := by
  simp only [adj]
  rw [Nat.max_comm v.val, Nat.min_comm v.val]
  rw [bne_comm (a := v) (b := w)]

def degree {n : Nat} (G : Graph n) (v : Fin n) : Nat :=
  ((List.finRange n).filter (G.adj v)).length

/-- Labels are in the order of the requested profile. An arbitrary labelling
    of the graph is available in the existential statements below. -/
def Realizes (d : List Nat) (G : Graph d.length) : Prop :=
  ∀ v : Fin d.length, G.degree v = d[v]

/-- A nonempty connected set presented in reverse construction order.
    Removing its head deletes a vertex attached to the remaining set. -/
def connected {n : Nat} (G : Graph n) : List (Fin n) → Bool
  | [] => false
  | [_] => true
  | v :: w :: rest => (w :: rest).any (G.adj v) && connected G (w :: rest)

def disjoint {n : Nat} (s t : List (Fin n)) : Bool :=
  s.all fun v => !(t.contains v)

def links {n : Nat} (G : Graph n) (s t : List (Fin n)) : Bool :=
  s.any fun v => t.any (G.adj v)

/-- Branch-set definition of a graph minor. Distinct bags are disjoint and
    each required edge must have two adjacent representatives. -/
def minorTest {n k : Nat} (G : Graph n) (required : Fin k → Fin k → Bool)
    (bags : Fin k → List (Fin n)) : Bool :=
  (List.finRange k).all fun i =>
    G.connected (bags i) && (List.finRange k).all fun j =>
      (i == j || disjoint (bags i) (bags j)) &&
      (!required i j || links G (bags i) (bags j))

def clique5 : Fin 5 → Fin 5 → Bool := fun i j => i != j
def biclique33 : Fin 6 → Fin 6 → Bool := fun i j => (i.val < 3) != (j.val < 3)

/-- Wagner's forbidden-minor characterization of planar finite graphs. -/
def Planar {n : Nat} (G : Graph n) : Prop :=
  (¬ ∃ bags, minorTest G clique5 bags = true) ∧
  (¬ ∃ bags, minorTest G biclique33 bags = true)
end Graph

def Graphic (d : List Nat) : Prop := ∃ G : Graph d.length, G.Realizes d
def Planaric (d : List Nat) : Prop := ∃ G : Graph d.length, G.Realizes d ∧ G.Planar

theorem planaric_graphic {d : List Nat} (h : Planaric d) : Graphic d := by
  obtain ⟨G, hG, _⟩ := h
  exact ⟨G, hG⟩

end SparseBoundary
