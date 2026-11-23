import DiskFullerene.EndGeometry

namespace DiskFullerene.SixTable
abbrev SixGraph := Fin 32768

def adjacent (G : SixGraph) (x y : Nat) : Bool :=
  x != y && G.val.testBit (max x y * (max x y - 1) / 2 + min x y)

private def slots : List (Nat × Nat) :=
  [(0,1), (0,2), (1,2), (0,3), (1,3), (2,3), (0,4), (1,4), (2,4), (3,4), (0,5), (1,5), (2,5), (3,5), (4,5)]

/-- Pack an arbitrary adjacency function on six labels into its fifteen undirected bits. -/
def encode (r : Nat → Nat → Bool) : SixGraph :=
  let bits := BitVec.ofBoolListLE (slots.map (fun (a,b) => r a b))
  ⟨bits.toNat, by
    have e : 2 ^ slots.length = 32768 := by decide
    simpa only [List.length_map, e] using bits.isLt⟩

private theorem slots_ok : ∀ x y : Fin 6, x ≠ y →
    slots[max x.val y.val * (max x.val y.val - 1) / 2 + min x.val y.val]? =
      some (min x.val y.val, max x.val y.val) := by decide

theorem encode_adjacent (r : Nat → Nat → Bool)
    (loopless : ∀ x : Fin 6, r x.val x.val = false)
    (symm : ∀ x y : Fin 6, r x.val y.val = r y.val x.val) (x y : Fin 6) :
    adjacent (encode r) x.val y.val = r x.val y.val := by
  by_cases h : x = y
  · subst y; simp [adjacent, loopless]
  have hn : x.val ≠ y.val := fun he => h (Fin.ext he)
  simp only [adjacent, bne_iff_ne.mpr hn, Bool.true_and]
  change (BitVec.ofBoolListLE (slots.map (fun (a,b) => r a b))).getLsbD _ = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_map, slots_ok x y h]
  by_cases hxy : x.val ≤ y.val
  · simp [Nat.min_eq_left hxy, Nat.max_eq_right hxy]
  · have hyx : y.val ≤ x.val := by omega
    simp [Nat.min_eq_right hyx, Nat.max_eq_left hyx, symm y x]


def labels := [0,1,2,3,4,5]
def pairs := [[0,1],[0,2],[0,3],[0,4],[0,5],[1,2],[1,3],[1,4],[1,5],[2,3],[2,4],[2,5],[3,4],[3,5],[4,5]]
def triples := [[0,1,2],[0,1,3],[0,1,4],[0,1,5],[0,2,3],[0,2,4],[0,2,5],[0,3,4],[0,3,5],[0,4,5],[1,2,3],[1,2,4],[1,2,5],[1,3,4],[1,3,5],[1,4,5],[2,3,4],[2,3,5],[2,4,5],[3,4,5]]
def clique (G : SixGraph) (s : List Nat) := s.all (fun i => s.all (fun j => i==j || adjacent G i j))
def innerNeighbors (G : SixGraph) (v : Nat) := labels.filter (adjacent G v)
def ear (G : SixGraph) (v : Nat) :=
  match innerNeighbors G v with
  | [_] => true
  | [a,b] => adjacent G a b
  | _ => false

def closedLink (G : SixGraph) (c : Nat) :=
  (EndGeometry.subsets (innerNeighbors G c)).any (fun s => !s.isEmpty &&
    s.all (fun v => 2 ≤ (s.filter (adjacent G v)).length))

def test (G : SixGraph) :=
  2 ≤ (labels.filter (ear G)).length ||
  (6 + (triples.filter (clique G)).length < (pairs.filter (clique G)).length + 1) ||
  labels.any (fun v => (innerNeighbors G v).isEmpty) ||
  labels.any (closedLink G)

end DiskFullerene.SixTable
