import Std

namespace SparseBoundary.Rotations

abbrev Rotation := List (List Nat)
abbrev Dart := Nat × Nat

/-- The darts of the graph described by the rotation rows. -/
def darts (rows : Rotation) : List Dart :=
  rows.zipIdx.flatMap fun (row, v) => row.map fun w => (v, w)

/-- The face permutation traverses a dart and turns to its cyclic successor. -/
def turn (rows : Rotation) (d : Dart) : Dart :=
  let row := rows[d.2]?.getD []
  let p := row.idxOf d.1
  (d.2, row[(p+1) % row.length]?.getD rows.length)

def walk {α : Type} (f : α → α) : Nat → α → List α
  | 0, _ => []
  | k+1, a => a :: walk f k (f a)

/-- A dart is the lexicographically first dart of its orbit exactly once
    per face. The full dart count bounds the length of each orbit. -/
def faceCount (rows : Rotation) : Nat :=
  let ds := darts rows
  (ds.filter fun d => (walk (turn rows) ds.length d).all (fun x => decide (d.1 < x.1 ∨ (d.1 = x.1 ∧ d.2 ≤ x.2)))).length

def reachable (rows : Rotation) : Nat → List Nat → List Nat
  | 0, seen => seen
  | k+1, seen =>
    reachable rows k ((seen ++ seen.flatMap (fun v => rows[v]?.getD [])).eraseDups)

/-- Check the labelled graph, vertex rotations, face orbits, and Euler
    characteristic. A nonempty connected orientable rotation system of
    characteristic two describes a cellular drawing on the sphere. -/
def verify (rows : Rotation) (target : List Nat) (faces : Nat) : Bool :=
  let n := rows.length
  let ds := darts rows
  0 < n &&
    n == target.length && target.all (fun d => target.count d == (rows.map List.length).count d) &&
    rows.zipIdx.all (fun (row,v) =>
      row.Nodup && row.all (fun w => w < n && w != v && (rows[w]?.getD []).contains v)) &&
    (reachable rows n [0]).length == n &&
    faceCount rows == faces &&
    2*n + 2*faces == 4 + ds.length

/-- The seven cyclic order systems of the small-realizations table. -/
def repairs : List (Rotation × List Nat × Nat) := [
  ([[4, 5, 7, 6], [2, 6, 5, 3], [4, 6, 1, 3], [1, 5, 4, 2], [0, 6, 2, 3], [3, 1, 6, 0], [5, 1, 2, 4, 0, 7], [6, 0]], [6, 4, 4, 4, 4, 4, 4, 2], 10),
  ([[1, 6, 2, 4, 3, 5], [0, 5, 3, 2, 6], [1, 4, 7, 0, 6], [4, 1, 5, 0, 8], [2, 3, 8, 0, 7], [3, 1, 0], [2, 0, 1], [4, 2], [3, 4]], [6, 5, 5, 5, 5, 3, 3, 2, 2], 11),
  ([[1, 6, 3, 5, 2], [0, 2, 4, 3, 6], [1, 0, 5, 4], [4, 0, 6, 1], [2, 5, 3, 1], [4, 2, 0], [3, 0, 1]], [5, 5, 4, 4, 4, 3, 3], 9),
  ([[3, 6, 7, 5, 4], [2, 5, 7, 6], [3, 4, 1, 6], [0, 4, 2, 6], [5, 2, 3, 0], [1, 4, 0, 7], [1, 0, 3, 2], [5, 0, 1]], [5, 4, 4, 4, 4, 4, 4, 3], 10),
  ([[1, 5, 4, 3, 7, 6, 2], [0, 2, 3, 4, 5], [1, 0, 6, 7, 3], [2, 0, 1], [1, 0, 5], [4, 0, 1], [2, 0, 7], [6, 0, 2]], [7, 5, 5, 3, 3, 3, 3, 3], 10),
  ([[1, 6, 5, 7, 2, 4], [0, 3, 2, 7, 5, 6], [1, 3, 4, 0, 7], [2, 1, 4], [3, 0, 2], [1, 0, 6], [5, 0, 1], [2, 0, 1]], [6, 6, 5, 3, 3, 3, 3, 3], 10),
  ([[1, 7, 6, 4, 3, 2, 5], [0, 5, 2, 6, 7, 8], [1, 5, 0, 3, 4, 6], [2, 0, 4], [3, 0, 2], [2, 1, 0], [2, 0, 1], [1, 0, 8], [7, 1]], [7, 6, 6, 3, 3, 3, 3, 3, 2], 11)
]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem repairs_spherical : repairs.all (fun (rows, target, faces) => verify rows target faces) = true := by
  decide +kernel

end SparseBoundary.Rotations
