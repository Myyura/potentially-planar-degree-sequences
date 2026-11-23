import Std

/-! A combinatorial map is specified on the original cubic graph, with labelled
vertices, cyclic neighbour rows and oriented facial boundary words.  Faces
must follow the rotation and partition the darts; Euler characteristic two
specifies the sphere. Connectivity after deleting vertices is ordinary
graph reachability. Nothing in the definition imposes a strip or an end. -/
namespace DiskFullerene

abbrev Dart := Nat × Nat

structure MapData where
  rows : List (List Nat)
  outer : List Nat
  inner : List (List Nat)
  deriving Repr

def MapData.ord (M : MapData) := M.rows.length
def MapData.faces (M : MapData) := M.outer :: M.inner
def MapData.adj (M : MapData) (u v : Nat) : Prop := v ∈ M.rows[u]?.getD []
def MapData.hexagons (M : MapData) := (M.inner.map List.length).count 6
def MapData.pentagons (M : MapData) := (M.inner.map List.length).count 5

/-- The oriented edges of one closed face walk. -/
def sides {α} : List α → List (α × α)
  | [] => []
  | u :: us => (u :: us).zip (us ++ [u])

private theorem sides_length {α} (f : List α) : (sides f).length = f.length := by
  cases f <;> simp [sides]

def MapData.darts (M : MapData) : List Dart :=
  M.rows.zipIdx.flatMap fun (r, u) => r.map (u, ·)

def MapData.turn (M : MapData) (d : Dart) : Dart :=
  let r := M.rows[d.2]?.getD []
  (d.2, r[(r.idxOf d.1 + 1) % r.length]?.getD M.ord)

def MapData.rotationOK (M : MapData) : Bool :=
  M.rows.zipIdx.all fun (r,u) => r.Nodup && r.all fun v =>
    v < M.ord && v != u && (M.rows[v]?.getD []).contains u

def MapData.faceOK (M : MapData) (f : List Nat) : Bool :=
  f.Nodup && (sides (sides f)).all fun (d,e) => M.turn d == e

inductive PathAvoiding (E : Nat → Nat → Prop) (gone : List Nat) : Nat → Nat → Prop where
  | here {a} (ok : a ∉ gone) : PathAvoiding E gone a a
  | step {a b c} : PathAvoiding E gone a b → E b c → c ∉ gone → PathAvoiding E gone a c

def MapData.ThreeConnected (M : MapData) : Prop :=
  4 ≤ M.ord ∧ ∀ (gone : List Nat), gone.length ≤ 2 →
    ∀ u v, u < M.ord → v < M.ord → u ∉ gone → v ∉ gone → PathAvoiding M.adj gone u v

structure IsDiskFullerene (M : MapData) (h : Nat) : Prop where
  cubic : ∀ r ∈ M.rows, r.length = 3
  simpleRotation : M.rotationOK = true
  faceOrbits : M.faces.all M.faceOK = true
  coverage : (M.faces.flatMap sides).Perm M.darts
  sphere : 2 * M.ord + 2 * M.faces.length = M.darts.length + 4
  connectivity : M.ThreeConnected
  outerSize : M.outer.length = h
  polygons : ∀ f ∈ M.inner, f.length = 5 ∨ f.length = 6

/-- Abstract graph isomorphism, allowing relabelling as well as reflection. -/
def GraphIso (M N : MapData) : Prop :=
  ∃ (f : Fin M.ord → Fin N.ord) (g : Fin N.ord → Fin M.ord),
    (∀ v, g (f v) = v) ∧ (∀ w, f (g w) = w) ∧
    ∀ v w, M.adj v.val w.val ↔ N.adj (f v).val (f w).val

/-- Theorem 1, including the order and pentagon count. This definition is
the verification target. It is not a proof of that proposition. -/
def MainStatement : Prop := ∀ h, 12 ≤ h →
  (∀ M, IsDiskFullerene M h → 6 ≤ M.hexagons) ∧
  ∃ G, IsDiskFullerene G h ∧ G.hexagons = 6 ∧ G.pentagons = h + 6 ∧
    G.ord = 2 * h + 22 ∧ ∀ H, IsDiskFullerene H h → H.hexagons = 6 → GraphIso G H

private theorem totalCubic (rs : List (List Nat)) (k : Nat)
    (hc : ∀ r ∈ rs, r.length = 3) :
    ((rs.zipIdx k).flatMap (fun (r,u) => r.map (u, ·))).length = 3 * rs.length := by
  induction rs generalizing k with
  | nil => simp
  | cons r rs ih =>
    have hr := hc r (by simp)
    have ht := ih (k+1) (fun x hx => hc x (by simp [hx]))
    simpa [List.zipIdx_cons, hr, Nat.mul_add, Nat.add_comm] using
      congrArg (r.length + ·) ht

theorem cubic_dart_count {M : MapData} (cubic : ∀ r ∈ M.rows, r.length=3) :
    M.darts.length = 3*M.ord := totalCubic M.rows 0 cubic

private theorem faceCounts (ns : List Nat) (hf : ∀ a ∈ ns, a = 5 ∨ a = 6) :
    ns.length = ns.count 5 + ns.count 6 ∧ ns.sum = 5 * ns.count 5 + 6 * ns.count 6 := by
  induction ns with
  | nil => simp
  | cons a xs ih =>
    have ⟨hl,hs⟩ := ih (fun x hx => hf x (by simp [hx]))
    rcases hf a (by simp) with rfl|rfl <;> simp <;> omega

/-- Euler and face incidence on the actual map, for every boundary length. -/
theorem eulerCounts {M : MapData} {h : Nat} (G : IsDiskFullerene M h) :
    M.pentagons = h + 6 ∧ M.ord = 2 * (h + M.hexagons + 5) := by
  have hc : M.darts.length = 3 * M.ord := totalCubic M.rows 0 G.cubic
  obtain ⟨hl,hs⟩ := faceCounts (M.inner.map List.length) (by
    intro a ha
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ha
    exact G.polygons f hf)
  have cov := G.coverage.length_eq
  simp [List.length_flatMap, sides_length, MapData.faces, G.outerSize] at cov
  have e := G.sphere
  simp only [MapData.faces,List.length_cons] at e
  simp only [List.length_map] at hl
  change h + (M.inner.map List.length).sum = M.darts.length at cov
  unfold MapData.pentagons MapData.hexagons
  omega

theorem extremalOrder {M : MapData} {h : Nat} (G : IsDiskFullerene M h)
    (six : M.hexagons = 6) : M.ord = 2*h+22 := by
  have := (eulerCounts G).2
  omega

end DiskFullerene
