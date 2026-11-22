import EmbeddingBridge

/-! The combinatorial dual of a sphere triangulation on the same directed
edges. Dual vertices and faces are cycles of specified permutations. Taking
the dual exchanges the rotation and the face walk, with the edge involution
unchanged. Geometric realization of a three-connected plane graph by a
convex polytope in real three-space (Steinitz) is a separate theorem. -/
namespace Recognition.PolytopeDual
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open SparseBoundary Recognition.Wagner

variable {V : Type*} {G : SimpleGraph V}

/-- A cell is a full cycle, including every dart in the orbit. -/
abbrev Cell {D : Type*} (π : Perm D) := Quotient (SameCycle.setoid π)

noncomputable def cellSize {D : Type*} (π : Perm D) (c : Cell π) : Nat :=
  Nat.card {e : D // Quotient.mk (SameCycle.setoid π) e = c}

/-- Around a dual vertex, walk around one primal face. -/
abbrev dualRot (M : PlaneMap G) := M.facePerm

/-- The dual face successor first reverses the dart, then takes the next
one around its dual vertex. -/
abbrev dualFace (M : PlaneMap G) := dualRot M * dartSymm G

@[simp] theorem dualFace_eq (M : PlaneMap G) : dualFace M = M.rot := by
  apply Equiv.ext
  intro d
  change M.rot d.symm.symm = M.rot d
  simp

/-- Dualization preserves each connected component, including its darts. -/
theorem component_iff (M : PlaneMap G) (a b : G.Dart) :
    compSetoid (dualRot M) (dartSymm G) a b ↔ compSetoid M.rot (dartSymm G) a b := by
  constructor
  · apply compSetoid_le
    · intro d
      exact (compSetoid M.rot (dartSymm G)).trans (compSetoid_right _ _ d)
        (compSetoid_left _ _ d.symm)
    · exact compSetoid_right _ _
  · apply compSetoid_le
    · intro d
      have step := (compSetoid (dualRot M) (dartSymm G)).trans (compSetoid_right _ _ d)
        (compSetoid_left _ _ d.symm)
      simpa [dualRot, PlaneMap.facePerm_apply] using step
    · exact compSetoid_right _ _

/-- The dual dart map is spherical. -/
theorem dual_spherical (M : PlaneMap G) : eulerDefect (dualRot M) (dartSymm G) = 0 := by
  have comps : numComponents (dualRot M) (dartSymm G) = numComponents M.rot (dartSymm G) :=
    numClasses_congr (component_iff M)
  have last := M.eulerDefect_eq_zero
  unfold eulerDefect at *
  rw [comps, show dualRot M * dartSymm G = M.rot from dualFace_eq M]
  change _ + _ - (cycleCount M.facePerm : ℤ) - _ - _ = 0
  change _ + _ - _ - _ - (cycleCount M.facePerm : ℤ) = 0 at last
  omega

private theorem face_cycle_iff_tail (M : PlaneMap G) (d e : G.Dart) :
    SameCycle (dualFace M) d e ↔ d.fst = e.fst := by
  rw [dualFace_eq]
  constructor
  · exact sameCycle_of_step (Setoid.ker fun t : G.Dart => t.fst)
      (fun x => (M.isRotationSystem.fst_apply x).symm)
  · exact M.isRotationSystem.sameCycle d e

/-- Every dual face carries a canonical primal vertex. -/
def faceVertex (M : PlaneMap G) : Cell (dualFace M) → V :=
  Quotient.lift (fun d : G.Dart => d.fst) (fun d e => (face_cycle_iff_tail M d e).mp)

/-- With no isolated primal vertices this labelling is a bijection. -/
noncomputable def faceEquiv (M : PlaneMap G) (nbr : ∀ x, ∃ y, G.Adj x y) :
    Cell (dualFace M) ≃ V := Equiv.ofBijective (faceVertex M) (by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y => exact fun h => Quotient.sound ((face_cycle_iff_tail M x y).mpr h)
  · intro v
    obtain ⟨w, edge⟩ := nbr v
    exact ⟨Quotient.mk _ (⟨(v,w),edge⟩ : G.Dart), rfl⟩)

/-- Boundary darts of a dual face correspond to individual neighbours of
its original vertex. This counts all faces, including repeated sizes. -/
theorem dual_face_size (M : PlaneMap G) (c : Cell (dualFace M)) :
    cellSize (dualFace M) c = Nat.card {u // G.Adj (faceVertex M c) u} := by
  induction c using Quotient.inductionOn with
  | h d =>
    let eqTail (x : G.Dart) : Quotient.mk (SameCycle.setoid (dualFace M)) x = Quotient.mk _ d ↔
        x.fst = d.fst := Quotient.eq.trans (face_cycle_iff_tail M x d)
    apply Nat.card_congr
    refine ⟨fun x => ⟨x.val.snd, ?_⟩,
      fun y => ⟨⟨(d.fst,y.val),y.property⟩, (eqTail _).mpr rfl⟩, ?_, ?_⟩
    · change G.Adj d.fst x.val.snd
      rw [← (eqTail _).mp x.property]
      exact x.val.adj
    · intro x
      apply Subtype.ext
      apply (SimpleGraph.Dart.ext_iff _ _).2
      exact Prod.ext ((eqTail _).mp x.property).symm rfl
    · intro y
      rfl

/-- Euler equality makes each dual vertex trivalent. -/
theorem tight_dual_cubic [Finite V] (M : PlaneMap G)
    (deg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u}) (order : Nonempty V)
    (edges : Nat.card G.edgeSet + 6 = 3 * Nat.card V) (c : Cell (dualRot M)) :
    cellSize (dualRot M) c = 3 := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨_, period⟩ := tight_faces M deg order edges
  induction c using Quotient.inductionOn with
  | h d =>
    have size : cellSize (dualRot M) (Quotient.mk _ d) =
        Nat.card {e // SameCycle M.facePerm d e} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivProp
      funext e
      apply propext
      rw [Quotient.eq]
      exact ⟨fun t => SameCycle.symm t, fun t => SameCycle.symm t⟩
    rw [size]
    apply Nat.le_antisymm _ (three_le_card_face M.isRotationSystem deg d)
    apply card_sameCycle_le _ 3 (by decide) _ d
    intro x
    change (M.facePerm ^ 3) x = x
    simpa only [pow_succ, pow_zero, mul_one, Perm.mul_apply, Perm.one_apply] using period x

/-- All positive outputs of the reduction admit a connected spherical dual
with cubic vertices and exactly the given face sizes, indexed bijectively.
The geometric Steinitz realization is external to this dart-map theorem. -/
theorem table_dual (d : List Nat) (valid : Reduction.TableValid d) (yes : Planaric d) :
    ∃ (G : Graph d.length) (M : PlaneMap (toSimple G))
      (labels : Cell (dualFace M) ≃ Fin d.length),
      numComponents (dualRot M) (dartSymm (toSimple G)) = 1 ∧
      eulerDefect (dualRot M) (dartSymm (toSimple G)) = 0 ∧
      (∀ c : Cell (dualRot M), cellSize (dualRot M) c = 3) ∧
      (∀ c : Cell (dualFace M), cellSize (dualFace M) c = d[labels c]) ∧
      (∀ c, labels c = faceVertex M c) := by
  obtain ⟨G, realizes, flat⟩ := yes
  obtain ⟨M⟩ := (planar_iff_rotation G).mp flat
  obtain ⟨low,edges⟩ := order_counts G valid realizes
  have deg (v) : 2 ≤ Nat.card {u // (toSimple G).Adj v u} := (by decide : 2 ≤ 3) |>.trans (low v)
  have len := valid.1
  have order : Nonempty (Fin d.length) := ⟨⟨0,by omega⟩⟩
  have nbr (v) : ∃ u, (toSimple G).Adj v u := by
    obtain ⟨u⟩ := (Nat.card_pos_iff.mp (by have := deg v; omega : 0 < Nat.card {u // (toSimple G).Adj v u})).1
    exact ⟨u.val,u.property⟩
  refine ⟨G,M,faceEquiv M nbr, ?_, dual_spherical M, tight_dual_cubic M deg order edges, ?_⟩
  · exact (numClasses_congr (component_iff M)).trans (tight_faces M deg order edges).1
  · exact ⟨fun c => (dual_face_size M c).trans ((neighbor_count G _).trans (realizes _)),
      fun _ => rfl⟩

/-- The flag-map version of the complete face-size language. Its dual
has a simple labelled underlying graph. Every label occurs on a face.
No primal degree constraint is placed on the witnessing graph. -/
def HasCubicDual (d : List Nat) : Prop :=
  ∃ (G : Graph d.length) (M : PlaneMap (toSimple G)),
    numComponents (dualRot M) (dartSymm (toSimple G)) = 1 ∧
    eulerDefect (dualRot M) (dartSymm (toSimple G)) = 0 ∧
    (∀ c : Cell (dualRot M), cellSize (dualRot M) c = 3) ∧
    Function.Bijective (faceVertex M) ∧
    ∀ c : Cell (dualFace M), cellSize (dualFace M) c = d[faceVertex M c]

/-- Reading the face sizes back from the dual gives a full planar
realization. Vertex labels cannot be omitted or counted twice. -/
theorem dual_spectrum_sound {d : List Nat} (h : HasCubicDual d) : Planaric d := by
  obtain ⟨G, M, _, _, _, bij, sizes⟩ := h
  refine ⟨G, ?_, (planar_iff_rotation G).mpr ⟨M⟩⟩
  intro v
  obtain ⟨c, rfl⟩ := bij.2 v
  exact (neighbor_count G _).symm.trans ((dual_face_size M c).symm.trans (sizes c))

/-- The equivalence concerns combinatorial dart maps. A corresponding
claim about convex Euclidean polytopes additionally uses the geometric
realization theorem and geometric polarity. -/
theorem dual_spectrum_iff {d : List Nat} (valid : Reduction.TableValid d) :
    HasCubicDual d ↔ Planaric d := by
  refine ⟨dual_spectrum_sound, ?_⟩
  intro yes
  obtain ⟨G, M, labels, one, flat, cubic, sizes, indexed⟩ := table_dual d valid yes
  have agree : (labels : Cell (dualFace M) → Fin d.length) = faceVertex M := funext indexed
  exact ⟨G, M, one, flat, cubic, agree ▸ labels.bijective,
    fun c => (sizes c).trans (congrArg (fun v : Fin d.length => d[v]) (indexed c))⟩

/-- The same compiled list transmits unary three-partition to the
geometric-free problem of matching all face sizes of the dual map. -/
theorem compiled_dual_iff (I : Reduction.Instance) :
    HasCubicDual (Reduction.reduceInstance I) ↔ Reduction.Valid I ∧ Reduction.ThreePartition I :=
  (dual_spectrum_iff (Reduction.reduce_promise I)).trans (planaric_reduction_iff I)

end Recognition.PolytopeDual
