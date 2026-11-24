import Triangulation.Layers
import SourceConverse
import SparseBoundary.GraphDeletion

namespace Recognition.HardnessConverse
open SparseBoundary SparseBoundary.Graph Recognition.Reduction Recognition.Layers Recognition.Rigidity
open Recognition.SourceConverse

def SameEdges {d : List Nat} (R : Layers.Model d) (G : Graph d.length) :=
  ∀ x y : Fin d.length, R.edge x.val y.val ↔ G.adj x y = true

/-- The usual embedding theorem for a simple planar graph attaining Euler's
edge bound. Both sides retain every original label and adjacency. This is an
explicit hypothesis of the final transfer, with no project axiom. -/
def TightEmbedding := ∀ (d : List Nat) (G : Graph d.length), TableValid d →
  G.Realizes d → G.Planar → ∃ R : Layers.Model d, SameEdges R G

private theorem filter_mass (xs : List Nat) (f : Nat → Bool) :
    (xs.filter f).length = mass xs (fun v => (f v).toNat) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [mass,h] at * <;> omega

theorem compatible_degrees {d : List Nat} (S : Layers.Model d) (G : Graph d.length)
    (same : SameEdges S G) : G.Realizes d := by
  classical
  intro i
  obtain ⟨a,ha⟩ := (S.hits i.val).mp i.isLt
  let f := fun v => (natAdj G i.val v).toNat
  have coincide (b : S.V) : f (S.label b) = mark (S.map.adj a b) := by
    let j : Fin d.length := ⟨S.label b,bound S b⟩
    have H : S.map.adj a b ↔ G.adj i j = true := by
      rw [← same]
      constructor
      · intro h; exact ⟨a,b,ha,rfl,h⟩
      · rintro ⟨u,v,hu,hv,h⟩
        exact S.inj _ _ (hu.trans ha.symm) ▸ S.inj _ _ hv ▸ h
    change (natAdj G i.val j.val).toNat = _
    rw [natAdj_fin]
    cases h : G.adj i j <;> simp [mark,H,h]
  calc
    G.degree i = mass (List.range d.length) f := (degree_count G i).symm.trans (filter_mass ..)
    _ = mass S.vertices.vertices (fun b => f (S.label b)) := (label_sum S f).symm
    _ = Rigidity.degree (M:=S.map) S.vertices a := by
      unfold Rigidity.degree mass
      rw [List.map_congr_left (fun b _ => coincide b)]
    _ = d[i] := by rw [S.value,ha,List.getElem?_eq_getElem i.isLt]; rfl

private theorem old_order (qs : List Test) (T : Table) : T.degrees.length ≤ (qs.foldl layer T).degrees.length := by
  induction qs generalizing T with
  | nil => exact Nat.le_refl _
  | cons t ts ih => exact Nat.le_trans (layer_ge T t) (ih _)

/-- From *one* edge-preserving triangular map on the output, the induced
source graph is planar by hereditary minor exclusion. No planar embedding
or matching of a second graph is required after peeling. -/
private theorem minor_restrict {n m k : Nat} (G : Graph n) (f : Fin m → Fin n)
    (inj : Function.Injective f) (P : Fin k → Fin k → Bool) (bags : Fin k → List (Fin m))
    (minor : (G.restrict f).minorTest P bags) : G.minorTest P (fun i => (bags i).map f) := by
  have old := SparseBoundary.Truncation.model_iff.mp minor
  apply SparseBoundary.Truncation.model_iff.mpr
  let rec con (l : List (Fin m)) : (G.restrict f).connected l → G.connected (l.map f) := by
    match l with
    | [] => exact id
    | [_] => exact id
    | x::y::xs =>
      intro h
      obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
      apply Bool.and_eq_true_iff.mpr
      obtain ⟨v,hv,hx⟩ := List.any_eq_true.mp a
      exact ⟨List.any_eq_true.mpr ⟨f v,List.mem_map.mpr ⟨v,hv,rfl⟩, (restrict_adj G f x v).symm ▸ hx⟩,
        con (y::xs) b⟩
  refine ⟨fun i => con _ (old.con i),?_,?_⟩
  · rintro i j h z hi hj
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    obtain ⟨b,hb,e⟩ := List.mem_map.mp hj
    exact old.sep i j h a ha (inj e ▸ hb)
  · intro i j h
    obtain ⟨x,hx,y,hy,e⟩ := old.link i j h
    exact ⟨f x,List.mem_map.mpr ⟨_,hx,rfl⟩,f y,List.mem_map.mpr ⟨_,hy,rfl⟩,
      (restrict_adj G f x y).symm ▸ e⟩

theorem decode_output_k5free (I : Instance) (hv : Valid I) (G : Graph (encode I).length)
    (hp : K5Free G) (R : Layers.Model (encode I)) (same : SameEdges R G) : ThreePartition I := by
  obtain ⟨S,prescribedEdges,induced⟩ := decode_induced I hv R
  have size : (sourceTable I).length ≤ (encode I).length := old_order (allTests I) ⟨sourceTable I,0⟩
  let f : Fin (sourceTable I).length → Fin (encode I).length := fun i => ⟨i.val,Nat.lt_of_lt_of_le i.isLt size⟩
  have H (x y : Fin (sourceTable I).length) : S.edge x.val y.val ↔ (G.restrict f).adj x y = true := by
    rw [restrict_adj]
    exact (induced _ _ x.isLt y.isLt).trans (same (f x) (f y))
  have free : K5Free (G.restrict f) := by
    rintro ⟨bags,hb⟩
    exact hp ⟨_,minor_restrict G f (fun _ _ eq => Fin.ext (congrArg (fun z : Fin (encode I).length => z.val) eq)) clique5 bags hb⟩
  refine source_converse_k5free I hv (G.restrict f) (compatible_degrees _ _ H) ?_ free
  intro e he
  obtain h := prescribedEdges e he
  obtain ⟨p,q,ep,eq,ed⟩ := h
  let x : Fin (sourceTable I).length := ⟨e.left,ep ▸ bound S p⟩
  let y : Fin (sourceTable I).length := ⟨e.right,eq ▸ bound S q⟩
  change natAdj (G.restrict f) x.val y.val = true
  rw [natAdj_fin]
  exact (H x y).mp ⟨p,q,ep,eq,ed⟩

theorem decode_output (I : Instance) (hv : Valid I) (G : Graph (encode I).length)
    (hp : G.Planar) (R : Layers.Model (encode I)) (same : SameEdges R G) : ThreePartition I :=
  decode_output_k5free I hv G hp.1 R same

theorem hardness_converse (embedding : TightEmbedding) (I : Instance) (hv : Valid I)
    (h : Planaric (encode I)) : ThreePartition I := by
  obtain ⟨G,deg,planar⟩ := h
  obtain ⟨R,same⟩ := embedding _ G (encoded_valid I hv) deg planar
  exact decode_output I hv G planar R same

end Recognition.HardnessConverse
