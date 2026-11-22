import CanonicalRow
import RowRouting
import RowSlotMap
import RowSphere

/-! The ordered interval test for the original labelled degree-list
language. Soundness is unconditional. Completeness uses just the classical
canonical-order existence theorem for a maximal planar host. -/
namespace Recognition.RowRecognition
open RowRule RowPlane RowRouting CanonicalRow LeanPool.K5MinorFreeChoosability SparseBoundary

private theorem width_exists (ls : List Layer) : ∃ w : Nat, ∀ a∈ls, a.width ≤ w := by
  induction ls with
  | nil => exact ⟨0, by simp⟩
  | cons a ls ih =>
    obtain ⟨w,hw⟩ := ih
    refine ⟨max a.width w,?_⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl|tail
    · exact Nat.le_max_left .. 
    · exact (hw _ tail).trans (Nat.le_max_right ..)

private theorem packed_of_simple {n} (H : SimpleGraph (Fin n)) (plane : IsPlanar H) {ds}
    (degree : (List.ofFn fun i => Nat.card {j // H.Adj i j}) = ds) : Planaric ds := by
  classical
  have size : n = ds.length := by simpa using congrArg List.length degree
  subst n
  let rel (i j : Fin ds.length) := decide (H.Adj i j)
  let K := Graph.ofRelation rel
  have edge (i j : Fin ds.length) : K.adj i j = rel i j :=
    Graph.adj_ofRelation rel (fun a b => decide_eq_decide.mpr (H.adj_comm a b))
      (fun a => decide_eq_false_iff_not.mpr (H.irrefl (v:=a))) i j
  have eq : Wagner.toSimple K = H := by
    ext a b
    rw [Wagner.toSimple_adj,edge]
    simp [rel]
  refine ⟨K,?_,(Wagner.planar_iff_rotation K).2 (eq ▸ plane)⟩
  intro i
  rw [← Wagner.neighbor_count K i,eq]
  have val := congrArg (fun l : List Nat => l[i.val]?) degree
  simpa [List.getElem?_eq_getElem i.isLt] using val

/-- A successful numerical trace yields a genuine planar realization.
The proof shrinks each same-name system of port wires to one vertex in
the spherical host constructed from the two triangulated pages. -/
theorem trace_planaric {ds} (run : NumericalTrace ds []) : Planaric ds := by
  classical
  obtain ⟨s,ls,_,hist,closed,_,_,_⟩ := replay_pages run
  obtain ⟨w,bound⟩ := width_exists ls
  obtain ⟨A⟩ := history_packing hist bound
  let mm := A.model (history_trace hist).valid
  have box (v : Fin s.n) (x : Nat × Nat) (hx : x∈mm.branch v) :
      RowSlotMap.InBox ls w x := A.bounds v v.isLt x hx
  let packed := RowSlotMap.pack mm box (fun _ _ e => e)
  have sphere := isPlanar_of_minorModel (RowSphere.portGraph_planar ls w) packed
  exact packed_of_simple _ sphere (stateGraph_degrees hist closed)

private theorem prepend_run {xs ys row} (hx : NumericalTrace xs []) (hy : NumericalTrace ys row) :
    NumericalTrace (xs++ys) row := by
  induction hy with
  | start => simpa using hx
  | advance _ m ih => simpa [List.append_assoc] using NumericalTrace.advance ih m

private def zeroMove : NumericalMove [] 0 where
  left := []; first := []; middle := []; last := []; right := []
  split := rfl
  firstSize := by decide
  lastSize := by decide
  interior := by simp
  affordable := by decide

private theorem zeros_run (xs : List Nat) (zero : ∀ v∈xs, v=0) : NumericalTrace xs [] := by
  induction xs with
  | nil => exact .start
  | cons v l ih =>
    have z := zero v (.head _)
    subst v
    have one : NumericalTrace [0] [] := .advance .start zeroMove
    exact prepend_run one (ih (fun x hx => zero _ (.tail _ hx)))

/-- Zero entries of the input correspond to isolated vertices, and all
occurrences of equal positive degrees may be chosen in any order. -/
theorem positive_trace_planaric {xs ds : List Nat}
    (perm : xs.Perm (ds.filter (fun x => 0 < x))) (run : NumericalTrace xs []) : Planaric ds := by
  let p := fun x : Nat => decide (0<x)
  let zs := ds.filter (fun x => !(p x))
  have all : ∀ x∈zs, x=0 := by
    intro x hx
    have b := (List.mem_filter.1 hx).2
    simp [p] at b
    omega
  have witness := trace_planaric (prepend_run run (zeros_run zs all))
  have sorted : (xs ++ zs).Perm ds := (perm.append_right zs).trans (List.filter_append_perm p ds)
  exact (planaric_perm sorted).1 witness

/-- The paper's interval characterization, with its one named literature
input. All other implications refer to the packed potential-planarity
language used by the NP-completeness and recognition theorems. -/
theorem interval_iff (ord : CanonicalOrderingInput) (ds : List Nat) :
    Planaric ds ↔ ∃ xs : List Nat, xs.Perm (ds.filter (fun x => 0 < x)) ∧ NumericalTrace xs [] :=
  ⟨planaric_has_trace ord, fun ⟨_,p,r⟩ => positive_trace_planaric p r⟩

/-- A prescribed positive occurrence can be reserved for the last move,
even if there are other vertices of that degree. -/
theorem interval_last_iff (ord : CanonicalOrderingInput) {ds : List Nat}
    (z : Fin ds.length) (positive : 0 < ds[z.val]) :
    Planaric ds ↔ ∃ xs : List Nat, xs.Perm (ds.filter (fun x => 0 < x)) ∧
      xs.getLast? = some ds[z.val] ∧ NumericalTrace xs [] :=
  ⟨fun hp => prescribed_last_degree ord hp z positive,
    fun ⟨_,p,_,r⟩ => positive_trace_planaric p r⟩

end Recognition.RowRecognition
