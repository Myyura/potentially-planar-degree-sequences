import DiskFullerene.Lower

/-! Up to five interior vertices, detect genuine facial ears using the
actual inner triangles. The graph is not assumed outerplanar. -/
namespace DiskFullerene.EndGeometry
open Lower

abbrev Tri := List Nat
def labels := [0,1,2,3,4]
def pairs := [[0,1],[0,2],[0,3],[0,4],[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]]
def triples := [[0,1,2],[0,1,3],[0,1,4],[0,2,3],[0,2,4],[0,3,4],[1,2,3],[1,2,4],[1,3,4],[2,3,4]]
def subsets {α} : List α → List (List α)
  | [] => [[]]
  | a::as => let ss := subsets as; ss ++ ss.map (a::·)

theorem filter_subset {α} (p : α → Bool) (xs : List α) :
    xs.filter p ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih => cases e : p x <;> simp [e,subsets,ih]

def clique (G : FiveGraph) (f : Tri) : Bool :=
  f.all (fun a => f.all (fun b => a == b || adjacent G a b))

def innerNeighbors (G : FiveGraph) (x : Nat) := labels.filter (adjacent G x)

def trueEar (G : FiveGraph) (F : List Tri) (x : Nat) : Bool :=
  match innerNeighbors G x with
  | [_] => true
  | [a,b] => F.any (fun t => t.contains x && t.contains a && t.contains b)
  | _ => false

def eCount (G : FiveGraph) := pairs.countP (clique G)
def vCount (G : FiveGraph) := labels.countP (fun x => !(innerNeighbors G x).isEmpty)

/-- A closed sublink. Every t in F has three distinct labels. When
linking at x, distinct t incident with x are edges on its other vertices. -/
def closedAt (F : List Tri) (x : Nat) (S : List Nat) : Bool :=
  !S.contains x && S.all (fun v => 2 ≤ F.countP (fun t =>
    t.contains x && t.contains v && t.all (fun w => w == x || S.contains w)))

def polygons := triples ++ [[0,1,2,3],[0,1,2,4],[0,1,3,4],[0,2,3,4],[1,2,3,4]]

def hasClosedLink (F : List Tri) : Bool :=
  labels.any fun x => polygons.any (closedAt F x)

private def finiteTest (G : FiveGraph) : Bool :=
  (subsets (triples.filter (clique G))).all (fun F =>
    !(0 < eCount G && decide (eCount G + 1 ≤ vCount G + F.length)) ||
    2 ≤ (labels.filter (trueEar G F)).length || hasClosedLink F)

private theorem all_graphs : ∀ G, finiteTest G = true := by
  set_option maxRecDepth 65536 in
  set_option maxHeartbeats 0 in
  decide +kernel

/-- No obstruction predicate or plane embedding is assumed. Our facial
data need only satisfy the Euler count and have no internal closed link. -/
theorem two_facial_ears (G : FiveGraph) (face : Tri → Bool)
    (someEdge : 0 < eCount G)
    (euler : eCount G + 1 ≤ vCount G + (((triples.filter (clique G)).filter face).length))
    (openLinks : hasClosedLink ((triples.filter (clique G)).filter face) = false) :
    2 ≤ (labels.filter (trueEar G ((triples.filter (clique G)).filter face))).length := by
  have check := List.all_eq_true.mp (all_graphs G) _ (filter_subset face (triples.filter (clique G)))
  simp only [someEdge, euler, decide_true, Bool.and_self, Bool.not_true,
    Bool.false_or, openLinks, Bool.or_false, decide_eq_true_eq] at check
  exact check

end DiskFullerene.EndGeometry

namespace DiskFullerene.EndGeometry

def third (t : Tri) (x v : Nat) := (t.find? fun a => a != x && a != v).getD 5

theorem third_table : triples.all (fun t => labels.all (fun x => labels.all (fun v =>
    !(t.contains x && t.contains v && x != v) ||
    let w := third t x v
    t.contains w && labels.contains w && w != x && w != v &&
      triples.all (fun u => !(u.contains x && u.contains v && u.contains w) || t == u)))) = true := by
  decide +kernel

private theorem max_mem {α : Type} (p : α → Nat) {l : List α} (ne : l ≠ []) :
    ∃ v ∈ l, ∀ u ∈ l, p u ≤ p v := by
  induction l with
  | nil => exact (ne rfl).elim
  | cons a as ih =>
    by_cases empty : as = []
    · subst as; exact ⟨a,by simp,by simp⟩
    obtain ⟨v,hv,big⟩ := ih empty
    by_cases order : p a ≤ p v
    · exact ⟨v,by simp [hv],by intro u hu; rcases List.mem_cons.mp hu with rfl|hu; exact order; exact big u hu⟩
    · exact ⟨a,by simp,by intro u hu; rcases List.mem_cons.mp hu with rfl|hu; omega; have := big u hu; omega⟩

/-- A rotation opened at a boundary neighbor provides distinct positions
for interior neighbors. Edges of each incident all-interior triangular
face join consecutive positions (they cannot pass through the cut). -/
structure LinearLinks (F : List Tri) where
  pos : Nat → Nat → Nat
  distinct : ∀ x a b, a ∈ labels → b ∈ labels → pos x a = pos x b → a = b
  step : ∀ t ∈ F, ∀ x ∈ t, ∀ v ∈ t, x ≠ v →
    pos x (third t x v) + 1 = pos x v ∨ pos x v + 1 = pos x (third t x v)

private theorem polygon_table :
    polygons.all (fun s => !s.isEmpty && s.all labels.contains) = true := by decide

theorem open_of_linear {F : List Tri} (faces : F ⊆ triples) (nodup : F.Nodup)
    (L : LinearLinks F) : hasClosedLink F = false := by
  apply List.any_eq_false.mpr
  intro x hx
  rw [Bool.not_eq_true]
  apply List.any_eq_false.mpr
  intro s hs closed
  simp only [closedAt,Bool.and_eq_true_iff,Bool.not_eq_true',List.all_eq_true,
    decide_eq_true_eq] at closed
  have tab := List.all_eq_true.mp polygon_table s hs
  simp only [Bool.and_eq_true_iff,Bool.not_eq_true',List.all_eq_true,
    List.contains_iff_mem, List.isEmpty_eq_false_iff] at tab
  obtain ⟨v,hv,large⟩ := max_mem (L.pos x) tab.1
  have hvL := tab.2 v hv
  have hxv : x ≠ v := by intro e; cases e; simp [hv] at closed
  let hit (t : Tri) := t.contains x && t.contains v && t.all (fun w => w == x || s.contains w)
  have two : 2 ≤ (F.filter hit).length := by simpa [hit,List.countP_eq_length_filter] using closed.2 v hv
  have dn := nodup.filter hit
  cases eg : F.filter hit with
  | nil => simp [eg] at two
  | cons a rest =>
    cases rest with
    | nil => simp [eg] at two
    | cons b tail =>
      have cnt (t : Tri) (mem : t ∈ F.filter hit) :
          t ∈ F ∧ x ∈ t ∧ v ∈ t ∧ ∀ w ∈ t, w = x ∨ w ∈ s := by
        simpa [hit,List.all_eq_true,Bool.and_assoc] using (List.mem_filter.mp mem)
      have prop (t : Tri) (mem : t ∈ F.filter hit) :
          (L.pos x (third t x v) + 1 = L.pos x v) ∧ third t x v ∈ labels ∧
            ∀ u ∈ triples, x ∈ u → v ∈ u → third t x v ∈ u → t = u := by
        have ⟨ht,hxt,hvt,hsall⟩ := cnt t mem
        have part := List.all_eq_true.mp (List.all_eq_true.mp
          (List.all_eq_true.mp third_table t (faces ht)) x hx) v hvL
        simp [hxt,hvt,hxv,List.all_eq_true,Bool.and_assoc] at part
        obtain ⟨hw,hwL,hwx,_,uniq⟩ := part
        have hwS := (hsall _ hw).resolve_left hwx
        have bound := large _ hwS
        have step := L.step t ht x hxt v hvt hxv
        exact ⟨by omega,hwL,fun u hu hxu hvu hwu => by simpa [hxu,hvu,hwu] using uniq u hu⟩
      have ma : a ∈ F.filter hit := by simp [eg]
      have mb : b ∈ F.filter hit := by simp [eg]
      obtain ⟨p,pa,ua⟩ := prop a ma
      obtain ⟨q,pb,_⟩ := prop b mb
      have same := L.distinct x _ _ pa pb (by omega)
      have ⟨hb,hxb,hvb,_⟩ := cnt b mb
      have thirdB := List.all_eq_true.mp (List.all_eq_true.mp
        (List.all_eq_true.mp third_table b (faces hb)) x hx) v hvL
      simp [hxb,hvb,hxv,List.all_eq_true,Bool.and_assoc] at thirdB
      have e := ua b (faces hb) hxb hvb (same ▸ thirdB.1)
      subst b
      simp [eg] at dn

end DiskFullerene.EndGeometry

namespace DiskFullerene.EndGeometry

def consecutive (n i j : Nat) :=
  i+1 = j ∨ j+1 = i ∨ (i=0 ∧ j+1=n) ∨ (j=0 ∧ i+1=n)

/-- The full cyclic row at each interior vertex, started at a boundary
neighbor. Labels 0,...,4 are reserved for the possible interior vertices.
The corners test only raw incidence: the other two vertices of each
incident face are consecutive in the full rotation. -/
structure CornerRows (F : List Tri) where
  start : Nat → Nat
  tail : Nat → List Nat
  startOutside : ∀ x, 5 ≤ start x
  corners : ∀ t ∈ F, ∀ x ∈ t, ∀ v ∈ t, x ≠ v →
    let row := start x :: tail x
    let w := third t x v
    v ∈ row ∧ w ∈ row ∧ consecutive row.length (row.idxOf v) (row.idxOf w)

private def position (neighbors : List Nat) (a : Nat) :=
  if a ∈ neighbors then neighbors.idxOf a else neighbors.length + a

private theorem position_injective (neighbors : List Nat) {a b : Nat} :
    position neighbors a = position neighbors b → a = b := by
  unfold position
  by_cases aMem : a ∈ neighbors <;> by_cases bMem : b ∈ neighbors <;> simp [aMem,bMem]
  · intro e
    have ha := List.idxOf_lt_length_iff.mpr aMem
    have hb := List.idxOf_lt_length_iff.mpr bMem
    calc a = neighbors[neighbors.idxOf a] := (List.getElem_idxOf ha).symm
         _ = neighbors[neighbors.idxOf b] := by simp [e]
         _ = b := List.getElem_idxOf hb
  · have := List.idxOf_lt_length_iff.mpr aMem; omega
  · have := List.idxOf_lt_length_iff.mpr bMem; omega

private theorem trip_mem {t : Tri} (ht : t ∈ triples) {a : Nat} (ha : a ∈ t) :
    a ∈ labels := by
  have table : triples.all (fun t => t.all labels.contains) = true := by decide
  exact List.contains_iff_mem.mp (List.all_eq_true.mp ((List.all_eq_true.mp table) t ht) a ha)

def linearFromRows {F : List Tri} (hf : F ⊆ triples) (R : CornerRows F) : LinearLinks F where
  pos x v := position (R.tail x) v
  distinct _ _ _ _ _ := position_injective _
  step := by
    intro t ht x hx v hv ne
    have xt := trip_mem (hf ht) hx
    have vt := trip_mem (hf ht) hv
    have tab := List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp third_table t (hf ht)) x xt) v vt
    simp [hx,hv,ne,Bool.and_assoc] at tab
    have z := R.startOutside x
    have table : labels.all (fun x => x < 5) = true := by decide
    have small (a) (mem : a ∈ labels) : a < 5 := by simpa using List.all_eq_true.mp table a mem
    have nv : R.start x ≠ v := by have := small v vt; omega
    have nw : R.start x ≠ third t x v := by have := small _ tab.2.1; omega
    obtain ⟨vm,wm,steps⟩ := R.corners t ht x hx v hv ne
    simp [Ne.symm nv, Ne.symm nw] at vm wm
    unfold consecutive at steps
    simp [List.idxOf_cons, nv,nw] at steps
    simp [position,vm,wm]
    omega

/-- The Euler count of the interior core follows from the *whole disk*
Euler identity and the incidence of the edges joining its two vertex
classes. Mixed triangles have two crossing edges; every crossing edge
is incident with two mixed triangles. Boundary edges form one cycle. -/
theorem innerEuler (b i innerEdges cross innerFaces mixed : Nat)
    (wholeEuler : (b+i) + (innerFaces+mixed) = (b+cross+innerEdges)+1)
    (crossIncidence : 2*cross = 2*mixed) :
    innerEdges+1 = i+innerFaces := by omega

theorem ears_of_rows (G : Lower.FiveGraph) (face : Tri → Bool)
    (R : CornerRows ((triples.filter (clique G)).filter face)) (edge : 0 < eCount G)
    (b cross mixed : Nat)
    (wholeEuler : (b+vCount G) + (((triples.filter (clique G)).filter face).length + mixed) =
      (b+cross+eCount G)+1) (crossIncidence : 2*cross = 2*mixed) :
    2 ≤ (labels.filter (trueEar G ((triples.filter (clique G)).filter face))).length := by
  have incl : (triples.filter (clique G)).filter face ⊆ triples :=
    fun t ht => (List.mem_filter.mp (List.mem_filter.mp ht).1).1
  have nd := ((show triples.Nodup from by decide).filter (clique G)).filter face
  exact two_facial_ears G face edge (Nat.le_of_eq (innerEuler _ _ _ _ _ _ wholeEuler crossIncidence))
    (open_of_linear incl nd (linearFromRows incl R))

end DiskFullerene.EndGeometry

namespace DiskFullerene.EndGeometry

private theorem free_three_table : ∀ (d : Fin 7) (a b : Fin 6),
    (d.val = 5 ∨ d.val = 6) → a.val < d.val → b.val < d.val →
    (a.val=b.val ∨ consecutive d.val a.val b.val) →
    ∃ i : Fin 6, i.val < d.val ∧ ∀ j : Fin 3,
      (i.val+j.val)%d.val ≠ a.val ∧ (i.val+j.val)%d.val ≠ b.val := by
  set_option maxRecDepth 8192 in
  unfold consecutive
  decide +kernel

/-- If an interior vertex has just one interior neighbor, or two which
are together on an incident triangle, all three corners of a consecutive
run in its rotation are boundary neighbors. The conclusion concerns the
actual vertex labels in the row. -/
theorem ear_boundary_run (row : List Nat) (a b : Nat)
    (d : row.length = 5 ∨ row.length = 6) (ha : a < row.length) (hb : b < row.length)
    (adj : a = b ∨ consecutive row.length a b)
    (inside : ∀ j (hj : j < row.length), row[j] < 5 → j=a ∨ j=b) :
    ∃ i, i < row.length ∧ ∀ j : Fin 3,
      5 ≤ row[(i+j.val)%row.length]'(Nat.mod_lt _ (by omega)) := by
  obtain ⟨i,hi,h⟩ := free_three_table ⟨row.length,by omega⟩ ⟨a,by omega⟩ ⟨b,by omega⟩ d ha hb adj
  refine ⟨i.val,hi,?_⟩
  intro j
  have pos : (i.val+j.val)%row.length < row.length := Nat.mod_lt _ (by omega)
  have avoid := h j
  change (i.val+j.val)%row.length ≠ a ∧ (i.val+j.val)%row.length ≠ b at avoid
  have l := inside _ pos
  omega

/-- In a boundary link path (with both ends labelled as boundary), the
two triangles against the boundary edges cannot leave a second interior
neighbor if their third vertex is the same. -/
theorem boundary_link_closes (line : List Nat) (u a c : Nat)
    (distinct : a ≠ c) (hu : u ∈ line) (ha : a ∈ line) (hc : c ∈ line)
    (outerA : line.idxOf a = 0 ∨ line.idxOf a+1=line.length)
    (outerC : line.idxOf c = 0 ∨ line.idxOf c+1=line.length)
    (angleA : line.idxOf a+1=line.idxOf u ∨ line.idxOf u+1=line.idxOf a)
    (angleC : line.idxOf c+1=line.idxOf u ∨ line.idxOf u+1=line.idxOf c)
    (inside : ∀ w ∈ line, w < 5 → 0 < line.idxOf w ∧ line.idxOf w+1 < line.length) :
    line.length = 3 ∧ ∀ w ∈ line, w < 5 → w = u := by
  have au := List.idxOf_lt_length_iff.mpr hu
  have aa := List.idxOf_lt_length_iff.mpr ha
  have ac := List.idxOf_lt_length_iff.mpr hc
  have neq : line.idxOf a ≠ line.idxOf c := by
    intro e; apply distinct
    calc a = line[line.idxOf a] := (List.getElem_idxOf aa).symm
         _ = line[line.idxOf c] := by simp [e]
         _ = c := List.getElem_idxOf ac
  refine ⟨by omega,?_⟩
  intro w hw small
  have hw' := inside w hw small
  have hi := List.idxOf_lt_length_iff.mpr hw
  have eq : line.idxOf w = line.idxOf u := by omega
  calc w = line[line.idxOf w] := (List.getElem_idxOf hi).symm
       _ = line[line.idxOf u] := by simp [eq]
       _ = u := List.getElem_idxOf au

end DiskFullerene.EndGeometry

namespace DiskFullerene.EndGeometry
open Lower

private theorem small_iff (w : Nat) : w ∈ labels ↔ w < 5 := by simp [labels]; omega

abbrev rowAt {F} (R : CornerRows F) (u : Nat) := R.start u :: R.tail u

theorem facial_ear_positions {G : FiveGraph} {F : List Tri} (R : CornerRows F)
    (hf : F ⊆ triples) (u : Nat) (hu : u ∈ labels) (he : trueEar G F u = true)
    (rel : ∀ v, v < 5 → (v ∈ rowAt R u ↔ v ∈ innerNeighbors G u))
    (nd : (rowAt R u).Nodup) :
    let row := rowAt R u
    ∃ a b, a < row.length ∧ b < row.length ∧ (a=b ∨ consecutive row.length a b) ∧
      ∀ i (hi : i < row.length), row[i] < 5 → i=a ∨ i=b := by
  let r := rowAt R u
  have small {v} (m : v ∈ innerNeighbors G u) : v < 5 :=
    (small_iff v).mp (List.mem_filter.mp m).1
  have mem {v} (m : v ∈ innerNeighbors G u) : v ∈ r := (rel v (small m)).mpr m
  have pin (i : Nat) (hi : i < r.length) (sm : r[i] < 5) :
      r[i] ∈ innerNeighbors G u := (rel _ sm).mp (List.getElem_mem hi)
  cases q : innerNeighbors G u with
  | nil => simp [trueEar,q] at he
  | cons v vs =>
    have mv : v ∈ innerNeighbors G u := by simp [q]
    have hv := List.idxOf_lt_length_iff.mpr (mem mv)
    cases vs with
    | nil =>
      refine ⟨r.idxOf v,r.idxOf v,hv,hv,Or.inl rfl,?_⟩
      intro i hi sm
      have h := pin i hi sm
      have eq : r[i] = v := by simpa [q] using h
      exact Or.inl (by simpa [←eq] using (List.Nodup.idxOf_getElem nd i hi).symm)
    | cons w ws =>
      have mw : w ∈ innerNeighbors G u := by simp [q]
      have hw := List.idxOf_lt_length_iff.mpr (mem mw)
      cases ws with
      | cons a s => simp [trueEar,q] at he
      | nil =>
        simp only [trueEar,q,List.any_eq_true,Bool.and_eq_true_iff,List.contains_iff_mem] at he
        obtain ⟨t,ft,⟨ut,vt⟩,_⟩ := he
        have ne : u ≠ v := by
          have adj := (List.mem_filter.mp mv).2; intro e; subst v
          simp [Lower.adjacent] at adj
        obtain ⟨_,tm,adj⟩ := R.corners t ft u ut v vt ne
        have tab := List.all_eq_true.mp (List.all_eq_true.mp
          (List.all_eq_true.mp third_table t (hf ft)) u hu) v ((small_iff v).mpr (small mv))
        simp [ut,vt,ne,Bool.and_assoc] at tab
        have thirdIn := (rel _ ((small_iff _).mp tab.2.1)).mp tm
        have eq : third t u v = w := by
          have hv' := tab.2.2.2.1
          simpa [q,hv'] using thirdIn
        rw [eq] at adj
        refine ⟨r.idxOf v,r.idxOf w,hv,hw,Or.inr adj,?_⟩
        intro i hi sm
        have h := pin i hi sm
        have e : r[i]=v ∨ r[i]=w := by simpa [q] using h
        rcases e with e | e
        · exact Or.inl (by simpa [←e] using (List.Nodup.idxOf_getElem nd i hi).symm)
        · exact Or.inr (by simpa [←e] using (List.Nodup.idxOf_getElem nd i hi).symm)

end DiskFullerene.EndGeometry

namespace DiskFullerene.EndGeometry
open Lower

def atRound (r : List Nat) (i : Nat) := r[i%r.length]?.getD 5

def Angle (line : List Nat) (u a : Nat) : Prop :=
  u ∈ line ∧ a ∈ line ∧ (line.idxOf a+1 = line.idxOf u ∨ line.idxOf u+1 = line.idxOf a)

/-- Local incidence data for a chordless triangulated end. The stored
boundary rows omit the pole and the exterior; each is a *linear* link.
A consecutive pair of boundary neighbors in an interior rotation gives a
triangular face, which must give a consecutive corner in both boundary
rows. We never assume that such a corner singles out a neighbor. -/
structure EndRows (G : FiveGraph) (F : List Tri) extends CornerRows F where
  marks : Nat × Nat
  seamThird : Nat
  line : Nat → List Nat
  rotationDegree : ∀ u ∈ labels, innerNeighbors G u ≠ [] →
    (rowAt toCornerRows u).length = 5 ∨ (rowAt toCornerRows u).length = 6
  rotationSimple : ∀ u ∈ labels, (rowAt toCornerRows u).Nodup
  innerEdges : ∀ u ∈ labels, ∀ v, v < 5 → (v ∈ rowAt toCornerRows u ↔ v ∈ innerNeighbors G u)
  exteriorEnds : ∀ b, 5 ≤ b → ∀ a ∈ line b, 5 ≤ a →
    (line b).idxOf a = 0 ∨ (line b).idxOf a+1 = (line b).length
  interiorSpots : ∀ b, 5 ≤ b → ∀ a ∈ line b, a < 5 →
    0 < (line b).idxOf a ∧ (line b).idxOf a+1 < (line b).length
  incidentCorners : ∀ u ∈ labels, ∀ i : Nat,
    let r := rowAt toCornerRows u
    let a := atRound r i
    let b := atRound r (i+1)
    5 ≤ a → 5 ≤ b → Angle (line b) u a ∧ Angle (line a) u b
  openArcDegree : ∀ b, 5 ≤ b → b ≠ marks.1 → b ≠ marks.2 → 4 ≤ (line b).length
  seamFace : seamThird < 5 ∧ seamThird ∈ line marks.1 ∧ seamThird ∈ line marks.2

theorem ear_is_third {G F} (R : EndRows G F) (faces : F ⊆ triples)
    {u : Nat} (ul : u ∈ labels) (he : trueEar G F u = true) : u = R.seamThird := by
  have pos := facial_ear_positions R.toCornerRows faces u ul he (R.innerEdges u ul)
    (R.rotationSimple u ul)
  obtain ⟨a,b,ha,hb,adj,inside⟩ := pos
  have occupied : innerNeighbors G u ≠ [] := by intro nil; simp [trueEar,nil] at he
  let r := rowAt R.toCornerRows u
  have degree := R.rotationDegree u ul occupied
  change r.length = 5 ∨ r.length = 6 at degree
  obtain ⟨i,hi,h⟩ := ear_boundary_run r a b degree ha hb adj inside
  let v := atRound r i
  let w := atRound r (i+1)
  let z := atRound r (i+2)
  have bound (j : Nat) : j % r.length < r.length := Nat.mod_lt _ (by omega)
  have round (j : Nat) : atRound r j = r[j%r.length]'(bound j) := by
    simp [atRound,List.getElem?_eq_getElem (bound j)]
  have hv : 5 ≤ v := by simpa [v,round] using h 0
  have hw : 5 ≤ w := by simpa [w,round] using h 1
  have hz : 5 ≤ z := by simpa [z,round] using h 2
  have vz : v ≠ z := by
    intro eq
    have eq' : r[i%r.length]'(bound i) = r[(i+2)%r.length]'(bound (i+2)) := by simpa only [v,z,round] using eq
    have nd := R.rotationSimple u ul
    change r.Nodup at nd
    have ij := congrArg (fun v => r.idxOf v) eq'
    simp only [List.Nodup.idxOf_getElem nd] at ij
    rcases degree with d|d <;> simp only [d] at ij hi <;> omega
  obtain ⟨au,av,ea⟩ := (R.incidentCorners u ul i hv hw).1
  obtain ⟨_,az,ez⟩ := (R.incidentCorners u ul (i+1) hw hz).2
  have result := boundary_link_closes (R.line w) u v z vz au av az
    (R.exteriorEnds w hw v av hv) (R.exteriorEnds w hw z az hz) ea ez (R.interiorSpots w hw)
  have uniq := result.2 R.seamThird
  have seam := R.seamFace
  by_cases left : w=R.marks.1
  · exact (uniq (left ▸ seam.2.1) seam.1).symm
  by_cases right : w=R.marks.2
  · exact (uniq (right ▸ seam.2.2) seam.1).symm
  have low := R.openArcDegree w hw left right
  have three := result.1
  omega

/-- A small end is impossible directly from the full disk Euler count,
mixed edge incidence, and the vertex rotations and degrees just above.
This lemma does not assume an enclosed star or a planar core obstruction. -/
theorem no_small_rotated_end (G : FiveGraph) (face : Tri → Bool)
    (R : EndRows G ((triples.filter (clique G)).filter face)) (edge : 0 < eCount G)
    (b cross mixed : Nat)
    (wholeEuler : (b+vCount G) + (((triples.filter (clique G)).filter face).length + mixed) =
      (b+cross+eCount G)+1) (crossIncidence : 2*cross = 2*mixed) : False := by
  let F := (triples.filter (clique G)).filter face
  have lo := ears_of_rows G face R.toCornerRows edge b cross mixed wholeEuler crossIncidence
  have subF : F ⊆ triples := fun t ht => (List.mem_filter.mp (List.mem_filter.mp ht).1).1
  have sub : (labels.filter (trueEar G F)) ⊆ [R.seamThird] := by
    intro u hu
    have h := List.mem_filter.mp hu
    simp [ear_is_third R subF h.1 h.2]
  have nd : (labels.filter (trueEar G F)).Nodup := (show labels.Nodup from by decide).filter (trueEar G F)
  have high := nd.length_le_of_subset sub
  change 2 ≤ (labels.filter (trueEar G F)).length at lo
  simp only [List.length_cons,List.length_nil] at high
  omega

/-- A one-sided Euler bound for the interior subcomplex already suffices;
it can be obtained from connectedness of the complementary dual complex. -/
theorem no_small_end_from_core (G : FiveGraph) (face : Tri → Bool)
    (R : EndRows G ((triples.filter (clique G)).filter face)) (edge : 0 < eCount G)
    (core : eCount G+1 ≤ vCount G + ((triples.filter (clique G)).filter face).length) : False := by
  let F := (triples.filter (clique G)).filter face
  have subF : F ⊆ triples := fun t ht => (List.mem_filter.mp (List.mem_filter.mp ht).1).1
  have nd := ((show triples.Nodup from by decide).filter (clique G)).filter face
  have lo := two_facial_ears G face edge core
    (open_of_linear subF nd (linearFromRows subF R.toCornerRows))
  have sub : labels.filter (trueEar G F) ⊆ [R.seamThird] := by
    intro u hu
    have h := List.mem_filter.mp hu
    simp [ear_is_third R subF h.1 h.2]
  have dn : (labels.filter (trueEar G F)).Nodup := (show labels.Nodup from by decide).filter _
  have bound := dn.length_le_of_subset sub
  change 2 ≤ (labels.filter (trueEar G F)).length at lo
  simp at bound
  omega

end DiskFullerene.EndGeometry
