import Witness

/-! A finite verifier for the labelled, uncompressed face certificate. -/
namespace Recognition.TraceCheck
open PlanarDegrees PlanarDegrees.Frontier PlanarDegrees.Topology Recognition.Witness SparseBoundary

/-- Reach one new face through a shared side. The surplus fuel case is
included so the checker has a structural recursion on an ordinary integer. -/
def flood {α : Type} [DecidableEq α] (adj : α → α → Bool) :
    Nat → List α → List α → Bool
  | 0, _, rest => rest.isEmpty
  | k+1, seen, rest =>
    match rest.find? (fun x => seen.any (adj · x)) with
    | some x => flood adj k (x::seen) (rest.erase x)
    | none => rest.isEmpty

private theorem flood_spec {α : Type} [DecidableEq α] (adj : α → α → Bool) (r : α)
    (k : Nat) (seen rest : List α) (fuel : rest.length ≤ k) (nd : rest.Nodup)
    (cover : ∀ x, x ∈ seen ∨ x ∈ rest) (disj : ∀ x ∈ rest, x ∉ seen)
    (root : r ∈ seen) (reach : ∀ x ∈ seen, Walk (fun a b => adj a b = true) r x) :
    flood adj k seen rest = true ↔ ∀ x, Walk (fun a b => adj a b = true) r x := by
  induction k generalizing seen rest with
  | zero =>
    have nil : rest=[] := List.length_eq_zero_iff.mp (by omega)
    subst rest
    simp [flood]
    exact fun x => reach _ ((cover x).resolve_right (by simp))
  | succ k ih =>
    rw [flood]
    split
    next x hx =>
      have hin := List.mem_of_find?_eq_some hx
      obtain ⟨u,hu,edge⟩ := List.any_eq_true.mp (List.find?_some (p := fun x => seen.any (adj · x)) hx)
      apply ih
      · rw [List.length_erase_of_mem hin]; omega
      · exact nd.erase _
      · intro a
        by_cases eq : a=x
        · simp [eq]
        · rcases cover a with h|h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr (nd.mem_erase_iff.mpr ⟨eq,h⟩)
      · intro a ha
        obtain ⟨ne,hrest⟩ := nd.mem_erase_iff.mp ha
        simp [ne,disj a hrest]
      · exact List.mem_cons_of_mem _ root
      · intro a ha
        rcases List.mem_cons.mp ha with rfl|ha
        · exact (reach _ hu).step edge
        · exact reach _ ha
    next hn =>
      constructor
      · intro h x
        have nil : rest = [] := List.isEmpty_iff.mp h
        exact reach _ ((cover _).resolve_right (by simp [nil]))
      · intro conn
        have closed {a b} (ha : a ∈ seen) (hab : adj a b = true) : b ∈ seen := by
          rcases cover b with h|h
          · exact h
          · exact False.elim (List.find?_eq_none.mp hn b h (List.any_eq_true.mpr ⟨a,ha,hab⟩))
        have all (x) : x ∈ seen := by
          have walk := conn x
          induction walk with
          | refl => exact root
          | step _ edge inside => exact closed inside edge
        apply List.isEmpty_iff.mpr
        exact List.eq_nil_iff_forall_not_mem.mpr (fun x h => disj x h (all x))

def connected {f : Nat} (adj : Fin (f+1) → Fin (f+1) → Bool) :=
  flood adj (f+1) [0] ((List.finRange _).erase 0)

theorem connected_spec {f : Nat} (adj : Fin (f+1) → Fin (f+1) → Bool) :
    connected adj ↔ ∀ z, Walk (fun a b => adj a b = true) 0 z := by
  apply flood_spec
  · rw [List.length_erase_of_mem (List.mem_finRange _)]; simp
  · exact (List.nodup_finRange _).erase _
  · intro x; by_cases eq : x=0 <;> simp [eq,List.mem_erase_of_ne]
  · intro x h
    obtain ⟨ne,_⟩ := (List.nodup_finRange _).mem_erase_iff.mp h
    simp [ne]
  · simp
  · intro x h; obtain rfl := List.mem_singleton.mp h; exact .refl

def shareBit {f} (faces : Fin (f+1) → Face) (a b : Fin (f+1)) :=
  (a != b) && (sideNames (faces a)).any (fun d => (sideNames (faces b)).contains d)

theorem share_spec {f} (fs : Fin (f+1) → Face) (a b : Fin (f+1)) :
    shareBit fs a b = true ↔ shared fs a b := by simp [shareBit,shared,List.any_eq_true]

/-- Typed fixed-width fields. Each row consists of three vertex-name words
and three color bits. The vertex and face parameters below encode positive
orders as v+1 and f+1. -/
structure Record (w : Nat) where
  x : BitVec w
  y : BitVec w
  z : BitVec w
  xy : Bool
  xz : Bool
  yz : Bool

def Record.valid {w} (s : Record w) (n : Nat) : Prop :=
  s.x.toNat < s.y.toNat ∧ s.y.toNat < s.z.toNat ∧ s.z.toNat < n

instance {w} (s : Record w) (n : Nat) : Decidable (s.valid n) := by unfold Record.valid; infer_instance

def Record.face {w n} (s : Record w) (h : s.valid n) : Face :=
  ⟨s.x.toNat,s.y.toNat,s.z.toNat,h.1,h.2.1,s.xy,s.xz,s.yz⟩

abbrev Records (v f : Nat) := Vector (Record (cost v)) (f+1)

def recordsOf {v f} (C : ClosedTrace v f) : Records v f :=
  Vector.ofFn fun z =>
    let F := C.faces z
    ⟨BitVec.ofNat _ F.x,BitVec.ofNat _ F.y,BitVec.ofNat _ F.z,F.redXY,F.redXZ,F.redYZ⟩

private theorem trunc {v i : Nat} (h : i<v+1) : (BitVec.ofNat (cost v) i).toNat = i := by
  have := (cost_brackets v).2
  simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : i<2^cost v)]

private theorem original {v f} (C : ClosedTrace v f) (z : Fin (f+1)) :
    ((recordsOf C)[z.val]).valid (v+1) ∧
    ∀ h : ((recordsOf C)[z.val]).valid (v+1), ((recordsOf C)[z.val]).face h = C.faces z := by
  have bound := C.bounded z
  have xy := (C.faces z).xy
  have yz := (C.faces z).yz
  have hx := trunc (v := v) (i := (C.faces z).x) (by omega)
  have hy := trunc (v := v) (i := (C.faces z).y) (by omega)
  have hz := trunc (v := v) bound
  constructor
  · simpa only [recordsOf,Vector.getElem_ofFn,Record.valid,hx,hy,hz] using And.intro xy (And.intro yz bound)
  · intro h
    cases eq : C.faces z with
    | mk a b c d e p q r =>
      simp only [eq] at hx hy hz
      simp [recordsOf,Record.face,eq,hx,hy,hz]

private def test (ds : List Nat) (v : Nat) {f : Nat} (fs : Fin (f+1) → Face) :=
  (List.finRange (v+1)).all (fun x => (List.finRange (f+1)).any
    (fun i => (cornerNames (fs i)).contains x.val)) &&
  connected (shareBit fs) &&
  match replay (sideTrace fs) with
  | none => false
  | some s => s.pending.isEmpty && decide (((List.range (v+1)).map s.redDegree).Perm ds)

/-- Check all labels, flood the face dual, replay the colors, and test the
terminal multiset. The histogram may be consumed in arbitrary vertex order. -/
def verify (ds : List Nat) {v f} (record : Records v f) : Bool :=
  if ds.length = v+1 ∧ (f+1)+4 = 2*(v+1) ∧ 4 ≤ v+1 then
    if good : ∀ i : Fin (f+1), (record[i]).valid (v+1) then
      test ds v (fun i => (record[i]).face (good i))
    else false
  else false

private theorem covered {v f : Nat} (fs : Fin (f+1) → Face) :
    (List.finRange (v+1)).all (fun x => (List.finRange (f+1)).any
        (fun i => (cornerNames (fs i)).contains x.val)) ↔
    ∀ x : Fin (v+1), ∃ i, x.val ∈ cornerNames (fs i) := by
  simp [List.all_eq_true,List.any_eq_true]

private theorem reach_iff {f} (fs : Fin (f+1) → Face) :
    connected (shareBit fs) ↔ ∀ z, Walk (shared fs) 0 z := by
  rw [connected_spec]
  have eq : (fun a b => shareBit fs a b = true) = shared fs :=
    funext fun a => funext fun b => propext (share_spec fs a b)
  rw [eq]

/-- Soundness includes the witness that the concrete checker actually read. -/
theorem verify_sound (ds : List Nat) {v f} (r : Records v f) (yes : verify ds r) :
    ds.length=v+1 ∧ (f+1)+4=2*(v+1) ∧ 4≤v+1 ∧
      ∃ C : ClosedTrace v f, (witnessDegrees C).Perm ds ∧
        ∀ (i : Fin (f+1)) (h : (r[i]).valid (v+1)), (r[i]).face (n := v+1) h = C.faces i := by
  unfold verify at yes
  split at yes <;> rename_i size
  · split at yes <;> rename_i good
    · let fs := fun i : Fin (f+1) => (r[i]).face (good i)
      change test ds v fs = true at yes
      unfold test at yes
      cases hs : replay (sideTrace fs) with
      | none => simp [hs] at yes
      | some s =>
        simp only [hs,Bool.and_eq_true] at yes
        obtain ⟨⟨vertices,conn⟩,closed,multiset⟩ := yes
        let C : ClosedTrace v f := ⟨fs, fun i => (good i).2.2, (covered fs).mp vertices,
          (reach_iff fs).mp conn, s, hs, List.isEmpty_iff.mp closed⟩
        exact ⟨size.1,size.2.1,size.2.2,C,of_decide_eq_true multiset,fun _ _ => rfl⟩
    · contradiction
  · contradiction

theorem verify_complete (ds : List Nat) {v f} (C : ClosedTrace v f)
    (h4 : 4≤v+1) (F : (f+1)+4=2*(v+1)) (degrees : (witnessDegrees C).Perm ds) :
    verify ds (recordsOf C) := by
  have len : ds.length=v+1 := by simpa [witnessDegrees] using degrees.length_eq.symm
  have good : ∀ i : Fin (f+1), ((recordsOf C)[i]).valid (v+1) := fun i => (original C i).1
  have eq : (fun i => ((recordsOf C)[i]).face (good i)) = C.faces :=
    funext fun i => (original C i).2 _
  have size := And.intro len (And.intro F h4)
  rw [verify, ite_eq_left size,dite_eq_left good]
  change test ds v (fun i => ((recordsOf C)[i]).face (good i)) = true
  rw [eq]
  simp only [test,C.accepted,C.closed,List.isEmpty_nil,Bool.and_eq_true]
  exact ⟨⟨(covered _).mpr C.used,(reach_iff _).mpr C.connected⟩,trivial,decide_eq_true degrees⟩

/-- For the prescribed face count the certificate has this many bits without
padding or vertex names in the output graph. -/
theorem certificate_bits (v f : Nat) (h : (f+1)+4=2*(v+1)) :
    (f+1)*(3*cost v+3) ≤ 6*(v+1)*(v.log2+3) := by
  have hi : cost v ≤ v.log2+2 := by
    have hu := Nat.lt_log2_self (n := v)
    by_cases v0 : v=0
    · subst v; decide
    · have hp := (cost_brackets v).1
      unfold cost at *
      have hh : v+1 < 2^(v.log2+2) := by
        rw [show v.log2+2=v.log2+1+1 by omega,Nat.pow_succ]; omega
      have l := (Nat.log2_lt (n := v+1) (by omega)).mpr hh
      omega
  have a := Nat.mul_le_mul (show f+1 ≤ 2*(v+1) by omega) (show 3*cost v+3 ≤ 3*(v.log2+3) by omega)
  exact Nat.le_trans a (by grind)

end Recognition.TraceCheck

namespace Recognition.TraceCheck
open PlanarDegrees PlanarDegrees.Frontier PlanarDegrees.Topology Recognition.Witness SparseBoundary

/-- Build the packed red graph of the records when all three names in every
row are well formed. Calling verify additionally checks closure and degrees. -/
def readGraph {v f} (record : Records v f) : Option (Graph (v+1)) :=
  if good : ∀ i : Fin (f+1), (record[i]).valid (v+1) then
    let fs := fun i => (record[i]).face (good i)
    some (graph (v+1) (reds (sideTrace fs)))
  else none

theorem readGraph_recordsOf {v f} (C : ClosedTrace v f) :
    readGraph (recordsOf C) = some (witnessGraph C) := by
  have good : ∀ i : Fin (f+1), ((recordsOf C)[i]).valid (v+1) := fun i => (original C i).1
  have eq : (fun i => ((recordsOf C)[i]).face (good i)) = C.faces :=
    funext (fun i => (original C i).2 _)
  simp only [readGraph,dite_eq_left good,eq,witnessGraph]

/-- The certificate checker has a computable graph output with the exact
degree multiset. The connected terminal vertex links belong to the same
triangles as this output. -/
theorem verify_recovers_witness (ds : List Nat) {v f} (r : Records v f) (h : verify ds r) :
    ∃ C : ClosedTrace v f, readGraph r = some (witnessGraph C) ∧
      (witnessDegrees C).Perm ds ∧ Graphic ds ∧
      ∃ G : Gluing v f C.ledger.sealed.length,
        (∀ z, (G.tri z).corners.map Fin.val = cornerNames (C.faces z)) ∧
        (∀ d, ((G.primal d).1.val,(G.primal d).2.val) =
          ((C.ledger.sealed[d.val]).lo,(C.ledger.sealed[d.val]).hi)) ∧
        (∀ x a b, x ∈ (G.tri a).corners → x ∈ (G.tri b).corners → Walk (G.link x) a b) := by
  obtain ⟨_,count,_,C,perm,matchRow⟩ := verify_sound ds r h
  refine ⟨C,?_,perm,graph_of_histogram C ds perm,(C.terminal_certificate count).2.2⟩
  have good : ∀ i : Fin (f+1), (r[i]).valid (v+1) := by
    unfold verify at h
    split at h <;> first | contradiction | split at h <;> first | assumption | contradiction
  have eq : (fun i : Fin (f+1) => (r[i]).face (good i)) = C.faces := funext (fun i => matchRow i _)
  rw [readGraph, dite_eq_left good]
  change some (graph _ (reds (sideTrace (fun i : Fin (f+1) => (r[i]).face (good i))))) = _
  rw [eq]
  rfl

theorem certificate_iff (ds : List Nat) (v f : Nat) (h4 : 4≤v+1) (faces : (f+1)+4=2*(v+1)) :
    (∃ r : Records v f, verify ds r) ↔ ∃ C : ClosedTrace v f, (witnessDegrees C).Perm ds := by
  constructor
  · rintro ⟨r,yes⟩
    obtain ⟨_,_,_,C,p,_⟩ := verify_sound ds r yes
    exact ⟨C,p⟩
  · rintro ⟨C,h⟩
    exact ⟨recordsOf C,verify_complete ds C h4 faces h⟩

end Recognition.TraceCheck
