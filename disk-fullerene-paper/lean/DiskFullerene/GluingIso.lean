import DiskFullerene.CapRing
import DiskFullerene.Strip
import DiskFullerene.Construction

namespace DiskFullerene.GluingIso

structure End where
  pat : CapRing.Pattern
  fan : CapRing.Index
  second : Bool

def End.ok (e : End) := CapRing.Compatible e.pat e.fan e.second

def End.active (e : End) (v : CapRing.Label) : Bool :=
  (CapRing.faces e.pat).any (fun t => CapRing.includesVertex t v.val) &&
    !CapRing.marked e.pat e.fan e.second v

/-- In a compatible cap, the lower-load endpoint is the new subdivision
vertex. The higher-load endpoint is the corner on the marked segment. -/
def End.weak (e : End) := CapRing.midpoint e.fan
def End.strong (e : End) := CapRing.corner (if e.second then CapRing.next e.fan else e.fan)

/-- Local appendix labels in Construction: center, rim 0,...,4 and
b₂,...,b₅. In CapRing the reference marks corner 0 to midpoint 0;
this reversal sends it to the appendix edge b₁ to b₀. -/
def base (u : Fin 10) : CapRing.Label :=
  ([0,1,5,4,3,2,10,9,8,7] : List (Fin 16))[u.val]?.getD 0

def End.place (e : End) (u : Fin 10) := CapRing.relabel e.fan e.second (base u)

structure LocalAgreement (e : End) : Prop where
  active : ∀ v, e.active v = true ↔ ∃ u, e.place u = v
  injective : ∀ u v, e.place u = e.place v → u = v
  boundary : ∀ u, 6 ≤ (e.place u).val ↔ 6 ≤ u.val
  edge : ∀ u v, CapRing.adjacent e.pat (e.place u).val (e.place v).val =
    Construction.capEdge u.val v.val
  weak : ∀ u, CapRing.adjacent e.pat (e.place u).val e.weak = Construction.capEdge u.val 10
  strong : ∀ u, CapRing.adjacent e.pat (e.place u).val e.strong = Construction.capEdge u.val 11

private theorem normal_agreement (i : CapRing.Index) (s : Bool) :
    LocalAgreement ⟨CapRing.singletonPattern i,i,s⟩ := by
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 0 in
  constructor <;> decide +revert +kernel

theorem local_agreement (e : End) (ok : e.ok) : LocalAgreement e := by
  rcases e with ⟨p,i,s⟩
  obtain rfl := (CapRing.classify p i s).mp ok
  exact normal_agreement i s

structure Assembly where
  ends : Bool → End
  moves : List Strip.Side
  finalGluing : Strip.Gluing

def Assembly.Legal (A : Assembly) : Prop :=
  (∀ b, (A.ends b).ok) ∧ Strip.Complete ⟨3,2⟩ A.moves A.finalGluing

/-- Actual terminal chord after following the chosen triangles. -/
def finalSeam (x y fresh : Nat) : List Strip.Side → Nat × Nat
  | [] => (x,y)
  | side :: rest => finalSeam (match side with | .left => x | .right => y) fresh (fresh+1) rest

private theorem final_right (a n : Nat) :
    finalSeam a (a+1) (a+2) (List.replicate n .right) = (a+n,a+n+1) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ,finalSeam,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (ih (a+1))

def Assembly.seams (A : Assembly) : Bool → Nat × Nat
  | false => (1,0)
  | true => let e := finalSeam 0 1 2 A.moves
            match A.finalGluing with
            | .twoThree => e
            | .threeTwo => (e.2,e.1)

private theorem seam_formula {A : Assembly} (ok : A.Legal) {n : Nat}
    (len : A.moves.length = n+2) (b : Bool) :
    A.seams b = (Construction.seamZero n b, Construction.seamOne n b) := by
  cases b with
  | false => rfl
  | true =>
    obtain ⟨_,hm,hg⟩ := (Strip.complete_iff _ _).mp ok.2
    have h : A.moves = List.replicate (n+2) .right := hm.trans (by rw [len])
    simp [Assembly.seams,hg,h,final_right,Construction.seamZero,Construction.seamOne]

def lineEdge (A : Assembly) (i j : Nat) : Prop :=
  i ≠ j ∧ ∃ t ∈ Strip.facesFrom 0 1 2 A.moves,
    CapRing.includesVertex t i = true ∧ CapRing.includesVertex t j = true

private theorem line_formula {A : Assembly} (ok : A.Legal) {n i j : Nat}
    (len : A.moves.length = n+2) (hi : i < n+4) (hj : j < n+4) :
    lineEdge A i j ↔ Construction.stripEdge i j = true := by
  simp only [lineEdge,Construction.stripEdge,decide_eq_true_eq,Strip.forced_faces ok.2,len]
  constructor
  · rintro ⟨hd,t,ht,hit,hjt⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    simp [CapRing.includesVertex] at hit hjt
    omega
  · rintro ⟨hd,h₁,h₂⟩
    let a := min (min i j) (n+1)
    have ha : a ∈ List.range' 0 (n+2) := List.mem_range'.mpr ⟨a,by dsimp [a]; omega,by simp⟩
    refine ⟨hd,(a,a+1,a+2),List.mem_map.mpr ⟨a,ha,rfl⟩,?_,?_⟩ <;>
      simp [CapRing.includesVertex,a] <;> omega

inductive Vertex where
  | pole
  | cap (b : Bool) (v : CapRing.Label)
  | spine (i : Nat)
  deriving DecidableEq, Repr

def Valid (A : Assembly) : Vertex → Prop
  | .pole => True
  | .cap b v => (A.ends b).active v = true
  | .spine i => i < A.moves.length+2

def join (A : Assembly) (b : Bool) (v : CapRing.Label) (i : Nat) : Bool :=
  let e := A.ends b
  (CapRing.adjacent e.pat v.val e.weak && i == (A.seams b).1) ||
    (CapRing.adjacent e.pat v.val e.strong && i == (A.seams b).2)

/-- The actual glued adjacency. Cap edges come from the outer-fan
triangles, strip edges from the chosen triangle sequence, and the pole
is joined to all boundary vertices. -/
def Adj (A : Assembly) : Vertex → Vertex → Prop
  | .pole,.pole => False
  | .pole,.cap _ v | .cap _ v,.pole => 6 ≤ v.val
  | .pole,.spine _ | .spine _,.pole => True
  | .cap b v,.cap c w => b = c ∧ CapRing.adjacent (A.ends b).pat v.val w.val = true
  | .spine i,.cap b v | .cap b v,.spine i => join A b v i = true
  | .spine i,.spine j => lineEdge A i j

def place (A : Assembly) : Construction.Vertex → Vertex
  | .pole => .pole
  | .cap b u => .cap b ((A.ends b).place u)
  | .spine i => .spine i

private theorem canonical_mem {n : Nat} (v : Construction.Vertex) :
    v ∈ Construction.vertices n ↔ match v with
      | .spine i => i < n+4 | _ => True := by
  cases v with
  | pole => simp [Construction.vertices]
  | cap b v => cases b <;> simp [Construction.vertices]
  | spine i => simp [Construction.vertices]

private theorem joins_match {A : Assembly} (ok : A.Legal) {n : Nat}
    (len : A.moves.length = n+2) (b : Bool) (u : Fin 10) (i : Nat) :
    join A b ((A.ends b).place u) i = Construction.joinEdge n b u i := by
  have agreement := local_agreement _ (ok.1 b)
  simp [join,Construction.joinEdge,agreement.weak,agreement.strong,seam_formula ok len]

/-- A single explicit graph isomorphism on the full vertex sets. Right
and left cap rotations/reflections are independent; the seam identifications
are determined by the degree constraints. -/
theorem assembled_iso {A : Assembly} (ok : A.Legal) {n : Nat} (len : A.moves.length = n+2) :
    (∀ v, Valid A v ↔ ∃ u ∈ Construction.vertices n, place A u = v) ∧
    (∀ u v, place A u = place A v → u = v) ∧
    (∀ u ∈ Construction.vertices n, ∀ v ∈ Construction.vertices n,
      Adj A (place A u) (place A v) ↔ Construction.adj n u v = true) := by
  refine ⟨?_,?_,?_⟩
  · intro v
    constructor
    · cases v with
      | pole => exact fun _ => ⟨.pole,(canonical_mem _).mpr trivial,rfl⟩
      | spine i =>
        intro h
        exact ⟨.spine i,(canonical_mem _).mpr (by simpa [Valid,len] using h),rfl⟩
      | cap b v =>
        intro h
        obtain ⟨u,hu⟩ := ((local_agreement _ (ok.1 b)).active v).mp h
        exact ⟨.cap b u,(canonical_mem _).mpr trivial,congrArg (Vertex.cap b) hu⟩
    · rintro ⟨u,hu,rfl⟩
      cases u with
      | pole => trivial
      | spine i => simpa [Valid,place,len] using (canonical_mem _).mp hu
      | cap b u => exact ((local_agreement _ (ok.1 b)).active _).mpr ⟨u,rfl⟩
  · intro u v h
    cases u <;> cases v <;> simp [place] at h ⊢
    all_goals try assumption
    obtain ⟨rfl,he⟩ := h
    exact ⟨rfl,(local_agreement _ (ok.1 _)).injective _ _ he⟩
  · intro u hu v hv
    have h₁ := (canonical_mem _).mp hu
    have h₂ := (canonical_mem _).mp hv
    cases u <;> cases v <;> simp only [place,Adj,Construction.adj]
    all_goals first
      | decide
      | simp only [decide_eq_true_eq]; exact (local_agreement _ (ok.1 _)).boundary _
      | trivial
      | exact (local_agreement _ (ok.1 _)).boundary _
      | exact line_formula ok len h₁ h₂
      | rw [joins_match ok len]
      | simp only [Bool.and_eq_true_iff,beq_iff_eq]; apply and_congr_right; rintro rfl
        rw [(local_agreement _ (ok.1 _)).edge]

end DiskFullerene.GluingIso
