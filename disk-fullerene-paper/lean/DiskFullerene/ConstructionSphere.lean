import DiskFullerene.Construction

namespace DiskFullerene.Construction

/-! A finite certificate for the two building blocks and a uniform description
of the family as successive facet sums. Every new block meets the *entire*
prefix exactly in its incoming triangle, and the outgoing facet is distinct. -/

private def verts (t : Triangle) := [t.1,t.2.1,t.2.2]
private def edges (t : Triangle) := [(t.1,t.2.1),(t.2.1,t.2.2),(t.2.2,t.1)]
private def hasEdge (t : Triangle) (e : Nat × Nat) :=
  contains t e.1 && contains t e.2
private def edgeUses (fs : List Triangle) (e : Nat × Nat) := fs.countP (hasEdge · e)

/-- With exactly two old vertices the new triangle meets the old disk along
one boundary edge. With three old vertices it meets it along two boundary
edges, the third edge being new. These are the two elementary disk shellings. -/
private def shellStep (fs : List Triangle) (t : Triangle) : Bool :=
  let v := (verts t).countP (fun a => fs.any (contains · a))
  let old := (edges t).map (edgeUses fs)
  (verts t).Nodup && old.all (· ≤ 1) &&
    ((v == 2 && old.count 1 == 1) || (v == 3 && old.count 1 == 2))

private def shellRest (fs : List Triangle) : List Triangle → Bool
  | [] => false
  | [t] =>
    (verts t).Nodup && (edges t).all (fun e => edgeUses fs e == 1) &&
    (fs.flatMap edges).all (fun e => edgeUses fs e != 1 || hasEdge t e)
  | t :: u :: ts => shellStep fs t && shellRest (t::fs) (u::ts)

/-- A direct PL sphere certificate: shell a disk starting with a triangle,
then close its complete three-edge boundary by the last triangle. -/
def shellSphere : List Triangle → Bool
  | [] => false
  | t::ts => (verts t).Nodup && shellRest [t] ts

def closedCap : List Triangle :=
  endFaces ++ (List.range 6).map (fun i => (12,boundary i,boundary ((i+1)%6)))

def tetrahedron : List Triangle := [(0,1,2),(3,0,1),(3,1,2),(3,0,2)]

theorem summandsShell : shellSphere closedCap = true ∧ shellSphere tetrahedron = true := by decide

inductive Piece (n : Nat) where
  | left
  | strip (i : Fin (n+2))
  | right
deriving DecidableEq

def Piece.position : Piece n → Nat
  | .left => 0
  | .strip i => i.val+1
  | .right => n+3

def Piece.order : Piece n → Nat
  | .left | .right => 13
  | .strip _ => 4

def Piece.faces : Piece n → List Triangle
  | .left | .right => closedCap
  | .strip _ => tetrahedron

open Vertex

private def capLabel (n : Nat) (s : Bool) (i : Nat) : Vertex :=
  if hi : i < 10 then cap s ⟨i,hi⟩
  else if i = 10 then spine (seamZero n s)
  else if i = 11 then spine (seamOne n s)
  else pole

def Piece.label : Piece n → Nat → Vertex
  | .left,i => capLabel n false i
  | .right,i => capLabel n true i
  | .strip j,i => if i < 3 then spine (j.val+i) else pole

def Piece.carries (p : Piece n) (v : Vertex) := ∃ i, i < p.order ∧ p.label i = v

theorem labelsInjective (p : Piece n) (i j : Nat) (hi : i < p.order) (hj : j < p.order)
    (e : p.label i = p.label j) : i = j := by
  cases p <;> simp only [Piece.order] at hi hj <;>
    simp only [Piece.label,capLabel,seamZero,seamOne,Bool.false_eq_true,ite_true,ite_false] at e <;>
    (repeat' first | omega | split at e | simp_all)

theorem carriesCap (s : Bool) (v : Vertex) :
    (∃ i, i < 13 ∧ capLabel n s i = v) ↔
    match v with
    | pole => True
    | cap t _ => s = t
    | spine j => j = seamZero n s ∨ j = seamOne n s := by
  cases v with
  | pole => exact ⟨fun _ => trivial, fun _ => ⟨12,by decide,by simp [capLabel]⟩⟩
  | cap t u =>
    constructor
    · rintro ⟨i,_,h⟩
      unfold capLabel at h
      repeat' first | split at h | simp_all
    · rintro rfl
      exact ⟨u.val,by omega,by simp [capLabel,u.isLt]⟩
  | spine j =>
    constructor
    · rintro ⟨i,_,h⟩
      unfold capLabel at h
      repeat' first | split at h | simp_all
    · rintro (rfl|rfl)
      · exact ⟨10,by decide,by simp [capLabel]⟩
      · exact ⟨11,by decide,by simp [capLabel]⟩

theorem carriesStrip (i : Fin (n+2)) (v : Vertex) :
    (Piece.strip i).carries v ↔ match v with
    | pole => True
    | cap _ _ => False
    | spine j => i.val ≤ j ∧ j ≤ i.val+2 := by
  cases v with
  | pole => exact ⟨fun _ => trivial, fun _ => ⟨3,by simp [Piece.order],by simp [Piece.label]⟩⟩
  | cap s a =>
    apply Iff.intro _ False.elim
    rintro ⟨j,_,e⟩
    simp only [Piece.label] at e; split at e <;> contradiction
  | spine j =>
    constructor
    · rintro ⟨u,_,eq⟩
      simp only [Piece.label] at eq
      split at eq <;> simp_all <;> omega
    · rintro ⟨lo,hi⟩
      exact ⟨j-i.val,show j-i.val < 4 by omega,by simp [Piece.label,show j-i.val < 3 by omega]; omega⟩

def seam (i : Nat) (v : Vertex) := v = pole ∨ v = spine i ∨ v = spine (i+1)

private theorem chooseEarlier (i : Nat) (hr : i < n+2) (hp : 2 ≤ i) :
    ∃ p : Piece n, p.position < i+1 ∧ p.carries (spine i) := by
  refine ⟨.strip ⟨i-1,by omega⟩,show i-1+1 < i+1 by omega,(carriesStrip ..).mpr ?_⟩
  simp; omega

/-- The old complex meets each incoming tetrahedron exactly in w,vᵢ,vᵢ₊₁;
the terminal cap meets the old complex in exactly the last such triple. -/
theorem prefixIntersection (p : Piece n) (hp : p ≠ .left) (v : Vertex) :
    (p.carries v ∧ ∃ q : Piece n, q.position < p.position ∧ q.carries v) ↔
      seam (p.position-1) v := by
  have left (v : Vertex) := @carriesCap n false v
  have right (v : Vertex) := @carriesCap n true v
  change ∀ v, (Piece.left (n:=n)).carries v ↔ _ at left
  change ∀ v, (Piece.right (n:=n)).carries v ↔ _ at right
  cases p with
  | left => contradiction
  | strip i =>
    constructor
    · rintro ⟨hv,q,ord,hq⟩
      rw [carriesStrip] at hv
      cases q <;> cases v <;>
        simp_all [Piece.position, seam,seamZero,seamOne,carriesStrip] <;> omega
    · intro h
      have hi := i.isLt
      simp [Piece.position,seam] at h
      rcases h with rfl|rfl|rfl
      · exact ⟨(carriesStrip ..).mpr trivial,.left,by simp [Piece.position],(left _).mpr trivial⟩
      · refine ⟨(carriesStrip ..).mpr (by simp),?_⟩
        by_cases small : i.val ≤ 1
        · exact ⟨.left,by simp [Piece.position],(left _).mpr (by change i.val = 1 ∨ i.val = 0; omega)⟩
        · exact chooseEarlier _ hi (by omega)
      · refine ⟨(carriesStrip ..).mpr (by simp),?_⟩
        by_cases zero : i.val = 0
        · exact ⟨.left,by simp [Piece.position],(left _).mpr (by simp [seamZero,seamOne,zero])⟩
        · exact ⟨.strip ⟨i.val-1,by omega⟩,show i.val-1+1 < i.val+1 by omega,
            (carriesStrip ..).mpr (by simp <;> omega)⟩
  | right =>
    constructor
    · rintro ⟨hv,q,ord,hq⟩
      rw [right] at hv
      cases q <;> cases v <;> simp_all [Piece.position,seam,seamZero,seamOne,carriesStrip]
    · intro h
      simp [seam,Piece.position] at h
      rcases h with rfl|rfl|rfl
      · exact ⟨(right _).mpr trivial,.left,by simp [Piece.position],(left _).mpr trivial⟩
      all_goals
        refine ⟨(right _).mpr (by simp [seamZero,seamOne] <;> omega),.strip ⟨n+1,by omega⟩,
          show n+1+1 < n+3 by omega,(carriesStrip ..).mpr (by simp <;> omega)⟩

def Piece.inFacet : Piece n → Triangle
  | .strip _ => (3,0,1)
  | _ => (12,10,11)

def Piece.outFacet : Piece n → Triangle
  | .strip _ => (3,1,2)
  | _ => (12,10,11)

def Piece.mapsFacet (p : Piece n) (t : Triangle) (j : Nat) : Prop :=
  t ∈ p.faces ∧ ∀ v, v ∈ (verts t).map p.label ↔ seam j v

theorem incomingFacet (p : Piece n) (hp : p ≠ .left) :
    p.mapsFacet p.inFacet (p.position-1) := by
  cases p with
  | left => contradiction
  | strip i =>
    constructor
    · simp only [Piece.inFacet,Piece.faces]; decide
    · intro v; simp [Piece.inFacet,verts,Piece.label,seam,Piece.position,or_comm]
  | right =>
    constructor
    · simp only [Piece.inFacet,Piece.faces]; decide
    · intro v; simp [Piece.inFacet,verts,Piece.label,capLabel,seam,seamZero,seamOne,Piece.position,or_comm]

theorem outgoingFacet (p : Piece n) (hp : p ≠ .right) :
    p.mapsFacet p.outFacet p.position := by
  cases p with
  | left =>
    constructor
    · simp only [Piece.outFacet,Piece.faces]; decide
    · intro v; simp [Piece.outFacet,verts,Piece.label,capLabel,seam,seamZero,seamOne,Piece.position,or_comm]
  | right => contradiction
  | strip i =>
    constructor
    · simp only [Piece.outFacet,Piece.faces]; decide
    · intro v; simp [Piece.outFacet,verts,Piece.label,seam,Piece.position,or_comm]

theorem outgoingIsFresh (i : Fin (n+2)) :
    (verts (Piece.strip i).outFacet).map (Piece.strip i).label ≠
      (verts (Piece.strip i).inFacet).map (Piece.strip i).label ∧
      ¬seam i.val (spine (i.val+2)) := by
  simp [Piece.outFacet, Piece.inFacet,verts,Piece.label,seam]

/-- Actual list after deleting each paired facet: the two caps contribute 21
triangles apiece and each tetrahedron contributes its strip triangle and one
cone triangle. -/
def Piece.remaining (p : Piece n) := p.faces.filter fun t =>
  match p with
  | .strip _ => t != p.inFacet && t != p.outFacet
  | .left => t != p.outFacet
  | .right => t != p.inFacet

def Piece.image (p : Piece n) (t : Triangle) : Vertex × Vertex × Vertex :=
  (p.label t.1, p.label t.2.1, p.label t.2.2)

def sphereFaces (n : Nat) :=
  let endPart (p : Piece n) := p.remaining.map p.image
  endPart .left ++ (List.finRange (n+2)).flatMap (fun i => endPart (.strip i)) ++ endPart .right

theorem sphereFaceCount (n : Nat) : (sphereFaces n).length = 2*(n+12)+22 := by
  have c : (Piece.left (n:=n)).remaining.length = 21 := by rfl
  have d : (Piece.right (n:=n)).remaining.length = 21 := by rfl
  have t (i : Fin (n+2)) : (Piece.strip i).remaining.length = 2 := by rfl
  have sumTwos (xs : List (Fin (n+2))) : (xs.map (fun _ => 2)).sum = 2*xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]; omega
  simp [sphereFaces,List.length_flatMap,c,d,t,sumTwos]
  omega

def localAdj (fs : List Triangle) (a b : Nat) : Bool :=
  a != b && fs.any (fun t => contains t a && contains t b)

private theorem capTable : ∀ a b : Fin 14,
    localAdj closedCap a.val b.val =
      (if a.val < 12 ∧ b.val < 12 then capEdge a.val b.val
       else decide (a.val=12 ∧ 6≤b.val ∧ b.val<12 ∨ b.val=12 ∧ 6≤a.val ∧ a.val<12)) := by decide

private theorem tetTable : ∀ a b : Fin 5,
    localAdj tetrahedron a.val b.val = decide (a.val<4 ∧ b.val<4 ∧ a.val≠b.val) := by decide

private def inCap (n : Nat) (s : Bool) (v : Vertex) : Fin 14 :=
  match v with
  | pole => ⟨12,by decide⟩
  | cap t u => if s=t then ⟨u.val,by omega⟩ else ⟨13,by decide⟩
  | spine i => if i=seamZero n s then ⟨10,by decide⟩ else if i=seamOne n s then ⟨11,by decide⟩ else ⟨13,by decide⟩

private def inTet (i : Nat) (v : Vertex) : Fin 5 :=
  match v with
  | pole => ⟨3,by decide⟩
  | cap _ _ => ⟨4,by decide⟩
  | spine j => if h : i ≤ j ∧ j ≤ i+2 then ⟨j-i,by omega⟩ else ⟨4,by decide⟩

def Piece.indexOf : Piece n → Vertex → Nat
  | .left,v => inCap n false v
  | .right,v => inCap n true v
  | .strip i,v => inTet i.val v

theorem indexLabel (p : Piece n) (i : Nat) (hi : i < p.order) : p.indexOf (p.label i) = i := by
  cases p <;> simp only [Piece.order] at hi <;>
    simp only [Piece.label,Piece.indexOf,capLabel,seamZero,seamOne,Bool.false_eq_true,ite_true,ite_false] <;>
    repeat' first | omega | split | simp_all [inCap,inTet,seamZero,seamOne]

def Piece.hasEdge (p : Piece n) (u v : Vertex) := localAdj p.faces (p.indexOf u) (p.indexOf v)

private def endMask (n : Nat) (s : Bool) : Vertex → Bool
  | pole => true
  | cap t _ => s == t
  | spine j => j == seamZero n s || j == seamOne n s

private def tetMask (i : Nat) : Vertex → Bool
  | pole => true
  | cap _ _ => false
  | spine j => decide (i ≤ j ∧ j ≤ i+2)

set_option maxHeartbeats 2000000 in
private theorem maskedCap (s : Bool) (u v : Vertex) :
    localAdj closedCap (inCap n s u) (inCap n s v) =
      (endMask n s u && endMask n s v && adj n u v) := by
  have c10 : (10 : Fin 14).val = 10 := rfl
  have c11 : (11 : Fin 14).val = 11 := rfl
  have c12 : (12 : Fin 14).val = 12 := rfl
  have c13 : (13 : Fin 14).val = 13 := rfl
  have w : capEdge 10 11 = true := by decide
  have w' : capEdge 11 10 = true := by decide
  have d : seamZero n s ≠ seamOne n s := by cases s <;> simp [seamZero,seamOne]
  have near : seamZero n s ≤ seamOne n s + 2 ∧ seamOne n s ≤ seamZero n s + 2 := by
    cases s <;> simp [seamZero,seamOne]
  rw [capTable]
  cases u <;> cases v <;>
    simp only [inCap,endMask,adj,stripEdge,joinEdge,Bool.beq_eq_decide_eq]
  all_goals
    repeat' first
      | split
      | split at *
      | (solve | simp_all [capEdge_comm] <;> omega)
      | simp_all
      | omega
      | decide

set_option maxHeartbeats 1200000 in
private theorem maskedTet (k : Fin (n+2)) (u v : Vertex) :
    localAdj tetrahedron (inTet k.val u) (inTet k.val v) =
      (tetMask k.val u && tetMask k.val v && adj n u v) := by
  have c3 : (3 : Fin 5).val = 3 := rfl
  have c4 : (4 : Fin 5).val = 4 := rfl
  rw [tetTable]
  cases u <;> cases v <;>
    simp only [inTet,tetMask,adj,stripEdge,Bool.false_and,Bool.and_false]
  all_goals repeat' first | omega | split | split at * | simp_all | grind

private def Piece.mask (p : Piece n) : Vertex → Bool :=
  match p with
  | .left => endMask n false
  | .right => endMask n true
  | .strip i => tetMask i.val

private theorem pieceEdges (p : Piece n) (u v : Vertex) :
    p.hasEdge u v = (p.mask u && p.mask v && adj n u v) := by
  cases p
  · exact maskedCap .. 
  · exact maskedTet ..
  · exact maskedCap ..

private def whichCap (n : Nat) : Bool → Piece n
  | false => .left
  | true => .right

private theorem capCover (s : Bool) (a : Fin 10) (v : Vertex) (e : adj n (cap s a) v) :
    (whichCap n s).mask (cap s a) && (whichCap n s).mask v := by
  cases s <;> cases v <;> simp_all [whichCap,Piece.mask,endMask,adj,joinEdge] <;> grind

private theorem spineRange {i : Nat} (h : spine i ∈ vertices n) : i < n+4 := by
  simpa [vertices] using h

private theorem commonPiece (u v : Vertex) (hu : u ∈ vertices n) (hv : v ∈ vertices n)
    (e : adj n u v) : ∃ p : Piece n, p.mask u && p.mask v := by
  cases u with
  | cap s a => exact ⟨whichCap n s,capCover s a v e⟩
  | pole =>
    cases v with
    | cap s a => exact ⟨whichCap n s, by rw [Bool.and_comm]; exact capCover s a pole (adj_symm n (cap s a) pole ▸ e)⟩
    | pole => contradiction
    | spine i =>
      have := spineRange hv
      exact ⟨.strip ⟨min i (n+1),by omega⟩, by simp [Piece.mask,tetMask]; omega⟩
  | spine i =>
    have hi := spineRange hu
    cases v with
    | cap s a => exact ⟨whichCap n s, by rw [Bool.and_comm]; exact capCover s a (spine i) (adj_symm n (cap s a) (spine i) ▸ e)⟩
    | pole => exact ⟨.strip ⟨min i (n+1),by omega⟩,by simp [Piece.mask,tetMask]; omega⟩
    | spine j =>
      have hj := spineRange hv
      simp [adj,stripEdge] at e
      refine ⟨.strip ⟨min (min i j) (n+1),by omega⟩,?_⟩
      simp [Piece.mask,tetMask]
      omega

/-- On the enumerated vertex set, adjacency agrees with the union of the
actual triangular-face 1-skeleta of the summands. Facet sums preserve
this union of edges; only the two identified triangle interiors disappear. -/
theorem adjacencyFromPieces (u v : Vertex) (hu : u ∈ vertices n) (hv : v ∈ vertices n) :
    adj n u v ↔ ∃ p : Piece n, p.hasEdge u v := by
  constructor
  · intro e
    obtain ⟨p,h⟩ := commonPiece u v hu hv e
    exact ⟨p,by simp [pieceEdges,h,e]⟩
  · rintro ⟨p,h⟩
    exact (Bool.and_eq_true_iff.mp ((pieceEdges p u v) ▸ h)).2

def Piece.survivingEdge (p : Piece n) (u v : Vertex) :=
  localAdj p.remaining (p.indexOf u) (p.indexOf v)

private theorem keptCapTable : ∀ a b : Fin 14,
    localAdj (closedCap.filter (· != (12,10,11))) a.val b.val =
    localAdj closedCap a.val b.val := by decide

private theorem keptTetTable : ∀ a b : Fin 5,
    localAdj (tetrahedron.filter (fun t => t != (3,0,1) && t != (3,1,2))) a.val b.val =
    (localAdj tetrahedron a.val b.val &&
      !decide (a.val=3 ∧ b.val=1 ∨ a.val=1 ∧ b.val=3)) := by decide

private def missing (p : Piece n) (u v : Vertex) : Prop :=
  match p with
  | .strip i => (u=pole ∧ v=spine (i.val+1)) ∨ (v=pole ∧ u=spine (i.val+1))
  | _ => False

private theorem keptEdge_iff (p : Piece n) (u v : Vertex) :
    p.survivingEdge u v ↔ (p.hasEdge u v ∧ ¬ missing p u v) := by
  cases p with
  | left => simp only [missing,not_false_eq_true,and_true]; exact Iff.of_eq (congrArg (· = true) (keptCapTable ..))
  | right => simp only [missing,not_false_eq_true,and_true]; exact Iff.of_eq (congrArg (· = true) (keptCapTable ..))
  | strip i =>
    change localAdj _ (inTet i.val u) (inTet i.val v) = true ↔ _
    simp only [Piece.remaining,Piece.faces,Piece.inFacet,Piece.outFacet]
    rw [keptTetTable]
    change (_ && _) = true ↔ localAdj tetrahedron (inTet i.val u) (inTet i.val v) = true ∧ _
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    apply and_congr_right
    intro _
    cases u <;> cases v <;>
      simp only [missing,inTet]
    all_goals
      repeat' first | split | omega | simp_all | grind

private theorem poleEdgeSurvives (j : Nat) (h : j<n+4) :
    ∃ p : Piece n, p.survivingEdge pole (spine j) := by
  let i : Fin (n+2) := ⟨if j<n+2 then j else j-2,by split <;> omega⟩
  have between : i.val ≤ j ∧ j ≤ i.val+2 := by dsimp [i]; split <;> omega
  have notMiddle : j ≠ i.val+1 := by dsimp [i]; split <;> omega
  refine ⟨.strip i,(keptEdge_iff ..).mpr ⟨?_,?_⟩⟩
  · simp [pieceEdges,Piece.mask,tetMask,adj,between]
  · simp [missing,notMiddle]

theorem adjacencySurvives (u v : Vertex) (hu : u ∈ vertices n) (hv : v ∈ vertices n) :
    adj n u v ↔ ∃ p : Piece n, p.survivingEdge u v := by
  constructor
  · intro e
    obtain ⟨p,hp⟩ := (adjacencyFromPieces u v hu hv).mp e
    by_cases miss : missing p u v
    · cases p <;> simp only [missing] at miss
      rcases miss with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact poleEdgeSurvives _ (spineRange hv)
      · obtain ⟨q,hq⟩ := poleEdgeSurvives _ (spineRange hu)
        refine ⟨q,?_⟩
        unfold Piece.survivingEdge localAdj at hq ⊢
        simpa only [bne_comm,Bool.and_comm (contains _ _) (contains _ _)] using hq
    · exact ⟨p,(keptEdge_iff ..).mpr ⟨hp,miss⟩⟩
  · rintro ⟨p,h⟩
    exact (adjacencyFromPieces _ _ hu hv).mpr ⟨p,((keptEdge_iff ..).mp h).1⟩

private theorem labelIndex (p : Piece n) (v : Vertex) (h : p.indexOf v < p.order) :
    p.label (p.indexOf v) = v := by
  have carried : p.carries v := by
    cases p with
    | left =>
      apply (carriesCap false v).mpr
      cases v <;> simp only [Piece.indexOf,Piece.order,inCap] at h
      all_goals repeat' first | trivial | split at h | exact False.elim (by omega) | simp_all
    | right =>
      apply (carriesCap true v).mpr
      cases v <;> simp only [Piece.indexOf,Piece.order,inCap] at h
      all_goals repeat' first | trivial | split at h | exact False.elim (by omega) | simp_all
    | strip i =>
      apply (carriesStrip i v).mpr
      cases v <;> simp only [Piece.indexOf,Piece.order,inTet] at h
      all_goals repeat' first | trivial | split at h | exact False.elim (by omega) | simp_all
  obtain ⟨a,ha,rfl⟩ := carried
  rw [indexLabel p a ha]

private theorem localValid (p : Piece n) {t : Triangle} (ht : t ∈ p.remaining)
    {a : Nat} (ha : a ∈ verts t) : a < p.order := by
  have bounds : p.remaining.all (fun f => (verts f).all (fun i => decide (i < p.order))) := by
    cases p <;> simp only [Piece.remaining,Piece.inFacet,Piece.outFacet,Piece.faces,Piece.order] <;> rfl
  exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp bounds) t ht)) a ha)

def triangleVertices (t : Vertex × Vertex × Vertex) := [t.1,t.2.1,t.2.2]

private theorem imageMember (p : Piece n) (ht : t ∈ p.remaining) (v : Vertex) :
    contains t (p.indexOf v) ↔ v ∈ triangleVertices (p.image t) := by
  have hm (a : Nat) : contains t a ↔ a ∈ verts t := by simp [contains,verts,or_assoc]
  rw [hm]
  change _ ↔ v ∈ (verts t).map p.label
  constructor
  · intro h
    exact List.mem_map.mpr ⟨_,h,labelIndex p v (localValid p ht h)⟩
  · intro h
    obtain ⟨a,ma,rfl⟩ := List.mem_map.mp h
    rwa [indexLabel p a (localValid p ht ma)]

private theorem retainedIncidence (p : Piece n) (u v : Vertex) :
    p.survivingEdge u v ↔ u ≠ v ∧ ∃ t ∈ p.remaining,
      u ∈ triangleVertices (p.image t) ∧ v ∈ triangleVertices (p.image t) := by
  simp only [Piece.survivingEdge,localAdj,Bool.and_eq_true,List.any_eq_true,bne_iff_ne]
  constructor
  · rintro ⟨ne,t,ht,hu,hv⟩
    exact ⟨fun e => ne (congrArg p.indexOf e),t,ht,(imageMember p ht u).mp hu,(imageMember p ht v).mp hv⟩
  · rintro ⟨ne,t,ht,hu,hv⟩
    have a := (imageMember p ht u).mpr hu
    have b := (imageMember p ht v).mpr hv
    refine ⟨?_,t,ht,a,b⟩
    intro eq
    have hu' : p.indexOf u ∈ verts t := by simpa [contains,verts,or_assoc] using a
    have hv' : p.indexOf v ∈ verts t := by simpa [contains,verts,or_assoc] using b
    exact ne ((labelIndex p u (localValid p ht hu')).symm.trans
      ((congrArg p.label eq).trans (labelIndex p v (localValid p ht hv'))))

private theorem memSphereFaces (f : Vertex × Vertex × Vertex) :
    f ∈ sphereFaces n ↔ ∃ (p : Piece n) (t : Triangle), t ∈ p.remaining ∧ p.image t = f := by
  simp only [sphereFaces,List.mem_append,List.mem_map,List.mem_flatMap,List.mem_finRange,
    true_and,List.append_assoc]
  constructor
  · rintro (h|h|h)
    · obtain ⟨t,ht,rfl⟩ := h; exact ⟨.left,t,ht,rfl⟩
    · obtain ⟨i,t,ht,rfl⟩ := h; exact ⟨.strip i,t,ht,rfl⟩
    · obtain ⟨t,ht,rfl⟩ := h; exact ⟨.right,t,ht,rfl⟩
  · rintro ⟨p,t,ht,rfl⟩
    cases p with
    | left => exact Or.inl ⟨_,ht,rfl⟩
    | strip i => exact Or.inr (Or.inl ⟨i,t,ht,rfl⟩)
    | right => exact Or.inr (Or.inr ⟨_,ht,rfl⟩)

/-- An edge of the degree-certified graph is exactly a pair of distinct
vertices sharing one of the final triangular faces, after all seam facets
have been removed. -/
theorem adjacencyFromFaces (u v : Vertex) (hu : u ∈ vertices n) (hv : v ∈ vertices n) :
    adj n u v ↔ u ≠ v ∧ ∃ f ∈ sphereFaces n,
      u ∈ triangleVertices f ∧ v ∈ triangleVertices f := by
  rw [adjacencySurvives u v hu hv]
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨ne,t,ht,a,b⟩ := (retainedIncidence ..).mp hp
    exact ⟨ne,p.image t,(memSphereFaces _).mpr ⟨p,t,ht,rfl⟩,a,b⟩
  · rintro ⟨ne,f,hf,a,b⟩
    obtain ⟨p,t,ht,rfl⟩ := (memSphereFaces _).mp hf
    exact ⟨p,(retainedIncidence ..).mpr ⟨ne,t,ht,a,b⟩⟩

/-- Every position 0 through n+3 occurs exactly once in the gluing order. -/
theorem pieceAt (j : Nat) (hj : j < n+4) : ∃ p : Piece n,
    p.position = j ∧ ∀ q : Piece n, q.position = j → q = p := by
  have inj (p q : Piece n) (eq : p.position = q.position) : p = q := by
    cases p <;> cases q <;> simp_all [Piece.position] <;> omega
  suffices ∃ p : Piece n, p.position = j by
    obtain ⟨p,e⟩ := this; exact ⟨p,e,fun q h => inj q p (h.trans e.symm)⟩
  by_cases zero : j=0
  · exact ⟨.left,zero.symm⟩
  by_cases last : j=n+3
  · exact ⟨.right,last.symm⟩
  exact ⟨.strip ⟨j-1,by omega⟩,by simp [Piece.position]; omega⟩

/-- An outgoing facet is still exposed when the next piece is attached:
its last spine vertex belongs to none of the earlier pieces. -/
theorem outgoingExposed (r p : Piece n) (lt : r.position < p.position) :
    ¬r.carries (spine (p.position+1)) := by
  have hp : p.position ≤ n+3 := by cases p <;> simp [Piece.position] <;> omega
  cases r with
  | left =>
    change 0 < p.position at lt
    have h := @carriesCap n false (spine (p.position+1))
    change (Piece.left (n:=n)).carries _ ↔ _ at h
    rw [h]
    simp [seamZero,seamOne]; omega
  | strip i =>
    change i.val+1 < p.position at lt
    rw [carriesStrip]
    simp; omega
  | right => change n+3 < p.position at lt; omega

/-- Checkable certificate for this *explicit* simplicial facet-sum family.
The index n is h−12. The final field records the edge relation of its
remaining triples, so the degree inventory refers to this same construction. -/
structure FacetSumCertificate (n : Nat) : Prop where
  pieces : ∀ p : Piece n, shellSphere p.faces
  chart : ∀ (p : Piece n) i j, i < p.order → j < p.order → p.label i = p.label j → i=j
  indexing : ∀ j, j < n+4 → ∃ p : Piece n,
    p.position=j ∧ ∀ q : Piece n, q.position=j → q=p
  overlaps : ∀ p : Piece n, p ≠ .left → ∀ v,
    (p.carries v ∧ ∃ q : Piece n, q.position < p.position ∧ q.carries v) ↔ seam (p.position-1) v
  incoming : ∀ p : Piece n, p ≠ .left → p.mapsFacet p.inFacet (p.position-1)
  outgoing : ∀ p : Piece n, p ≠ .right → p.mapsFacet p.outFacet p.position
  fresh : ∀ (r p : Piece n), r.position < p.position → ¬r.carries (spine (p.position+1))
  edgeFaces : ∀ u ∈ vertices n, ∀ v ∈ vertices n,
    adj n u v ↔ u ≠ v ∧ ∃ f ∈ sphereFaces n, u ∈ triangleVertices f ∧ v ∈ triangleVertices f

theorem assembled (n : Nat) : FacetSumCertificate n := by
  refine ⟨?_,labelsInjective,pieceAt,prefixIntersection,incomingFacet,outgoingFacet,outgoingExposed,?_⟩
  · intro p; cases p <;> first | exact summandsShell.1 | exact summandsShell.2
  · intro u hu v hv; exact adjacencyFromFaces u v hu hv

/-- Uniform dual construction, including the endpoint h=12. -/
theorem extremalDualFamily (h : Nat) (hh : 12 ≤ h) :
    ∃ n, n+12=h ∧ FacetSumCertificate n ∧ (vertices n).Nodup ∧
      (sphereFaces n).length = 2*h+22 ∧
      (vertices n).countP (fun v => degree n v == h) = 1 ∧
      (vertices n).countP (fun v => degree n v == 5) = h+6 ∧
      (vertices n).countP (fun v => degree n v == 6) = 6 := by
  obtain ⟨n,rfl⟩ : ∃ n, h=n+12 := ⟨h-12,by omega⟩
  exact ⟨n,rfl,assembled n,vertices_nodup n,sphereFaceCount n,degreeInventory n⟩

end DiskFullerene.Construction
