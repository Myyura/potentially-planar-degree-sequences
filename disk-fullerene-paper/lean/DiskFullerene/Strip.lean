import Std

/-! Section 5.1, after the cut disk has been identified as two marked ends
with a path of triangles between them. We allow either old endpoint to stay
at each triangle and both bijections on the last marked edge. -/
namespace DiskFullerene.Strip

inductive Side where
  | left | right
  deriving DecidableEq, Repr

structure Loads where
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def kept (p : Loads) : Side → Nat
  | .left => p.left
  | .right => p.right

def dropped (p : Loads) : Side → Nat
  | .left => p.right
  | .right => p.left

/-- New order of endpoints: the retained endpoint, then the fresh vertex. -/
def after (p : Loads) (keep : Side) : Loads := ⟨kept p keep + 1, 1⟩

def allowed (d : Nat) : Prop := d = 5 ∨ d = 6

inductive Gluing where
  | twoThree | threeTwo
  deriving DecidableEq, Repr

def endLoads : Gluing → Loads
  | .twoThree => ⟨2, 3⟩
  | .threeTwo => ⟨3, 2⟩

/-- Both final endpoints see the other endpoint and the apex. -/
def fits (p : Loads) (g : Gluing) : Prop :=
  allowed (2 + p.left + (endLoads g).left) ∧
    allowed (2 + p.right + (endLoads g).right)

/-- Test exactly the finalized degrees: while crossing a triangle the
dropped endpoint sees its earlier load, the kept endpoint, the fresh vertex,
and the apex. The retained endpoint is tested only when it is finalized. -/
def Complete (p : Loads) : List Side → Gluing → Prop
  | [], g => fits p g
  | side :: rest, g => allowed (3 + dropped p side) ∧ Complete (after p side) rest g

theorem loads_bounded {p : Loads} {choices : List Side} {g : Gluing}
    (hc : Complete p choices g) : p.left ≤ 3 ∧ p.right ≤ 3 := by
  induction choices generalizing p with
  | nil =>
    cases g <;> simp [Complete, fits, endLoads, allowed] at hc <;> omega
  | cons side rest ih =>
    obtain ⟨hdrop, hrest⟩ := hc
    obtain ⟨hkeep, _⟩ := ih hrest
    cases side <;> simp [after, kept, dropped, allowed] at hdrop hkeep <;> omega

/-- The local inequalities in (4) follow from the degrees of the completed
strip. No intermediate upper bound on the retained endpoint was imposed. -/
theorem transition {p : Loads} {side : Side} {rest : List Side} {g : Gluing}
    (hc : Complete p (side :: rest) g) :
    kept p side ≤ 2 ∧ (dropped p side = 2 ∨ dropped p side = 3) := by
  obtain ⟨hdrop, hrest⟩ := hc
  have hkeep := (loads_bounded hrest).1
  simp only [after] at hkeep
  unfold allowed at hdrop
  omega

def canonicalLoads : Nat → Loads
  | 0 => ⟨3, 2⟩
  | 1 => ⟨3, 1⟩
  | _ + 2 => ⟨2, 1⟩

private theorem next_right (n : Nat) :
    after (canonicalLoads n) .right = canonicalLoads (n+1) := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

private theorem right_allowed (n : Nat) :
    allowed (3 + dropped (canonicalLoads n) .right) := by
  cases n with
  | zero => exact Or.inr rfl
  | succ n => cases n <;> simp [allowed, dropped, canonicalLoads]

private theorem must_keep_right {n : Nat} {side : Side} {rest : List Side} {g : Gluing}
    (hc : Complete (canonicalLoads n) (side :: rest) g) : side = .right := by
  cases side with
  | right => rfl
  | left =>
    have h := transition hc
    cases n with
    | zero => simp [canonicalLoads, kept, dropped] at h
    | succ n => cases n <;> simp [canonicalLoads, kept, dropped] at h

private theorem end_iff (n : Nat) (g : Gluing) :
    fits (canonicalLoads n) g ↔ 2 ≤ n ∧ g = .twoThree := by
  cases n with
  | zero => cases g <;> simp [fits, canonicalLoads, endLoads, allowed]
  | succ n =>
    cases n with
    | zero => cases g <;> simp [fits, canonicalLoads, endLoads, allowed]
    | succ n => cases g <;> simp [fits, canonicalLoads, endLoads, allowed]

private theorem suffix_iff (n : Nat) (choices : List Side) (g : Gluing) :
    Complete (canonicalLoads n) choices g ↔
      2 ≤ n + choices.length ∧ choices = List.replicate choices.length .right ∧
      g = .twoThree := by
  induction choices generalizing n with
  | nil => simpa [Complete] using end_iff n g
  | cons side rest ih =>
    constructor
    · intro hc
      obtain rfl := must_keep_right hc
      obtain ⟨_, hrest⟩ := hc
      rw [next_right] at hrest
      obtain ⟨hlen, hword, hend⟩ := (ih (n+1)).mp hrest
      refine ⟨by simp; omega, ?_, hend⟩
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
      exact hword
    · rintro ⟨hlen, hword, hend⟩
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq] at hword
      obtain ⟨rfl, hrest⟩ := hword
      refine ⟨right_allowed n, ?_⟩
      rw [next_right]
      exact (ih (n+1)).mpr ⟨by simp at hlen; omega, hrest, hend⟩

/-- Classification of *all* oriented triangle sequences and final
endpoint identifications between the prescribed marked ends. -/
theorem complete_iff (choices : List Side) (g : Gluing) :
    Complete ⟨3, 2⟩ choices g ↔
      2 ≤ choices.length ∧ choices = List.replicate choices.length .right ∧
      g = .twoThree := by
  simpa [canonicalLoads] using suffix_iff 0 choices g

theorem strip_exists {k : Nat} (hk : 2 ≤ k) :
    Complete ⟨3, 2⟩ (List.replicate k .right) .twoThree :=
  (complete_iff _ _).mpr (by simp [hk])

theorem one_triangle_impossible (side : Side) (g : Gluing) :
    ¬ Complete ⟨3, 2⟩ [side] g := by simp [complete_iff]

abbrev Triangle := Nat × Nat × Nat

/-- Start at seam (x,y), always label the new vertex fresh, and record
the actual triangles. The ordering of the two old endpoints is retained
only to fix labels; no global orientation is chosen here. -/
def facesFrom (x y fresh : Nat) : List Side → List Triangle
  | [] => []
  | side :: rest =>
    (x,y,fresh) :: facesFrom (match side with | .left => x | .right => y) fresh (fresh+1) rest

private theorem right_faces (start len : Nat) :
    facesFrom start (start+1) (start+2) (List.replicate len .right) =
    (List.range' start len).map (fun i => (i,i+1,i+2)) := by
  induction len generalizing start with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.range', List.map_cons, facesFrom]
    exact congrArg _ (ih (start+1))

theorem forced_faces {moves : List Side} {g : Gluing}
    (hc : Complete ⟨3, 2⟩ moves g) :
    facesFrom 0 1 2 moves = (List.range' 0 moves.length).map (fun i => (i,i+1,i+2)) := by
  have heq := ((complete_iff _ _).mp hc).2.1
  calc
    _ = facesFrom 0 1 2 (List.replicate moves.length .right) := congrArg _ heq
    _ = _ := right_faces 0 moves.length

end DiskFullerene.Strip
