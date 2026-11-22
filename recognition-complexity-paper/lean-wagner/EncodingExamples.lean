import Triangulation.SourceBridge
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-! Small instances printed in the verification appendix. Tests of a marker
family require an actual matching of the selected endpoint set. -/
namespace Recognition.EncodingExamples
open Recognition.Reduction Recognition.SourceMap

abbrev Pair := Nat × Nat

def choices (k : Nat) : List Pair :=
  (List.range (2*k+1)).flatMap fun u =>
    ((List.range (2*k+1)).filter (fun v => u<v)).map (fun v => (u,v))

def assignments (ps : List Pair) : Nat → List (List Pair)
  | 0 => [[]]
  | k+1 => ps.flatMap fun p => (assignments ps k).map (p::·)

theorem choices_spec (k a b : Nat) : (a,b) ∈ choices k ↔ a<b ∧ b<2*k+1 := by
  simp [choices]; omega

theorem choices_distinct (k : Nat) : (choices k).Nodup := by
  unfold choices
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    exact ((List.nodup_range).filter _).map (fun x y eq => congrArg Prod.snd eq)
  · apply List.nodup_range.imp
    intro a b ne _ ha hb
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,_,eq⟩ := List.mem_map.mp hb
    exact ne (congrArg Prod.fst eq).symm

theorem assignments_spec (ps : List Pair) (k : Nat) (xs : List Pair) :
    xs ∈ assignments ps k ↔ xs.length=k ∧ ∀ x∈xs, x∈ps := by
  induction k generalizing xs with
  | zero => cases xs <;> simp [assignments]
  | succ k ih => cases xs <;> simp [assignments,ih] <;> grind

theorem assignments_distinct (ps : List Pair) (h : ps.Nodup) (k : Nat) :
    (assignments ps k).Nodup := by
  induction k with
  | zero => simp [assignments]
  | succ k ih =>
    rw [assignments,List.nodup_flatMap]
    constructor
    · intro a _; exact ih.map (fun x y eq => (List.cons.inj eq).2)
    · apply h.imp
      intro a b ne x ha hb
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,_,eq⟩ := List.mem_map.mp hb
      exact ne (List.cons.inj eq).1.symm

def testClasses (k width : Nat) : List (List Nat) :=
  let all := List.range k
  all :: (List.range width).flatMap (fun b =>
    [all.filter (fun i => !(i.testBit b)),all.filter (fun i => i.testBit b)])

def assign (system : List Pair) : List Nat → List Nat → Bool
  | [], free => free.isEmpty
  | i::is, free => free.any fun v =>
      system[i]?.any (fun (a,b) => v == a || v == b) && assign system is (free.erase v)

/-- Each selected marker is matched bijectively to an allowed endpoint. -/
theorem assign_spec (system : List Pair) (indices free : List Nat) :
    assign system indices free = true ↔ ∃ vs, vs.Perm free ∧
      List.Forall₂ (fun i v => system[i]?.any (fun (a,b) => v == a || v == b) = true) indices vs := by
  induction indices generalizing free with
  | nil => cases free <;> simp [assign,List.forall₂_nil_left_iff]
  | cons i is ih =>
    simp only [assign,List.any_eq_true,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨v,mem,ok,vs,perm,matchings⟩
      exact ⟨v::vs,List.cons_perm_iff_perm_erase.mpr ⟨mem,perm⟩,.cons ok matchings⟩
    · rintro ⟨vs,perm,matchings⟩
      cases matchings with
      | @cons v _ _ _ ok tail =>
        obtain ⟨mem,perm⟩ := List.cons_perm_iff_perm_erase.mp perm
        exact ⟨_,mem,ok,_,perm,tail⟩

def covers (system : List Pair) (indices : List Nat) (side : Nat) : Bool :=
  assign system indices (indices.map (fun i => 2*i+side))

def surviving (k width : Nat) :=
  (assignments (choices k) k).filter (fun system =>
    (testClasses k width).all (fun indices => covers system indices 0 && covers system indices 1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem three_markers :
    (assignments (choices 3) 3).length = 9261 ∧
    surviving 3 2 = [[(0,1),(2,3),(4,5)]] := by decide +kernel

set_option maxRecDepth 10000 in
theorem small_markers :
    (assignments (choices 1) 1).length = 3 ∧ surviving 1 0 = [[(0,1)]] ∧
    (assignments (choices 2) 2).length = 100 ∧ surviving 2 1 = [[(0,1),(2,3)]] := by
  decide +kernel

/-- The three families tested at each number of bins from one through eight. -/
def sample (i : Fin 8) (j : Fin 3) : Instance :=
  let triple := [([4,5,6],15),([7,8,9],24),([6,6,6],18)][j.val]!
  ⟨(List.replicate (i.val+1) triple.1).flatten,i.val+1,triple.2⟩

private def marks (i : Fin 8) (j : Fin 3) : List (Fin (sample i j).bins × Nat) :=
  let I := sample i j
  (List.finRange I.bins).flatMap fun r =>
    (I.weights.drop (3*r.val) |>.take 3).map (fun w => (r,w))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem inputs : ∀ (i : Fin 8) (j : Fin 3), Valid (sample i j) ∧
    (marks i j).map Prod.snd=(sample i j).weights ∧
    ∀ r, (binWeights (marks i j) r).sum=(sample i j).capacity ∧
         (binWeights (marks i j) r).length=3 := by
  unfold Valid
  decide +kernel

theorem source_samples (i : Fin 8) (j : Fin 3) :
    let I := sample i j
    ∃ M, RealizesSource I M ∧ ∀ e ∈ prescribed I,e.left ∈ M.neighbors e.right := by
  obtain ⟨v,ws,bins⟩ := inputs i j
  exact source_prescribed_stacked (sample i j) v ⟨marks i j,ws,bins⟩

end Recognition.EncodingExamples
