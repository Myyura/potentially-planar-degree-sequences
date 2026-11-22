import Mathlib.Tactic.FinCases
import RowRecognition
import SparseBoundary.GraphDeletion

/-! Concrete examples of the ordered row criterion and the obstruction to
discarding its order. All moves below use the same numerical successor as
the recognition theorem. -/
namespace Recognition.IntervalExamples
open RowRule SparseBoundary

abbrev Move (row : List Nat) (d : Nat) (next : List Nat) :=
  ∃ c : NumericalMove row d, c.next = next

/-- The rows after each successive entry in a specified run. -/
def Follows (row : List Nat) : List Nat → List (List Nat) → Prop
  | [], [] => True
  | d :: ds, r :: rs => Move row d r ∧ Follows r ds rs
  | _, _ => False

theorem octahedron_rows :
    Follows [] [4,4,4,4,4,4] [[4],[3,3],[2,2,2],[1,2,1,2],[1,1,1,1],[]] := by
  refine ⟨?_,?_,?_,?_,?_,?_,trivial⟩
  · exact ⟨⟨[],[],[],[],[],rfl,by simp,by simp,by simp,by simp⟩,rfl⟩
  · exact ⟨⟨[],[4],[],[],[],rfl,by simp,by simp,by simp,by simp⟩,rfl⟩
  · exact ⟨⟨[],[3],[],[3],[],rfl,by simp,by simp,by simp,by simp⟩,rfl⟩
  · exact ⟨⟨[],[2],[],[2],[2],rfl,by simp,by simp,by simp,by simp⟩,rfl⟩
  · exact ⟨⟨[1],[2],[1],[2],[],rfl,by simp,by simp,by simp,by simp⟩,rfl⟩
  · exact ⟨⟨[],[],[1,1,1,1],[],[],rfl,by simp,by simp,by simp,by simp⟩,rfl⟩

private theorem follows_trace {r ds rs} (h : Follows r ds rs) {earlier : List Nat}
    (prior : NumericalTrace earlier r) :
    NumericalTrace (earlier++ds) ((rs.getLast?).getD r) := by
  induction ds generalizing earlier r rs with
  | nil => cases rs <;> simp_all [Follows]
  | cons d ds ih =>
    cases rs with
    | nil => exact False.elim h
    | cons s rs =>
      obtain ⟨⟨m,rfl⟩,rest⟩ := h
      have result := ih rest (NumericalTrace.advance prior m)
      cases rs with
      | nil => simpa [List.append_assoc] using result
      | cons x xs =>
        have last := List.getLast?_eq_some_getLast (List.cons_ne_nil x xs)
        simpa [List.append_assoc,last] using result

theorem octahedron_trace : NumericalTrace [4,4,4,4,4,4] [] :=
  follows_trace octahedron_rows NumericalTrace.start

/-- A relaxation of the usual trace allowing a permutation between moves. -/
inductive FreeTrace : List Nat → List Nat → Prop where
  | start : FreeTrace [] []
  | step {ds r d s} : FreeTrace ds r → Move r d s → FreeTrace (ds++[d]) s
  | rearrange {ds r s} : FreeTrace ds r → r.Perm s → FreeTrace ds s

def profile (t : Nat) := [t+2,t+2,t+2] ++ List.replicate t 3

private theorem two_large (t : Nat) : FreeTrace [t+2,t+2] [t+1,t+1] := by
  let first : NumericalMove [] (t+2) := ⟨[],[],[],[],[],rfl,by simp,by simp,by simp,by simp⟩
  have h : FreeTrace [t+2] [t+2] := FreeTrace.step (ds:=[]) .start
    ⟨first,by simp [first,NumericalMove.next]⟩
  let second : NumericalMove [t+2] (t+2) := ⟨[],[t+2],[],[],[],rfl,by simp,by simp,by simp,by simp⟩
  exact FreeTrace.step h ⟨second,by simp [second,NumericalMove.next]⟩

private theorem small_vertices (t k : Nat) (bound : k≤t) :
    FreeTrace ([t+2,t+2] ++ List.replicate k 3)
      ([t+1-k,t+1-k] ++ List.replicate k 1) := by
  induction k with
  | zero => simpa using two_large t
  | succ k ih =>
    have prev := ih (by omega)
    let a := t+1-k
    let xs := List.replicate k 1
    let m : NumericalMove ([a,a]++xs) 3 :=
      ⟨[],[a],[],[a],xs,rfl,by simp,by simp,by simp,by simp⟩
    have pos : 0<a-1 := by dsimp [a];omega
    have paid : m.next = (a-1) :: 1 :: (a-1) :: xs := by
      simp [m,NumericalMove.next,xs,pos]
    have next := FreeTrace.step prev ⟨m,paid⟩
    have sw := (List.Perm.swap (a-1) 1 xs).cons (a-1)
    have moved := FreeTrace.rearrange next sw
    have val : a-1=t+1-(k+1) := by dsimp [a]; omega
    rw [List.replicate_succ' (n:=k) (a:=3),← List.append_assoc]
    simpa [List.replicate_succ,val,xs] using moved

private theorem final_move (t : Nat) : Move ([1,1]++List.replicate t 1) (t+2) [] := by
  let ones := [1,1]++List.replicate t 1
  let m : NumericalMove ones (t+2) := ⟨[],[],ones,[],[],by simp,by decide,by decide,
    by intro x h; simp [ones] at h; tauto,by simp [ones]⟩
  refine ⟨m,?_⟩
  simp [m,NumericalMove.next,ones,List.filter_append]

theorem unordered_accepts (t : Nat) :
    ∃ ds, ds.Perm (profile t) ∧ FreeTrace ds [] := by
  have h : FreeTrace ([t+2,t+2]++List.replicate t 3) ([1,1]++List.replicate t 1) := by
    simpa using small_vertices t t (by omega)
  refine ⟨_,?_,FreeTrace.step h (final_move t)⟩
  simp [profile]

private theorem universal_adj {n : Nat} (G : Graph n) (v w : Fin n)
    (deg : G.degree v+1=n) (ne : w≠v) : G.adj v w=true := by
  classical
  let adj := ((List.finRange n).filter (G.adj v)).toFinset
  have sub : adj ⊆ Finset.univ.erase v := by
    intro x h
    have hit : G.adj v x=true := (List.mem_filter.mp (List.mem_toFinset.mp h)).2
    apply Finset.mem_erase.mpr
    exact ⟨fun eq => by subst x;simp at hit,Finset.mem_univ _⟩
  have card : adj.card=G.degree v := List.toFinset_card_of_nodup
    (List.filter_sublist.nodup (List.nodup_finRange n))
  have eq := Finset.eq_of_subset_of_card_le sub (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,card];omega)
  have hh : w∈adj := eq ▸ Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩
  exact (List.mem_filter.mp (List.mem_toFinset.mp hh)).2

theorem three_universal_nonplanar (t : Nat) (size : 3≤t) : ¬Planaric (profile t) := by
  rintro ⟨G,real,flat⟩
  have len : (profile t).length=t+3 := by simp [profile]
  let f (i : Fin 6) : Fin (profile t).length := ⟨i.val,by have := i.isLt;omega⟩
  have inj : Function.Injective f := fun _ _ eq => Fin.ext (congrArg (fun a : Fin (profile t).length => a.val) eq)
  have maxdeg (i : Fin 6) (hi : i.val<3) : G.degree (f i)+1=(profile t).length := by
    rw [real]
    fin_cases i <;> simp_all [f,profile]
  apply flat.2
  refine ⟨fun i => [f i],?_⟩
  simp only [Graph.minorTest,List.all_eq_true]
  intro i _
  simp [Graph.connected]
  intro j
  constructor
  · by_cases h : i=j
    · simp [h]
    · simp [Graph.disjoint,h,inj.ne h]
  · by_cases h : Graph.biclique33 i j=true
    · have bits : (i.val < 3) ≠ (j.val < 3) := by simpa [Graph.biclique33] using h
      have ne : i≠j := fun eq => by subst j;exact bits rfl
      have arc : G.adj (f i) (f j)=true := by
        by_cases hi : i.val<3
        · exact universal_adj G _ _ (maxdeg i hi) (inj.ne ne.symm)
        · have hj : j.val < 3 := by by_contra hn;exact bits (propext (iff_of_false hi hn))
          rw [Graph.adj_comm]
          exact universal_adj G _ _ (maxdeg j hj) (inj.ne ne)
      simp [Graph.links,h,arc]
    · simp [h]

/-- Allowing arbitrary rearrangement between genuine interval moves gives a
false positive at every order t+3 with t at least three. -/
theorem unordered_counterexample (t : Nat) (ht : 3≤t) :
    (∃ ds, ds.Perm (profile t) ∧ FreeTrace ds []) ∧ ¬Planaric (profile t) :=
  ⟨unordered_accepts t,three_universal_nonplanar t ht⟩

end Recognition.IntervalExamples
