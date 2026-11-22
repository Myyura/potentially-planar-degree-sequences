import ElementaryCompare
import IncidenceMeter

/-! Cache distinct nonempty incidence rows, then construct the compact
coloured vertex and arc arrays. A row comparison checks membership in
two sets of at most m elements. -/
namespace Recognition.SparseMeter
open StateIso SparseCompare StepCost

theorem block_count (A : Colored m) : (blocks A).length≤m := by
  unfold blocks
  exact ((List.dedup_sublist _).length_le.trans (List.length_filter_le ..)).trans_eq (by simp)

private def rowTest (A : Colored m) (x : Fin m) :=
  (row A x,8*(m+1))

private def read (A : Colored m) (R : Fin m → Finset (Fin m))
    (atBlock : Fin (blocks A).length → Finset (Fin m)) : Node A → Node A → Bool
  | .inl i,.inl j => !(low A i && low A j) && A.edge i j
  | .inl i,.inr b => decide (R i=atBlock b)
  | .inr b,.inl i => decide (i∈atBlock b)
  | .inr _,.inr _ => false

private theorem read_eq (A : Colored m) (x y : Node A) :
    read A (row A) ((blocks A).get) x y=arc A x y := by cases x <;> cases y <;> rfl

private theorem cached (A : Colored m) : (tab (rowTest A)).1=row A := by
  funext i;simp [rowTest]

/-- Materialize the compact coloured graph, including non-equivalence
relations that can occur among unsuccessful catalogue entries. -/
def compact (A : Colored m) : Colored (m+(blocks A).length) × Nat :=
  let rows:=tab (rowTest A)
  let bs:=(((List.finRange m).map rows.1).filter (· != ∅)).dedup.toArray
  let getBlock (b : Fin (blocks A).length) := bs[b.val]'(by simpa [bs,rows,cached,blocks] using b.isLt)
  let colors:=tab fun i : Fin (m+(blocks A).length) => (color A (finSumFinEquiv.symm i),4)
  let edges:=square fun e : QuotientDP.Side (m+(blocks A).length) =>
    (read A rows.1 getBlock (finSumFinEquiv.symm e.1) (finSumFinEquiv.symm e.2),8*(m+1)^2)
  (⟨colors.1,fun i j => edges.1 (i,j)⟩,
    rows.2+8*(m+1)^4+colors.2+edges.2)

@[simp] theorem compact_eq (A : Colored m) : (compact A).1=graph A := by
  have get (b : Fin (blocks A).length) : (blocks A).toArray[b.val]=(blocks A).get b := by simp
  simp only [compact,cached,graph]
  congr 1
  · funext i; exact tab_val _ _
  · funext i j; rw [square_val];exact read_eq A _ _

private def polynomial (m : Nat) :=
  m*(8*(m+1)+2)+1+8*(m+1)^4+(2*m*6+1)+squareBound (2*m) (8*(m+1)^2)

theorem compact_cost (A : Colored m) : (compact A).2 ≤ polynomial m := by
  have br:=block_count A
  have a:=tab_cost (rowTest A) (8*(m+1)) (fun _ => Nat.le_refl _)
  have b (f : Fin (m+(blocks A).length) → Nat) := tab_cost (fun i => (f i,4)) 4 (fun _ => Nat.le_refl _)
  have c (f : QuotientDP.Side (m+(blocks A).length) → Bool) :=
    square_cost (fun e => (f e,8*(m+1)^2)) (8*(m+1)^2) (fun _ => Nat.le_refl _)
  simp only [compact]
  apply (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right a _) (b _)) (c _)).trans
  unfold polynomial squareBound
  gcongr <;> omega

/-- The continuation receives genuine integer-indexed materialized tables.
The degree list and packet labels are no longer scanned by its arc queries. -/
def provide (s : QuotientDP.State n) (f : ∀ k,Colored k → α) : α × Nat :=
  let (A,c):=IncidenceMeter.materialize s
  let (B,t):=compact A
  (f _ B,c+t)

@[simp] theorem provide_val (s : QuotientDP.State n) (f : ∀ k,Colored k → α) :
    (provide s f).1=f (ElementaryCompare.orderSize s) (ElementaryCompare.pattern s) := by
  simp only [provide,compact_eq,ElementaryCompare.pattern]
  exact congrArg (fun G : Colored (StateIncidence.names s).length => f _ (graph G)) (IncidenceMeter.materialize_eq s)

theorem provide_cost (s : QuotientDP.State n) (f : ∀ k,Colored k → α) :
    (provide s f).2 ≤ 12000*(n+2)^10 := by
  have a:=IncidenceMeter.materialize_cost s
  have b:=compact_cost (IncidenceMeter.materialize s).1
  have z:=IncidenceMeter.names_size s
  apply (Nat.add_le_add a b).trans
  apply (Nat.add_le_add_left (show polynomial (StateIncidence.names s).length≤polynomial (n+n^2) by
    unfold polynomial squareBound;gcongr) _).trans
  unfold polynomial squareBound
  ring_nf;omega

/-- Cache preparation and the continuation charge add along each evaluation. -/
def charge (s : QuotientDP.State n) := (provide s fun _ _ => ()).2

def run (s : QuotientDP.State n) (f : ∀ k,Colored k → α × Nat) : α × Nat :=
  let (out,c):=provide s f
  (out.1,c+out.2)

theorem run_eq (s : QuotientDP.State n) (f : ∀ k,Colored k → α × Nat) :
    run s f=
      let out:=f (ElementaryCompare.orderSize s) (ElementaryCompare.pattern s)
      (out.1,charge s+out.2) := by
  simp only [run,provide_val];rfl

theorem charge_cost (s : QuotientDP.State n) : charge s≤12000*(n+2)^10 := provide_cost _ _

end Recognition.SparseMeter
