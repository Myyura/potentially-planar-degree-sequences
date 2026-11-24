import SparseBoundary.GraphWeighted
import SparseBoundary.GraphRootTwo
import SparseBoundary.GraphPetals
import SparseBoundary.GraphContractionCheck

/-! Finite labelled multigraphs, with each unordered nonloop pair stored once.
Planarity means Wagner planarity of the underlying simple support. -/
namespace Combined.Support
open SparseBoundary SparseBoundary.Graph

def vsum {n : Nat} (f : Fin n → Nat) : Nat := (List.ofFn f).sum
@[simp] theorem vsum_zero_dim (f : Fin 0 → Nat) : vsum f=0 := by simp [vsum]
theorem vsum_succ (f : Fin (n+1) → Nat) : vsum f=f 0+vsum (fun i => f i.succ) := by
  simp [vsum,List.ofFn_succ]
theorem vsum_add (f g : Fin n → Nat) : vsum (fun i => f i+g i)=vsum f+vsum g := by
  induction n with
  | zero => simp
  | succ n ih => rw [vsum_succ,vsum_succ f,vsum_succ g,ih]; omega
theorem vsum_le (f g : Fin n → Nat) (le : ∀ i, f i≤g i) : vsum f≤vsum g := by
  induction n with
  | zero => simp
  | succ n ih => rw [vsum_succ,vsum_succ g]; exact Nat.add_le_add (le 0) (ih _ _ (fun i => le i.succ))
@[simp] theorem vsum_zeros (n : Nat) : vsum (fun _ : Fin n => 0)=0 := by
  induction n with | zero => simp | succ n ih => rw [vsum_succ]; simp [ih]
def hit {n : Nat} (i x : Fin n) : Nat := if i=x then 1 else 0
@[simp] theorem vsum_hit (x : Fin n) : vsum (fun i => hit i x)=1 := by
  induction n with
  | zero => exact Fin.elim0 x
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) x
    · rw [vsum_succ]; simp [hit,Fin.succ_ne_zero]
    · rw [vsum_succ]; simpa [hit,Ne.symm (Fin.succ_ne_zero j)] using ih j

def present (x : Nat) : Nat := min x 1
@[simp] theorem present_zero : present 0=0 := rfl
@[simp] theorem present_succ (m : Nat) : present (m+1)=1 := by simp [present]

inductive Multi : Nat → Type
  | nil : Multi 0
  | cons {n : Nat} (loops : Nat) (row : Fin n → Nat) (rest : Multi n) : Multi (n+1)
namespace Multi

def support : Multi n → Graph n
 | .nil => ⟨0⟩
 | .cons _ row rest => adjoinRow (fun i => decide (0<row i)) rest.support

def degree : Multi n → Fin n → Nat
 | .nil => Fin.elim0
 | .cons L row rest => Fin.cases (2*L+vsum row) (fun i => rest.degree i+row i)

def edges : Multi n → Nat
 | .nil => 0
 | .cons L row rest => L+vsum row+rest.edges

def pairs : Multi n → Nat
 | .nil => 0
 | .cons _ row rest => vsum (fun i => present (row i))+rest.pairs

def loops : Multi n → Nat
 | .nil => 0
 | .cons L _ rest => L+rest.loops

def cost : Multi n → Nat
 | .nil => 0
 | .cons L row rest => 2*L+vsum (fun i => row i-present (row i))+rest.cost

theorem handshake (M : Multi n) : vsum M.degree=2*M.edges := by
  induction M with
  | nil => rfl
  | cons L row rest ih => rw [vsum_succ]; simp only [degree,Fin.cases_zero,Fin.cases_succ,edges,vsum_add,ih]; omega

theorem cost_identity (M : Multi n) : M.cost+M.pairs=M.edges+M.loops := by
  induction M with
  | nil => rfl
  | cons L row rest ih =>
    have split := vsum_add (fun i => row i-present (row i)) (fun i => present (row i))
    have point (i) : row i-present (row i)+present (row i)=row i := Nat.sub_add_cancel (Nat.min_le_left _ _)
    have ve : (fun i => row i-present (row i)+present (row i))=row := funext point
    rw [ve] at split
    simp only [cost,pairs,edges,loops]; omega

def bump (row : Fin n → Nat) (x : Fin n) : Fin n → Nat := fun i => row i+hit i x

@[simp] theorem sum_bump (row : Fin n → Nat) (x : Fin n) : vsum (bump row x)=vsum row+1 := by
  unfold bump
  rw [vsum_add,vsum_hit]

/-- Add an undirected edge, including a loop when the endpoints coincide. -/
def addEdge (M : Multi n) (a b : Fin n) : Multi n := match M with
 | .nil => Fin.elim0 a
 | .cons L row rest => Fin.cases
    (Fin.cases (.cons (L+1) row rest) (fun y => .cons L (bump row y) rest) b)
    (fun x => Fin.cases (.cons L (bump row x) rest) (fun y => .cons L row (rest.addEdge x y)) b) a

theorem addEdge_degree (M : Multi n) (a b i : Fin n) :
     (M.addEdge a b).degree i = M.degree i+hit i a+hit i b := by
  induction M with
  | nil => exact Fin.elim0 a
  | cons L row rest ih =>
    refine Fin.cases ?_ (fun x => ?_) a <;> refine Fin.cases ?_ (fun y => ?_) b <;>
      refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [addEdge,degree,ih,Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero _),hit,Nat.add_comm,Nat.add_left_comm] <;> first | omega | simp [bump,hit,Nat.add_assoc]

theorem addEdge_edges (M : Multi n) (a b : Fin n) : (M.addEdge a b).edges=M.edges+1 := by
  have h := M.handshake
  have k := (M.addEdge a b).handshake
  have de : (M.addEdge a b).degree=fun i => (M.degree i+hit i a)+hit i b := funext (M.addEdge_degree a b)
  rw [de,vsum_add,vsum_add,vsum_hit,vsum_hit] at k
  omega

theorem addEdge_loops (M : Multi n) (a b : Fin n) : (M.addEdge a b).loops=M.loops+hit a b := by
  induction M with
  | nil => exact Fin.elim0 a
  | cons L row rest ih =>
    refine Fin.cases ?_ (fun x => ?_) a <;> refine Fin.cases ?_ (fun y => ?_) b <;>
      simp [addEdge,loops,ih,hit,Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero _),Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def linked (a b i j : Fin n) : Bool :=
  (i != j) && ((i==a && j==b) || (i==b && j==a))

theorem addEdge_adj (M : Multi n) (a b i j : Fin n) :
 (M.addEdge a b).support.adj i j = (M.support.adj i j || linked a b i j) := by
  induction M with
  | nil => exact Fin.elim0 a
  | cons L row rest ih =>
    refine Fin.cases ?_ (fun x => ?_) a <;> refine Fin.cases ?_ (fun y => ?_) b <;>
      refine Fin.cases ?_ (fun v => ?_) i <;> refine Fin.cases ?_ (fun w => ?_) j <;>
      simp [addEdge,support,incident,linked,bump,hit,ih] <;> grind

end Multi
end Combined.Support
