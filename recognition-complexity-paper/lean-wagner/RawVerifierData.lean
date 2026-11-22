import RawWire
import ComplexityCost

/-! Metered input validation for the ordinary rotation verifier. Equality of
two dart labels uses a bounded number of word operations. The packed graph
may occupy quadratically many words, so even a bit probe is charged for a
full traversal of its storage and the triangular-index calculation. -/
namespace Recognition.RawVerifierData
open SparseBoundary Wagner RotationVerifier ComplexityCost

def mapM (f : α → Meter β) : List α → Meter (List β)
  | [] => ⟨[],1⟩
  | a::as =>
    let x := f a
    let tail := mapM f as
    ⟨x.value::tail.value,x.work+tail.work+2⟩

theorem map_value (f : α → Meter β) (xs : List α) :
    (mapM f xs).value=xs.map (fun x => (f x).value) := by
  induction xs <;> simp [mapM, *]

theorem map_work (f : α → Meter β) (xs : List α) (k : Nat)
    (bound : ∀ a,(f a).work≤k) : (mapM f xs).work≤xs.length*(k+2)+1 := by
  induction xs with
  | nil => simp [mapM]
  | cons a as ih => simp only [mapM,List.length_cons,Nat.succ_mul];have := bound a;omega

def allM (f : α → Meter Bool) : List α → Meter Bool
  | [] => ⟨true,1⟩
  | a::as =>
    let x := f a
    let tail := allM f as
    ⟨x.value && tail.value,x.work+tail.work+2⟩

theorem all_value (f : α → Meter Bool) (xs : List α) :
    (allM f xs).value=xs.all (fun x => (f x).value) := by
  induction xs <;> simp [allM, *]

theorem all_work (f : α → Meter Bool) (xs : List α) (k : Nat)
    (bound : ∀ a,(f a).work≤k) : (allM f xs).work≤xs.length*(k+2)+1 := by
  induction xs with
  | nil => simp [allM]
  | cons a as ih => simp only [allM,List.length_cons,Nat.succ_mul];have := bound a;omega

/-- One packed adjacency query computes its triangular prefix in at most
`n` additions and probes a bit of a word with at most `n²` bits. -/
def adjFee (n : Nat) := 8*(n+2)^2

/-- Form the Cartesian square of the vertex names, retain adjacent pairs
and package every retained pair as a dart. Each charge is associated to
the list traversed in that stage. -/
def enumerate (G : Graph n) : Meter (List (toSimple G).Dart) :=
  let vs:=List.finRange n
  let ps:=vs.product vs
  let es:=ps.filter (fun p=>G.adj p.1 p.2)
  let ds:=es.attach.map (fun p => (⟨p.val,(List.mem_filter (p:=fun q : Fin n × Fin n => G.adj q.1 q.2)).mp p.property |>.2⟩ : (toSimple G).Dart))
  ⟨ds, (vs.length+1)*(3*vs.length+3)+ps.length*(adjFee n+3)+3*es.length+5⟩

theorem enumerate_value (G : Graph n) : (enumerate G).value=darts G := rfl

theorem enumerate_work (G : Graph n) : (enumerate G).work≤24*(n+2)^4 := by
  change ((List.finRange n).length+1)*(3*(List.finRange n).length+3)+
    ((List.finRange n).product (List.finRange n)).length*(adjFee n+3)+
    3*(((List.finRange n).product (List.finRange n)).filter (fun p=>G.adj p.1 p.2)).length+5≤_
  have f := List.length_filter_le (fun p : Fin n × Fin n => G.adj p.1 p.2)
    ((List.finRange n).product (List.finRange n))
  have pairs : ((List.finRange n).product (List.finRange n)).length=n*n :=
    (List.length_product _ _).trans (by simp)
  rw [pairs] at f ⊢
  simp only [List.length_finRange]
  unfold adjFee
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n^3),Nat.zero_le (n^4)]

private def tableCell {n : Nat} {G : Graph n} (d : (toSimple G).Dart) : Fin (n*n) := ⟨d.fst.val*n+d.snd.val,by
  have s:=d.snd.isLt
  calc
    _ < (d.fst.val+1)*n := by rw [Nat.succ_mul];omega
    _ ≤ _ := Nat.mul_le_mul_right n d.fst.isLt⟩

private def load (G : Graph n) (a : Vector (Fin n × Fin n) (n*n))
    (d : (toSimple G).Dart) : Option ((toSimple G).Dart × (toSimple G).Dart) :=
  let p:=a[(tableCell (G:=G) (n:=n) d).val]
  if h : G.adj p.1 p.2=true then some (d,⟨p,h⟩) else none

/-- Dense successor and predecessor arrays are read one cell per accepted
dart. The error path stops on the first nonedge. -/
def readTable (G : Graph n) (a : Vector (Fin n × Fin n) (n*n)) :
    List (toSimple G).Dart → Meter (Option (OrbitTable.Rows (toSimple G).Dart))
  | [] => ⟨some [],1⟩
  | d::ds =>
    match load G a d with
    | none => ⟨none,adjFee n+n*n+7⟩
    | some p =>
      let t:=readTable G a ds
      ⟨t.value.map (p::·),adjFee n+n*n+7+t.work⟩

theorem table_value (G : Graph n) (a : Vector (Fin n × Fin n) (n*n)) (xs) :
    (readTable G a xs).value=xs.mapM (load G a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases eq : load G a x <;> simp [readTable,eq,ih,List.mapM_cons,Bind.bind]
    cases xs.mapM (load G a) <;> rfl

theorem table_length (G : Graph n) (a : Vector (Fin n × Fin n) (n*n)) {xs r}
    (hit : (readTable G a xs).value=some r) : r.length=xs.length := by
  induction xs generalizing r with
  | nil => cases hit;rfl
  | cons x xs ih =>
    cases eq : load G a x with
    | none => simp [readTable,eq] at hit
    | some p =>
      cases h : (readTable G a xs).value with
      | none => simp [readTable,eq,h] at hit
      | some l => simp [readTable,eq,h] at hit;subst r;simp [ih h]

theorem table_work (G : Graph n) (a : Vector (Fin n × Fin n) (n*n)) (xs) :
    (readTable G a xs).work≤xs.length*(adjFee n+n*n+7)+1 := by
  induction xs with
  | nil => simp [readTable]
  | cons x xs ih => cases eq : load G a x <;>
      simp only [readTable,eq,List.length_cons,Nat.succ_mul] <;> omega

def degrees (ds : List Nat) (G : Graph ds.length) : Meter Bool :=
  let vs:=List.finRange ds.length
  let tested:=allM (fun i:Fin ds.length =>
    let neighbors:=vs.filter (G.adj i)
    ⟨neighbors.length==ds[i],vs.length*(adjFee ds.length+2)+neighbors.length+ds.length+4⟩) vs
  ⟨tested.value,tested.work+vs.length+1⟩

theorem degrees_value (ds : List Nat) (G : Graph ds.length) : (degrees ds G).value=
    (List.finRange ds.length).all (fun i=>G.degree i==ds[i]) := by
  simp only [degrees,all_value,Graph.degree]

theorem degrees_work (ds : List Nat) (G : Graph ds.length) :
    (degrees ds G).work≤24*(ds.length+2)^4 := by
  let n:=ds.length
  let c:=n*(adjFee n+2)+2*n+4
  unfold degrees
  apply Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (all_work _ _ c (fun a=>by
      have hh:= List.length_filter_le (G.adj a) (List.finRange ds.length)
      simp only [List.length_finRange] at hh ⊢;unfold c n;omega)) _) _)
  simp only [List.length_finRange]
  dsimp [c,n,adjFee]
  ring_nf;omega

/-- The last two local equality checks are definitionally the cell order
and dart validation used by the public pure rotation verifier. -/
theorem assembled (ds : List Nat) (C : Raw ds.length) :
    (match (readTable C.graph C.next (darts C.graph)).value,
           (readTable C.graph C.prev (darts C.graph)).value with
     | some f,some g => (degrees ds C.graph).value && checkRotation C.graph ⟨f,g⟩
     | _,_ => false)=verify ds C := by
  rw [table_value,table_value,degrees_value]
  rfl

end Recognition.RawVerifierData
