import TreeBands

/-! A connected genus-zero dart table has an explicit reversible code of four
bits per dart. Two independent parentheses strings specify the tree and
remaining bands. Doubling the positions represents fixed darts by adjacent
pairs and lets both strings use the ordinary fixed-point-free chord parser. -/
namespace Recognition.RibbonCode
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability PlanarDegrees.MapCode

theorem cyclic {n : Nat} (θ : Perm (Fin n)) (all : ∀ a b, SameCycle θ a b) :
    ∃ e : Perm (Fin n), e.permCongr θ=finRotate n := by
  classical
  obtain _|_|n := n
  · exact ⟨1,Subsingleton.elim _ _⟩
  · exact ⟨1,by ext1 x; apply Fin.ext; have ha := ((1 : Perm (Fin 1)).permCongr θ x).isLt; have hb := (finRotate 1 x).isLt; omega⟩
  have moves (v : Fin (n+2)) : θ v≠v := by
    intro stop
    have const (w) := (all v w).eq_of_left stop
    have z := const 0
    have o := const 1
    have neq : (0 : Fin (n+2))≠1 := by intro h; have := congrArg Fin.val h; simp at this
    exact neq (z.symm.trans o)
  have c : IsCycle θ := ⟨0,moves 0,fun {y} _ => all 0 y⟩
  have sup : θ.support=Finset.univ := Finset.eq_univ_of_forall (fun z => mem_support.mpr (moves z))
  obtain ⟨e,eq⟩ := isConj_iff.mp ((isConj_iff_cycleType_eq (σ := θ) (τ := finRotate (n+2))).mpr
    (by simp [c.cycleType,sup]))
  exact ⟨e,eq⟩

private def value {n : Nat} (A : Perm (Fin n)) (x : Nat) :=
  if h : x<n then (A ⟨x,h⟩).val else x

private def doubleMate {n : Nat} (A : Perm (Fin n)) (x : Nat) :=
  2*value A (x/2) + (1-x%2)

private theorem below {n : Nat} (A : Perm (Fin n)) {x : Nat} (hx : x<n) :
    value A x<n := by simp [value,hx]

private theorem twice {n : Nat} (A : Perm (Fin n)) (undo : ∀ x, A (A x)=x) (v : Nat) :
    value A (value A v)=v := by
  by_cases h : v<n
  · simp [value,h,(A ⟨v,h⟩).isLt,undo]
  · simp [value,h]

private def doubled {n : Nat} (A : Perm (Fin n)) (undo : ∀ x, A (A x)=x)
    (sphere : eulerDefect (finRotate n) A=0) : Chords (2*n) where
  mate := doubleMate A
  bound := by intro i h; have := below A (x := i/2) (by omega); unfold doubleMate; omega
  undo := by
    intro i hi
    have eff : doubleMate A i/2=value A (i/2) := by unfold doubleMate; omega
    have rem : doubleMate A i%2=1-i%2 := by unfold doubleMate; omega
    unfold doubleMate
    change 2*value A (doubleMate A i/2)+(1-doubleMate A i%2)=i
    rw [eff,rem,twice A undo]
    omega
  distinct := by intro i hi; unfold doubleMate; omega
  noncrossing := by
    intro i j ij jk kl valid
    unfold doubleMate at jk kl valid
    let a := i/2
    let b := j/2
    have hi : a<n := by
      have m := twice A undo b
      by_contra! no
      have hold : value A a=a := by simp [value,show ¬ a<n by omega]
      have hb : b<n := by
        by_contra! no'
        have gone : value A b=b := by simp [value,show ¬ b<n by omega]
        dsimp [a,b] at *
        omega
      dsimp [a,b] at *
      omega
    have hj : b<n := by
      have := below A hi
      dsimp [a,b] at *
      omega
    have ab : a<b := by
      by_contra! no
      have eq : a=b := by dsimp [a,b] at *; omega
      have valEq := congrArg (value A) eq
      dsimp [a,b] at *
      omega
    have bc : b<value A a := by
      have le : b≤value A a := by dsimp [a,b] at *; omega
      by_contra! no
      have eq : b=value A a := by omega
      have reverse : value A b=a := eq ▸ twice A undo a
      dsimp [a,b] at *
      omega
    have cd : value A a<value A b := by
      have ne : value A a≠value A b := fun h =>
        ab.ne ((twice A undo a).symm.trans ((congrArg (value A) h).trans (twice A undo b)))
      dsimp [a,b] at *
      omega
    apply Bouquet.no_crossing A undo sphere ⟨a,hi⟩ ⟨b,hj⟩ ab
    · exact (show b<(A ⟨a,hi⟩).val by simpa [value,hi] using bc)
    · simpa [value,hi,hj] using cd

def mateAt (pairs : List (Nat × Nat)) (x : Nat) : Option Nat := do
  let p ← pairs.find? (fun p => p.1==x || p.2==x)
  return if p.1=x then p.2 else p.1

private theorem mate_correct {n : Nat} (C : Chords n) {pairs : List (Nat × Nat)}
    (rel : ∀ a b, (a,b)∈pairs ↔ a<b ∧ b<n ∧ C.mate b=a) (x : Nat) (hx : x<n) :
    mateAt pairs x=some (C.mate x) := by
  have hb := C.bound _ hx
  have undo := C.undo _ hx
  have ne := C.distinct _ hx
  let p := fun z : Nat × Nat => z.1==x || z.2==x
  cases h : pairs.find? p with
  | none =>
    have absent := List.find?_eq_none.mp h
    by_cases le : x < C.mate x
    · exact False.elim (absent _ ((rel _ _).mpr ⟨le,hb,undo⟩) (by simp [p]))
    · exact False.elim (absent _ ((rel _ _).mpr ⟨by omega,hx,rfl⟩) (by simp [p]))
  | some pair =>
    obtain ⟨a,b⟩ := pair
    have mem := (rel a b).mp (List.mem_of_find?_eq_some h)
    have hit := List.find?_some h
    change (a==x || b==x)=true at hit
    change ((pairs.find? p).bind (fun z => some (if z.1=x then z.2 else z.1)))=_
    rw [h]
    simp only [Bool.or_eq_true,beq_iff_eq] at hit
    rcases hit with rfl|rfl
    · simp [← mem.2.2,C.undo b mem.2.1]
    · simp [mem.1.ne,mem.2.2]

structure Rows where
  length : Nat
  tree : List (Nat × Nat)
  other : List (Nat × Nat)

def decode (bits : List Bool) : Option Rows := do
  let n := bits.length/4
  if bits.length ≠ 4*n then none else
    let t ← decodeChords (bits.take (2*n))
    let c ← decodeChords (bits.drop (2*n))
    return ⟨n,t,c⟩

def bandAt (pairs : List (Nat×Nat)) (x : Nat) : Option Nat := do
  let y ← mateAt pairs (2*x)
  return y/2

def Rows.rotation (R : Rows) (x : Nat) : Option Nat := do
  let y ← bandAt R.tree x
  return (y+1)%R.length

def Rows.pairing (R : Rows) (x : Nat) : Option Nat := do
  let y ← bandAt R.other x
  bandAt R.tree y

private theorem band_code {n : Nat} (A : Perm (Fin n)) (undo : ∀ x, A (A x)=x)
    (sphere : eulerDefect (finRotate n) A=0) :
    ∃ bits pairs, bits.length = 2*n ∧ decodeChords bits=some pairs ∧
      ∀ x : Fin n, bandAt pairs x.val=some (A x).val := by
  let C := doubled A undo sphere
  obtain ⟨l,pairs,ok,rel⟩ := chord_round_trip C
  refine ⟨C.bits,pairs,l,ok,?_⟩
  intro x
  have h := mate_correct C rel (2*x.val) (by have := x.isLt; omega)
  rw [bandAt,h]
  change some (doubleMate A (2*x.val)/2)=_
  simp [doubleMate,value,x.isLt]; omega

/-- The two slots above each original dart are both opening or both closing
for a genuine band, and form an adjacent matched pair at a fixed dart. -/
def pairedBits {n : Nat} (A : Perm (Fin n)) := (List.finRange n).flatMap fun i =>
  [decide (i≤A i),decide (i<A i)]

theorem paired_band {n : Nat} (A : Perm (Fin n)) (undo : ∀ x,A (A x)=x)
    (sphere : eulerDefect (finRotate n) A=0) :
    ∃ pairs, decodeChords (pairedBits A)=some pairs ∧
      ∀ x : Fin n, bandAt pairs x.val=some (A x).val := by
  let C := doubled A undo sphere
  have double (k : Nat) (bound : k≤n) :
      (List.range (2*k)).map C.bit =
      (List.range k).flatMap (fun i => [decide (i≤value A i),decide (i<value A i)]) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have first : C.bit (2*k)=decide (k≤value A k) := by
        simp [C,Chords.bit,doubled,doubleMate]
      have second : C.bit (2*k+1)=decide (k<value A k) := by
        simp [C,Chords.bit,doubled,doubleMate,show (2*k+1)/2=k by omega]; omega
      rw [show 2*(k+1)=2*k+1+1 by omega,List.range_succ,List.range_succ (n:=2*k),
        List.range_succ (n:=k),List.map_append,List.map_append,List.flatMap_append,ih (by omega)]
      simp [first,second,List.append_assoc]
  have er : pairedBits A = C.bits := by
    rw [Chords.bits,double n le_rfl,pairedBits]
    have vr : (List.finRange n).map Fin.val=List.range n := by
      apply List.ext_getElem <;> simp
    rw [←vr,List.flatMap_map]
    congr 1
    funext i; simp [value,i.isLt]
  obtain ⟨_,pairs,ok,rel⟩ := chord_round_trip C
  refine ⟨pairs,er ▸ ok,?_⟩
  intro x
  have h := mate_correct C rel (2*x.val) (by have := x.isLt; omega)
  rw [bandAt,h]
  change some (doubleMate A (2*x.val)/2)=_
  simp [doubleMate,value,x.isLt]; omega

/-- Four bits per dart suffice to reconstruct both permutations of every
connected zero-defect multimap, up to a single common renaming of darts.
The parser obtains the dart count from the length of its input. -/
theorem round_trip {n : Nat} (σ α : Perm (Fin n)) (inv : ∀ x, α (α x)=x)
    (planar : eulerDefect σ α=0) (connected : ∀ a b, compSetoid σ α a b) :
    ∃ bits : List Bool, ∃ R : Rows, ∃ order : Perm (Fin n),
      bits.length=4*n ∧ decode bits=some R ∧ R.length=n ∧
      (∀ x : Fin n, R.rotation x.val=some ((order.permCongr σ) x).val) ∧
      ∀ x : Fin n, R.pairing x.val=some ((order.permCongr α) x).val := by
  obtain ⟨θ,T,C,h,one,pt⟩ := TreeBands.decompose σ α inv planar connected
  obtain ⟨e,num⟩ := cyclic θ one
  have encode (A : Perm (Fin n)) (u : ∀ x, A (A x)=x) (g : eulerDefect θ A=0) :
      ∃ bits pairs, bits.length=2*n ∧ decodeChords bits=some pairs ∧
        ∀ x : Fin n, bandAt pairs x.val=some ((e.permCongr A) x).val := by
    apply band_code
    · intro x; simp [u]
    · rw [← num,eulerDefect_permCongr,g]
  obtain ⟨t,tp,tl,ta,tr⟩ := encode T h.treeUndo pt
  obtain ⟨c,cp,cl,ca,cr⟩ := encode C h.cotreeUndo h.cotreeSphere
  have len : (t++c).length=4*n := by simp [tl,cl]; omega
  refine ⟨t++c,⟨n,tp,cp⟩,e,len,?_,rfl,?_,?_⟩
  · simp [decode,len,← tl,ta,ca]
  · intro x
    rw [Rows.rotation,tr,← h.rotation,permCongr_mul,num,Perm.mul_apply]
    change some (((e.permCongr T x).val+1)%n) = some ((finRotate n (e.permCongr T x)).val)
    cases n with
    | zero => exact Fin.elim0 x
    | succ n =>
      rw [coe_finRotate]
      split
      · next he => rw [he]; simp
      · next ne =>
        simp only [Fin.ext_iff,Fin.val_last] at ne
        have := (e.permCongr T x).isLt
        rw [Nat.mod_eq_of_lt (by omega)]
  · intro x
    rw [Rows.pairing,cr,← h.pairing,permCongr_mul,Perm.mul_apply]
    exact tr _

#print axioms round_trip
end Recognition.RibbonCode
