import StateIso
import Mathlib.Data.Nat.Pairing

/-! Recover a concrete colour-preserving isomorphism with polynomially many
calls to a decision procedure, by individualising vertices in input order. -/
namespace Recognition.IsoWitness
open Recognition.StateIso

def paint (A : Colored n) (xs : List (Fin n)) : Colored n where
  color x := Nat.pair (A.color x) (xs.idxOf x)
  edge := A.edge

def Fits (A : Colored n) (B : Colored m) (xs : List (Fin n)) (ys : List (Fin m)) : Prop :=
  ∃ f : Fin n ≃ Fin m, xs.map f=ys ∧ (∀ i,A.color i=B.color (f i)) ∧
    ∀ i j,A.edge i j=B.edge (f i) (f j)

private theorem index_map (p : Fin n ≃ Fin m) (xs : List (Fin n)) (i : Fin n) :
    (xs.map p).idxOf (p i)=xs.idxOf i := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases eq : x=i <;> simp [eq,ih]

theorem paint_iff (A : Colored n) (B : Colored m) {xs : List (Fin n)} {ys : List (Fin m)}
    (len : xs.length=ys.length) (nd : xs.Nodup) :
    Iso (paint A xs) (paint B ys) ↔ Fits A B xs ys := by
  constructor
  · rintro ⟨f,labels,edges⟩
    have data (i) := Nat.pair_eq_pair.mp (labels i)
    refine ⟨f,?_,fun i => (data i).1,edges⟩
    apply List.ext_getElem
    · simpa using len
    · intro j hj hy
      have hx : j<xs.length := by simpa using hj
      let a := xs[j]
      have z : ys.idxOf (f a)=j := (data a).2.symm.trans (nd.idxOf_getElem j hx)
      have inY : f a∈ys := List.idxOf_lt_length_iff.mp (z ▸ hy)
      simp only [List.getElem_map]
      have found := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr inY)
      simpa [z] using found.symm
  · rintro ⟨f,rfl,labels,edges⟩
    exact ⟨f,fun i => by simp [paint,labels,index_map],edges⟩

/-- The comparison primitive returns a truth value on two graphs of the
same fixed sizes. The output list gives the images of the source vertices. -/
def extend (oracle : Colored n → Colored m → Bool) (A : Colored n) (B : Colored m) :
    List (Fin n) → List (Fin n) → List (Fin m) → Option (List (Fin m)) × Nat
  | [],_,ys => (some ys,0)
  | x::rest,xs,ys =>
    let candidates := List.finRange m
    let pass (y) := oracle (paint A (x::xs)) (paint B (y::ys))
    match candidates.find? pass with
    | none => (none,m)
    | some y =>
      let (out,c) := extend oracle A B rest (x::xs) (y::ys)
      (out,((candidates.idxOf y)+1)+c)

theorem extend_cost (oracle : Colored n → Colored m → Bool) (A : Colored n) (B : Colored m)
    (rest xs : List (Fin n)) (ys : List (Fin m)) : (extend oracle A B rest xs ys).2≤rest.length*m := by
  induction rest generalizing xs ys with
  | nil => simp [extend]
  | cons x rest ih =>
    rw [extend]
    split
    · simp [Nat.succ_mul]
    · next y yes =>
      have h := List.idxOf_lt_length_iff.mpr (List.mem_finRange y)
      have recCost := ih (x::xs) (y::ys)
      simp only [List.length_finRange] at h
      simp only [List.length_cons,Nat.succ_mul]
      omega

private theorem continue_iff (oracle : Colored n → Colored m → Bool) (A : Colored n) (B : Colored m)
    (ok : ∀ G H,oracle G H=true ↔ Iso G H) (x : Fin n) (xs : List (Fin n)) (ys : List (Fin m))
    (len : xs.length=ys.length) (nd : (x::xs).Nodup) :
    ((List.finRange m).find? (fun y => oracle (paint A (x::xs)) (paint B (y::ys)))).isSome ↔ Fits A B xs ys := by
  rw [List.isSome_find?,List.any_eq_true]
  constructor
  · rintro ⟨y,_,yes⟩
    obtain ⟨f,maps,col,edge⟩ := (paint_iff A B (xs := x::xs) (ys := y::ys) (congrArg Nat.succ len) nd).mp ((ok ..).mp yes)
    exact ⟨f,(List.cons.inj maps).2,col,edge⟩
  · rintro ⟨f,maps,col,edge⟩
    refine ⟨f x,List.mem_finRange _,(ok ..).mpr ((paint_iff A B (xs := x::xs) (ys := f x::ys) (congrArg Nat.succ len) nd).mpr ?_)⟩
    exact ⟨f,by simp [maps],col,edge⟩

private theorem extend_spec (oracle : Colored n → Colored m → Bool) (A : Colored n) (B : Colored m)
    (ok : ∀ G H,oracle G H=true ↔ Iso G H) (rest xs : List (Fin n)) (ys : List (Fin m))
    (len : xs.length=ys.length) (unique : (rest.reverse++xs).Nodup)
    (fits : Fits A B xs ys) :
    ∃ out,(extend oracle A B rest xs ys).1=some out ∧ Fits A B (rest.reverse++xs) out := by
  induction rest generalizing xs ys with
  | nil => exact ⟨ys,rfl,by simpa using fits⟩
  | cons x rest ih =>
    have nd : (rest.reverse++x::xs).Nodup := by simpa using unique
    have next := (List.nodup_append.mp nd).2.1
    have someY := (continue_iff oracle A B ok x xs ys len next).mpr fits
    obtain ⟨y,hit⟩ := Option.isSome_iff_exists.mp someY
    have step := (paint_iff A B (xs := x::xs) (ys := y::ys) (congrArg Nat.succ len) next).mp ((ok ..).mp (List.find?_some (p := fun y => oracle (paint A (x::xs)) (paint B (y::ys))) hit))
    obtain ⟨out,found,exactly⟩ := ih (x::xs) (y::ys) (congrArg Nat.succ len) nd step
    refine ⟨out,?_,by simpa using exactly⟩
    simpa only [extend,hit] using found

/-- One global test also covers the empty source. An accepted run returns
the images, in reverse input order, of one actual isomorphism. -/
def recover (oracle : Colored n → Colored m → Bool) (A : Colored n) (B : Colored m) :=
  if oracle A B then
    let (out,c) := extend oracle A B (List.finRange n) [] []
    (out,c+1)
  else (none,1)

theorem recover_correct (oracle : Colored n → Colored m → Bool) (A : Colored n) (B : Colored m)
    (ok : ∀ G H,oracle G H=true ↔ Iso G H) :
    ((recover oracle A B).1.isSome ↔ Iso A B) ∧
    (∀ out,(recover oracle A B).1=some out → Fits A B (List.finRange n).reverse out) ∧
    (recover oracle A B).2≤n*m+1 := by
  by_cases yes : oracle A B=true
  · obtain ⟨f,col,ed⟩ := (ok A B).mp yes
    have base : Fits A B [] [] := ⟨f,rfl,col,ed⟩
    obtain ⟨ys,find,hs⟩ := extend_spec oracle A B ok (List.finRange n) [] [] rfl (by simpa using (List.nodup_finRange n)) base
    have cost := extend_cost oracle A B (List.finRange n) [] []
    simp only [recover,yes,ite_true,find,Option.isSome_some,Option.some.injEq,true_iff]
    refine ⟨⟨f,col,ed⟩,fun out eq => ?_,?_⟩
    · subst out; simpa using hs
    · simpa using Nat.add_le_add_right cost 1
  · have no : ¬Iso A B := mt (ok A B).mpr yes
    simp [recover,yes,no]

end Recognition.IsoWitness
