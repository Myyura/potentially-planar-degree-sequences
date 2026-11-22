import DiamondExample

namespace Recognition.DiamondExample
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

abbrev D := Fin 10
abbrev Orient := Bool × Bool

def ends : D → V × V := ![(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(3,0),(3,1)]
def number : V → V → D := ![![0,0,1,2],![3,0,4,5],![6,7,0,0],![8,9,0,0]]

def dart : D ≃ diamond.Dart where
  toFun i := ⟨ends i, (show ∀ i : D, diamond.Adj (ends i).1 (ends i).2 by decide) i⟩
  invFun d := number d.fst d.snd
  left_inv := (show ∀ i : D, number (ends i).1 (ends i).2 = i by decide)
  right_inv := by
    rintro ⟨⟨i,j⟩,h⟩
    apply SimpleGraph.Dart.ext
    exact (show ∀ i j : V, diamond.Adj i j → ends (number i j) = (i,j) by decide) i j h

def forward : D → D := ![1,2,0,4,5,3,7,6,9,8]
def backward : D → D := ![2,0,1,5,3,4,7,6,9,8]

def next (o : Orient) (i : D) : D :=
  if (if i.val < 3 then o.1 else o.2) then forward i else backward i

def rot (o : Orient) : Perm D where
  toFun := next o
  invFun := next (!o.1,!o.2)
  left_inv := (show ∀ o : Orient, ∀ i : D, next (!o.1,!o.2) (next o i) = i by decide) o
  right_inv := (show ∀ o : Orient, ∀ i : D, next o (next (!o.1,!o.2) i) = i by decide) o

private theorem powers {A B : Type*} (f : A → B) (p : Perm A) (q : Perm B)
    (comm : ∀ x, f (p x) = q (f x)) (n : Nat) (x : A) :
    f ((p ^ n) x) = (q ^ n) (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',pow_succ',Perm.mul_apply,Perm.mul_apply,comm,ih]

private theorem orbit_of_pow {A : Type*} (p : Perm A) {i j : A} {n : Nat} (h : (p^n) i = j) :
    p.SameCycle i j := ⟨(n : ℤ),by simpa only [zpow_natCast] using h⟩

private def lifted (o : Orient) : Perm diamond.Dart := dart.permCongr (rot o)

private theorem lifted_step (o : Orient) (i : D) : dart (rot o i) = lifted o (dart i) := by
  simp [lifted,Equiv.permCongr_apply]

def rotation (o : Orient) : ArithmeticRotation.Rotation diamond := by
  refine ⟨lifted o,⟨?_,?_⟩⟩
  · intro d
    obtain ⟨i,rfl⟩ := dart.surjective d
    rw [←lifted_step]
    exact (show ∀ u : Orient, ∀ x : D, (ends (next u x)).1 = (ends x).1 by decide) o i
  · intro d e
    obtain ⟨i,rfl⟩ := dart.surjective d
    obtain ⟨j,rfl⟩ := dart.surjective e
    intro same
    have check : ∀ u : Orient, ∀ x y : D, (ends x).1 = (ends y).1 →
        ∃ k : Fin 3, (rot u ^ k.val) x = y := by decide +kernel
    obtain ⟨k,hk⟩ := check o i j same
    apply orbit_of_pow (lifted o) (n:=k.val)
    rw [←powers dart _ _ (lifted_step o),hk]

private def choices (a : Flags) (x : D) : D :=
  if h : x.val < 6 then if a ⟨x.val,h⟩ then forward x else backward x else forward x

/-- Each three-dart fibre has two cyclic orders. The two-dart fibres
have one. The finite check ranges only over six binary choices. -/
private theorem classify (s : Perm D) (tail : ∀ x, (ends (s x)).1 = (ends x).1)
    (moved : ∀ x, s x ≠ x) : ∃ o : Orient, s = rot o := by
  let a (k : Fin 6) := decide (s ⟨k.val, by omega⟩ = forward ⟨k.val,by omega⟩)
  have alternatives : ∀ x y : D, (ends y).1 = (ends x).1 → y ≠ x →
      (y = forward x ∨ y = backward x) ∧ (6 ≤ x.val → y = forward x) := by decide
  have expand (x : D) : s x = choices a x := by
    obtain ⟨either,large⟩ := alternatives x (s x) (tail x) (moved x)
    by_cases h : x.val < 6
    · simpa [choices,h,a] using (show s x = if s x = forward x then forward x else backward x by
        split <;> grind)
    · simpa [choices,h] using large (by omega)
  have test : ∀ c : Flags, (∀ x y : D, choices c x = choices c y → x = y) →
      ∃ o : Orient, ∀ x : D, choices c x = rot o x := by decide +kernel
  obtain ⟨o,ho⟩ := test a (fun x y h => s.injective (by simpa only [expand] using h))
  exact ⟨o,Equiv.ext fun x => (expand x).trans (ho x)⟩

private theorem all_rotations (r : ArithmeticRotation.Rotation diamond) : ∃ o, rotation o = r := by
  let s : Perm D := dart.symm.permCongr r.val
  have sc (x : D) : dart (s x) = r.val (dart x) := by simp [s,Equiv.permCongr_apply]
  obtain ⟨o,ho⟩ := classify s (fun x => by
    change (dart (s x)).fst = (dart x).fst
    rw [sc,r.property.fst_apply]) (fun x fixed => by
    have diff : ∀ x : D, ∃ y : D, (ends x).1 = (ends y).1 ∧ x ≠ y := by decide
    obtain ⟨y,hy,ne⟩ := diff x
    exact ne (dart.injective ((r.property.sameCycle (dart x) (dart y) hy).eq_of_left
      (by change r.val (dart x) = dart x; rw [←sc,fixed]))))
  refine ⟨o,Subtype.ext (Equiv.ext fun d => ?_)⟩
  obtain ⟨i,rfl⟩ := dart.surjective d
  change lifted o (dart i) = r.val (dart i)
  rw [←lifted_step,←ho,sc]

private theorem rotation_inj : Function.Injective rotation := by
  intro o p eq
  have point (u : D) : next o u = next p u := by
    apply dart.injective
    exact (lifted_step o u).trans ((congrArg (fun r : ArithmeticRotation.Rotation diamond =>
        r.val (dart u)) eq).trans (lifted_step p u).symm)
  exact (show ∀ a b : Orient, next a 0 = next b 0 → next a 3 = next b 3 → a = b by decide)
    o p (point 0) (point 3)

noncomputable def rotations : Orient ≃ ArithmeticRotation.Rotation diamond :=
  Equiv.ofBijective rotation ⟨rotation_inj,all_rotations⟩

def reverseDart : D → D := ![3,6,8,0,7,9,1,4,2,5]

def flip : Perm D :=
  Function.Involutive.toPerm _ (show Function.Involutive reverseDart from
    (show ∀ x : D, reverseDart (reverseDart x) = x by decide))

abbrev faces : Orient → Nat
  | (false,false) | (true,true) => 1
  | (false,true) | (true,false) => 3

def faceLabel : (o : Orient) → D → Fin (faces o)
  | (false,false) | (true,true) => fun _ => 0
  | (false,true) => ![0,1,2,2,0,1,0,1,1,2]
  | (true,false) => ![0,1,2,1,2,0,2,1,0,2]

theorem face_count (o : Orient) : ArithmeticRotation.exponent diamond (rotation o) = faces o := by
  let p := rot o * flip
  let q := (rotation o).val * dartSymm diamond
  have comm (x : D) : dart (p x) = q (dart x) := by
    have rev (i : D) : dart (flip i) = (dart i).symm := by
      apply SimpleGraph.Dart.ext
      exact (show ∀ x : D, ends (reverseDart x) = ((ends x).2,(ends x).1) by decide) i
    change dart (rot o (flip x)) = lifted o ((dart x).symm)
    rw [lifted_step,rev]
  let tag (x : diamond.Dart) := faceLabel o (dart.symm x)
  have sync (x : D) : tag (dart x) = faceLabel o x := by simp [tag]
  have step (x : diamond.Dart) : tag x = tag (q x) := by
    obtain ⟨i,rfl⟩ := dart.surjective x
    rw [←comm,sync,sync]
    exact (show ∀ u : Orient, ∀ x : D,
        faceLabel u x = faceLabel u ((rot u * flip) x) by decide) o i
  have orbits (x y : diamond.Dart) : q.SameCycle x y ↔ tag x = tag y := by
    constructor
    · exact sameCycle_of_step (Setoid.ker tag) step
    · obtain ⟨i,rfl⟩ := dart.surjective x
      obtain ⟨j,rfl⟩ := dart.surjective y
      rw [sync,sync]
      intro h
      have table : ∀ u : Orient, ∀ i j : D, faceLabel u i = faceLabel u j →
          ∃ k : Fin 10, ((rot u * flip)^k.val) i = j := by decide +kernel
      obtain ⟨k,hk⟩ := table o i j h
      apply orbit_of_pow q (n:=k.val)
      rw [←powers dart p q comm]
      exact congrArg dart hk
  have onto : Function.Surjective tag := by
    intro y
    obtain ⟨i,hi⟩ := (show ∀ u : Orient, ∀ y : Fin (faces u), ∃ i : D, faceLabel u i = y by decide) o y
    exact ⟨dart i,(sync i).trans hi⟩
  have rel : SameCycle.setoid q = Setoid.ker tag := Setoid.ext orbits
  change Nat.card (Quotient (SameCycle.setoid q)) = _
  rw [rel,Nat.card_congr (Setoid.quotientKerEquivOfSurjective tag onto),Nat.card_fin]

end Recognition.DiamondExample
