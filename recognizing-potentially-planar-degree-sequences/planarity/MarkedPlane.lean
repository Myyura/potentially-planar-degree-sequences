import RibbonCode
import Wire
import Frontier
import OrbitTable
import Augmentation

/-! A single bit string for a vertex-coloured simple plane graph, its
retained edges and once-per-vertex counters. A maximal plane completion
connects all components while using only linearly many additional darts. -/
namespace Recognition.MarkedPlane
open LeanPool.K5MinorFreeChoosability Equiv Equiv.Perm PlanarDegrees.Frontier

structure View where
  ribbon : RibbonCode.Rows
  retained : List Bool
  roles : List Nat
  values : List Nat

/-- The outer delimiter specifies the number of darts in unary. Both
parenthesis streams together have four bits per dart. -/
private def splitSize : List Bool → Option (Nat × List Bool)
  | [] => none
  | false::xs => some (0,xs)
  | true::xs => (splitSize xs).map fun (n,rest) => (n+1,rest)

private theorem split_ok (n : Nat) (xs : List Bool) :
    splitSize (List.replicate n true ++ false::xs)=some (n,xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,splitSize,ih]

def decode (bits : List Bool) : Option View := do
  let (n,s) ← splitSize bits
  let R ← RibbonCode.decode (s.take (4*n))
  let t := s.drop (4*n)
  let us ← Wire.readDegrees (t.drop n)
  if t.length < n ∨ us.length ≠ 2*n then none
  else return ⟨R,t.take n,us.take n,us.drop n⟩

def pack (n : Nat) (b keep : List Bool) (roles vals : List Nat) :=
  List.replicate n true ++ false::(b++(keep++Wire.degrees (roles++vals)))

theorem unpack {R : RibbonCode.Rows} {n : Nat} {b keep : List Bool} {roles vals : List Nat}
    (bh : b.length=4*n) (rd : RibbonCode.decode b=some R) (kh : keep.length=n)
    (rh : roles.length=n) (vh : vals.length=n) :
    decode (pack n b keep roles vals)=some ⟨R,keep,roles,vals⟩ := by
  simp only [decode,pack,split_ok,bind,pure,Option.bind_some,
    List.take_left' bh,List.drop_left' bh,rd,List.take_left' kh,List.drop_left' kh,
    Wire.degrees_round_trip,List.take_left' rh,List.drop_left' rh,List.length_append,kh,rh,vh]
  simp [Nat.two_mul]

private theorem bin_width (a : Nat) (k : Nat) (h : a<2^k) :
    (Wire.bin a).length ≤ 2*k+1 := by
  induction k generalizing a with
  | zero =>
    have z : a=0 := by simpa using h
    subst a; simp [Wire.bin]
  | succ k ih =>
    rw [Wire.bin]
    split
    · simp
    · rw [pow_succ] at h
      have smaller := ih (a/2) (by omega)
      simp only [List.length_cons]
      omega

private theorem value_width (v : Nat) : (Wire.bin v).length ≤ 2*cost v+1 :=
  bin_width v _ (by have := (cost_brackets v).2; omega)

private theorem code_size (xs : List Nat) :
    (Wire.degrees xs).length = (xs.map (fun a => (Wire.bin a).length)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [Wire.degrees,List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons] at *; rw [ih]

def View.turn (V : View) {n : Nat} (i : Fin n) : Fin n :=
  let z := (V.ribbon.rotation i.val).getD i.val
  if h : z<n then ⟨z,h⟩ else i

/-- Compute equality of vertex cycles by merging the dart classes. -/
def View.vertexKey (V : View) {n : Nat} (i : Fin n) :=
  let xs := List.finRange n
  OrbitTable.key (OrbitTable.run xs (xs.map (fun x => (x,V.turn x)))) i

def View.counter (V : View) {n : Nat} (i : Fin n) :=
  ∑ j : Fin n, if V.vertexKey j=V.vertexKey i then V.values[j.val]?.getD 0 else 0

private theorem key_correct {C : View} {n : Nat} (r : Perm (Fin n))
    (read : ∀ i : Fin n, C.ribbon.rotation i.val=some (r i).val) (i j : Fin n) :
    C.vertexKey i=C.vertexKey j ↔ SameCycle r i j := by
  have step (x : Fin n) : C.turn x=r x := by simp [View.turn,read,(r x).isLt]
  unfold View.vertexKey
  simp only [step]
  apply OrbitTable.generated _ List.mem_finRange _ (SameCycle.setoid r)
  · rintro e he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    exact sameCycle_apply_right.mpr (SameCycle.refl _ _)
  · intro s h
    exact fun _ _ => sameCycle_of_step s (fun a => h (a,r a) (List.mem_map.mpr ⟨a,List.mem_finRange _,rfl⟩))

/-- The numerical fields on one representative dart per vertex use at
most the sum of their variable-length widths, plus one zero per other dart. -/
private theorem value_sum {V : Type} [Fintype V] [DecidableEq V] {n : Nat}
    (tail : Fin n → V) (rep : V → Fin n) (section_ : Function.LeftInverse tail rep)
    (val : V → Nat) :
    let field := fun d => if d=rep (tail d) then val (tail d) else 0
    (∑ d : Fin n,(Wire.bin (field d)).length) ≤ n+2*∑ v, cost (val v) := by
  classical
  let reps := Finset.univ.image rep
  have member (d : Fin n) : d∈reps ↔ d=rep (tail d) := by
    constructor
    · intro h; obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp h; rw [section_]
    · intro h; exact Finset.mem_image.mpr ⟨tail d,Finset.mem_univ _,h.symm⟩
  dsimp only
  calc
    _ ≤ ∑ d : Fin n,(1 + if d∈reps then 2*cost (val (tail d)) else 0) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases h : d=rep (tail d)
      · rw [ite_eq_left h,ite_eq_left ((member _).mpr h)]; have := value_width (val (tail d)); omega
      · simp [h,mt (member _).mp h,Wire.bin]
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_ite_mem]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,Finset.univ_inter]
      congr 1
      rw [show reps=Finset.univ.image rep by rfl,Finset.sum_image (fun a _ b _ h => section_.injective h)]
      simp only [section_ _]; rw [Finset.mul_sum]


/-- Test adjacency between the two decoded vertex classes, retaining only
the darts whose original edge survived planar completion. -/
def View.edgeBetween (C : View) {n : Nat} (a b : Fin n) :=
  (List.finRange n).any fun d =>
    C.retained[d.val]?.getD false && C.vertexKey d == C.vertexKey a &&
      (C.ribbon.pairing d.val).any (fun i => if h : i<n then C.vertexKey (⟨i,h⟩ : Fin n) == C.vertexKey b else false)

theorem graph_code {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (planar : IsPlanar G) (size : 4≤Nat.card V) (role : V → Fin 4) (val : V → Nat) :
    ∃ n : Nat, ∃ bits : List Bool, ∃ C : View, ∃ tail : Fin n → V,
      Function.Surjective tail ∧ decode bits=some C ∧ C.ribbon.length=n ∧
      n+12=6*Nat.card V ∧ bits.length ≤ 20*n+2*∑ v, cost (val v) + 1 ∧
      (∀ a b, C.vertexKey a=C.vertexKey b ↔ tail a=tail b) ∧
      (∀ a, C.roles[a.val]?=some (role (tail a)).val ∧ C.counter a=val (tail a)) ∧
      ∀ a b, C.edgeBetween a b ↔ G.Adj (tail a) (tail b) := by
  classical
  let _ : Nonempty V := (Nat.card_pos_iff.mp (by omega : 0<Nat.card V)).1
  obtain ⟨H,sub,maximal⟩ := Augment.exists_maximal G planar
  obtain ⟨M⟩ := maximal.1
  have conn := Augment.maximal_connected maximal
  obtain ⟨minDeg,edges⟩ := Augment.maximal_tight M maximal conn size
  let n := Fintype.card H.Dart
  let e := Fintype.equivFin H.Dart
  let r := e.permCongr M.rot
  let p := e.permCongr (dartSymm H)
  have joint : ∀ i j : Fin n, compSetoid r p i j := by
    have subOne := numComponents_le_one_of_connected M.isRotationSystem conn
    have one : Subsingleton (Quotient (compSetoid M.rot (dartSymm H))) :=
      Finite.card_le_one_iff_subsingleton.mp subOne
    intro i j
    have related : compSetoid M.rot (dartSymm H) (e.symm i) (e.symm j) :=
      Quotient.exact (one.elim ⟦e.symm i⟧ ⟦e.symm j⟧)
    simpa [r,p] using (compSetoid_permCongr_iff e M.rot (dartSymm H) _ _).mp related
  obtain ⟨b,R,o,len,parsed,Rn,rot,pair⟩ := RibbonCode.round_trip r p
    (by intro x; simp [p,permCongr_apply,dartSymm]) (by simpa [r,p,eulerDefect_permCongr] using M.eulerDefect_eq_zero) joint
  let z := e.trans o
  let tail (i : Fin n) := (z.symm i).fst
  have onto : Function.Surjective tail := by
    intro v
    obtain ⟨u⟩ := (Nat.card_pos_iff.mp (by have := minDeg v; omega : 0<Nat.card {u // H.Adj v u})).1
    exact ⟨z ⟨(v,u.val),u.property⟩,by simp [tail]⟩
  let rep := Function.surjInv onto
  have sect : Function.LeftInverse tail rep := Function.rightInverse_surjInv onto
  let keep := List.ofFn fun i : Fin n => decide (G.Adj (tail i) (z.symm i).snd)
  let roles := List.ofFn fun i : Fin n => (role (tail i)).val
  let value (i : Fin n) := if i=rep (tail i) then val (tail i) else 0
  let vals := List.ofFn value
  let C : View := ⟨R,keep,roles,vals⟩
  let bits := pack n b keep roles vals
  have rotation (i : Fin n) : C.ribbon.rotation i.val=some ((z.permCongr M.rot) i).val := rot i
  have pairing (i : Fin n) : C.ribbon.pairing i.val = some (z (z.symm i).symm).val := pair i
  have keys (i j : Fin n) : C.vertexKey i=C.vertexKey j ↔ tail i=tail j := by
    rw [key_correct _ rotation]
    have same := sameCycle_permCongr_iff z M.rot (z.symm i) (z.symm j)
    simp only [apply_symm_apply] at same
    rw [←same]
    exact ⟨r_eq_of_sameCycle (r := id) M.isRotationSystem.fst_apply, M.isRotationSystem.sameCycle _ _⟩
  have cnt (i : Fin n) : C.counter i=val (tail i) := by
    unfold View.counter
    have get (j : Fin n) : C.values[j.val]?.getD 0=value j := by simp [C,vals]
    simp only [get,keys]
    rw [Finset.sum_eq_single (rep (tail i))]
    · simp [value,sect _]
    · intro j _ ne
      by_cases eq : tail j=tail i
      · simp [value,eq,ne]
      · simp [eq]
    · simp
  refine ⟨n,bits,C,tail,onto,unpack len parsed (by simp [keep]) (by simp [roles]) (by simp [vals]),Rn,?_,?_,keys,?_,?_⟩
  · have darts := card_dart_eq_two_mul H
    rw [←card_edgeSet_eq_cycleCount] at darts
    have dn : n=Nat.card H.Dart := Nat.card_eq_fintype_card.symm
    omega
  · have bytes := value_sum tail rep sect val
    have fieldLen : (Wire.degrees vals).length ≤ n+2*∑ v, cost (val v) := by
      simpa only [code_size,vals,List.map_ofFn,List.sum_ofFn,Function.comp_apply,value] using bytes
    have roleLen : (Wire.degrees roles).length ≤ 5*n := by
      rw [code_size,List.map_ofFn,List.sum_ofFn]
      calc
        _ ≤ ∑ _ : Fin n, 5 := Finset.sum_le_sum (fun i _ => bin_width _ 2 (role (tail i)).isLt)
        _ = _ := by simp [Nat.mul_comm]
    have append (a b : List Nat) : Wire.degrees (a++b)=Wire.degrees a++Wire.degrees b := List.flatMap_append ..
    simp only [bits,pack,List.length_append,List.length_replicate,List.length_cons,len,List.length_ofFn,
      keep,append]
    omega
  · intro i; exact ⟨by simp [C,roles],cnt i⟩
  · intro a b
    have test (d : Fin n) :
        C.retained[d.val]?.getD false = decide (G.Adj (tail d) (z.symm d).snd) := by
      simp [C,keep]
    simp only [View.edgeBetween,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true,
      test,decide_eq_true_eq,beq_iff_eq,keys,pairing,Option.any_some]
    constructor
    · rintro ⟨d,⟨good,hd⟩,he⟩
      have tip : tail (z (z.symm d).symm)=(z.symm d).snd := by simp [tail]
      rw [dite_eq_left (z (z.symm d).symm).isLt,beq_iff_eq,keys] at he
      rwa [←hd,←he,tip]
    · intro good
      let d : H.Dart := ⟨(tail a,tail b),sub good⟩
      refine ⟨z d,⟨?_,?_⟩,?_⟩
      · simpa [d,tail] using good
      · simp [tail,d]
      · rw [dite_eq_left (z (z.symm (z d)).symm).isLt,beq_iff_eq,keys]
        simp [tail,d]

end Recognition.MarkedPlane

namespace Recognition.MarkedPlane
open PlanarDegrees.MapCode

private theorem split_shape {xs : List Bool} {n : Nat} {rest : List Bool}
    (read : splitSize xs=some (n,rest)) : n+1+rest.length=xs.length := by
  induction xs generalizing n rest with
  | nil => contradiction
  | cons b bs ih =>
    cases b with
    | false => simp only [splitSize,Option.some.injEq,Prod.mk.injEq] at read; obtain ⟨rfl,rfl⟩ := read; simp [Nat.add_comm]
    | true =>
      cases val : splitSize bs with
      | none => simp [splitSize,val] at read
      | some pair =>
        obtain ⟨k,tail⟩ := pair
        simp [splitSize,val] at read
        obtain ⟨rfl,rfl⟩ := read
        have := ih val
        simp; omega

private theorem ribbon_shape {xs : List Bool} {R : RibbonCode.Rows} (read : RibbonCode.decode xs=some R) :
    4*R.length=xs.length ∧ R.tree.length=R.length ∧ R.other.length=R.length := by
  classical
  unfold RibbonCode.decode at read
  dsimp only at read
  split at read
  · contradiction
  next h =>
    simp only [not_not] at h
    cases t : decodeChords (xs.take (2*(xs.length/4))) with
    | none => simp [t] at read
    | some p =>
      cases q : decodeChords (xs.drop (2*(xs.length/4))) with
      | none => simp [t,q] at read
      | some g =>
        simp [t,q] at read
        subst R
        have a := decoded_length t
        have b := decoded_length q
        simp only [List.length_take,List.length_drop] at a b
        dsimp
        omega

private theorem fields_width (xs : List Bool) {us : List Nat} (read : Wire.readDegrees xs=some us) :
    us.length≤xs.length ∧ ∀ i∈us, i<2^xs.length := by
  induction xs using Wire.readDegrees.induct generalizing us with
  | case1 => simp [Wire.readDegrees] at read; simp [read]
  | case2 xs ih =>
    cases h : Wire.readDegrees xs with
    | none => simp [Wire.readDegrees,h] at read
    | some vs =>
      simp [Wire.readDegrees,h] at read
      obtain rfl := read
      obtain ⟨len,vals⟩ := ih h
      simp only [List.length_cons,List.mem_cons,Nat.pow_succ]
      exact ⟨by omega,fun i hi => hi.elim (by rintro rfl; positivity) (fun m => by have := vals i m; omega)⟩
  | case3 => contradiction
  | case4 b xs ih =>
    cases h : Wire.readDegrees xs with
    | none => simp [Wire.readDegrees,h] at read
    | some vs =>
      cases vs with
      | nil => simp [Wire.readDegrees,h] at read
      | cons v vs =>
        simp [Wire.readDegrees,h] at read
        obtain rfl := read
        obtain ⟨len,vals⟩ := ih h
        have high := vals v (by simp)
        simp only [List.length_cons,List.mem_cons,Nat.pow_succ] at *
        refine ⟨by omega,fun i hi => ?_⟩
        rcases hi with rfl|m
        · cases b <;> simp <;> omega
        · have := vals i (Or.inr m); omega

/-- Even a syntactically accepted malformed proposal has linear-size
dart and mark tables, and each decoded numeric entry has at most as many
bits as the proposed record. No semantic validity hypothesis is needed. -/
theorem decode_bounds {bits : List Bool} {C : View} (ok : decode bits=some C) :
    6*C.ribbon.length+1 ≤ bits.length ∧ C.retained.length=C.ribbon.length ∧
    C.roles.length=C.ribbon.length ∧ C.values.length=C.ribbon.length ∧
    C.ribbon.tree.length=C.ribbon.length ∧ C.ribbon.other.length=C.ribbon.length ∧
    ∀ i∈C.roles++C.values, i<2^bits.length := by
  unfold decode at ok
  cases hdr : splitSize bits with
  | none => simp [hdr] at ok
  | some pair =>
    obtain ⟨n,s⟩ := pair
    have shape := split_shape hdr
    cases r : RibbonCode.decode (s.take (4*n)) with
    | none => simp [hdr,r] at ok
    | some R =>
      cases l : Wire.readDegrees ((s.drop (4*n)).drop n) with
      | none => simp only [hdr,r,l,bind,Option.bind_some,Option.bind_none,reduceCtorEq] at ok
      | some us =>
        have eq := ribbon_shape r
        have bounds := fields_width _ l
        simp only [hdr,r,l,bind,Option.bind_some,pure] at ok
        split at ok
        · contradiction
        next guard =>
          obtain rfl := Option.some.inj ok
          simp only [List.length_take,List.length_drop,List.take_append_drop] at *
          have sz : n=R.length := by omega
          refine ⟨by omega,by omega,by omega,by omega,eq.2.1,eq.2.2,?_⟩
          intro i m
          have b := bounds.2 i (by simpa using m)
          exact b.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

#print axioms decode_bounds
end Recognition.MarkedPlane
