import SATWire
import RotationVerifier
import VerifierCost

/-! A concrete binary certificate for the NP verification theorem. Graph
bits are little-endian in the existing packed graph order. Each table
coordinate is its unary value followed by a zero, in row-major order. -/
namespace Recognition.RawWire
open SparseBoundary Recognition.RotationVerifier

def putNat (a : Nat) : List Bool := List.replicate a true ++ [false]

def getNat : List Bool → Option (Nat × List Bool)
  | [] => none
  | false::bs => some (0,bs)
  | true::bs => (getNat bs).map (fun (k,rest) => (k+1,rest))

@[simp] theorem get_put (k : Nat) (bs : List Bool) : getNat (putNat k++bs)=some (k,bs) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (getNat (putNat k++bs)).map _=some _
    rw [ih]; rfl

def putPair (p : Fin n × Fin n) := putNat p.1.val ++ putNat p.2.val

def getPair (n : Nat) (bits : List Bool) : Option ((Fin n × Fin n) × List Bool) := do
  let (a,r) ← getNat bits
  let (b,t) ← getNat r
  if h : a<n ∧ b<n then return ((⟨a,h.1⟩,⟨b,h.2⟩),t) else none

@[simp] theorem pair_roundtrip (p : Fin n × Fin n) (bs : List Bool) :
    getPair n (putPair p++bs)=some (p,bs) := by
  simp [getPair,putPair,List.append_assoc,p.1.isLt,p.2.isLt]

def table (n : Nat) : Nat → List Bool → Option (List (Fin n × Fin n) × List Bool)
  | 0,bs => some ([],bs)
  | k+1,bs => do
    let (p,tail) ← getPair n bs
    let (ps,rest) ← table n k tail
    return (p::ps,rest)

@[simp] theorem table_roundtrip (ps : List (Fin n × Fin n)) (bs : List Bool) :
    table n ps.length (ps.flatMap putPair++bs)=some (ps,bs) := by
  induction ps generalizing bs with
  | nil => rfl
  | cons p ps ih => simp [table, List.append_assoc,ih]

private def putBits (b : BitVec w) := List.ofFn (fun i : Fin w => b[i.val])

def getBits (w : Nat) (bs : List Bool) : Option (BitVec w × List Bool) :=
  let head := bs.take w
  if h : head.length=w then some ((BitVec.ofBoolListLE head).cast h,bs.drop w) else none

private theorem put_length (b : BitVec w) : (putBits b).length=w := by simp [putBits]

private theorem restoreBits (b : BitVec w) (h : (putBits b).length=w) :
    (BitVec.ofBoolListLE (putBits b)).cast h=b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  simp [putBits,List.getD_eq_getElem?_getD,hi]

@[simp] theorem bits_roundtrip (b : BitVec w) (bs : List Bool) :
    getBits w (putBits b++bs)=some (b,bs) := by
  have len := put_length b
  have left : (putBits b++bs).take w=putBits b := List.take_left' len
  have right : (putBits b++bs).drop w=bs := List.drop_left' len
  have helper (l : List Bool) (he : l=putBits b) (h : l.length=w) : (BitVec.ofBoolListLE l).cast h=b := he ▸ restoreBits b len
  unfold getBits; dsimp only; rw [dite_eq_left ((congrArg List.length left).trans len),helper _ left,right]

def encode (C : Raw n) : List Bool :=
  putBits C.graph.bits ++ C.next.toList.flatMap putPair ++ C.prev.toList.flatMap putPair

def decode (n : Nat) (bs : List Bool) : Option (Raw n) := do
  let (bits,tail) ← getBits (pairCount n) bs
  let (a,tail) ← table n (n*n) tail
  let (b,rest) ← table n (n*n) tail
  if h : a.length=n*n ∧ b.length=n*n ∧ rest=[] then
    return ⟨⟨bits⟩,⟨a.toArray,by simpa using h.1⟩,⟨b.toArray,by simpa using h.2.1⟩⟩
  else none

theorem roundtrip (C : Raw n) : decode n (encode C)=some C := by
  have first := table_roundtrip C.next.toList (C.prev.toList.flatMap putPair)
  have last := table_roundtrip C.prev.toList []
  simp only [Vector.length_toList,List.append_nil] at first last
  simp only [decode,encode,List.append_assoc,bits_roundtrip,bind,Option.bind_some,first,last]
  have l := C.next.length_toList
  have r := C.prev.length_toList
  simp [l,r]
  obtain ⟨⟨g⟩,⟨a,ha⟩,⟨b,hb⟩⟩ := C
  simp

private theorem word_length (p : Fin n × Fin n) : (putPair p).length≤2*n := by
  have a := p.1.isLt; have b := p.2.isLt
  simp [putPair,putNat]; omega

private theorem table_length (xs : List (Fin n × Fin n)) : (xs.flatMap putPair).length≤xs.length*(2*n) := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    exact (Nat.add_le_add (word_length p) ih).trans_eq (Nat.add_comm ..)

theorem length_bound (C : Raw n) : (encode C).length ≤ 5*(n+1)^3 := by
  have a := table_length C.next.toList
  have b := table_length C.prev.toList
  have g := Certificate.certificate_width n
  simp only [Vector.length_toList] at a b
  simp only [encode,List.length_append,put_length]
  nlinarith [Nat.zero_le (n*n),Nat.zero_le n]

def verify (ds : List Nat) (bits : List Bool) : Bool :=
  if bits.length≤5*(ds.length+1)^3 then
    (decode ds.length bits).any (RotationVerifier.verify ds)
  else false

theorem verify_iff (ds : List Nat) : (∃ bits, verify ds bits=true) ↔ Planaric ds := by
  rw [←RotationVerifier.verify_iff]
  constructor
  · rintro ⟨bs,h⟩; unfold verify at h; split at h
    · cases eq : decode ds.length bs with
      | none => simp [eq] at h
      | some C => exact ⟨C,by simpa [eq] using h⟩
    · contradiction
  · rintro ⟨C,ok⟩; exact ⟨encode C,by simp [verify,length_bound C,roundtrip,ok]⟩

theorem bounded_certificate (ds : List Nat) : Planaric ds ↔
    ∃ bits : List Bool,bits.length≤5*(ds.length+1)^3 ∧ verify ds bits=true := by
  constructor
  · intro h; obtain ⟨C,ok⟩ := (RotationVerifier.verify_iff ds).mpr h
    exact ⟨_,length_bound C,by simp [verify,length_bound C,roundtrip,ok]⟩
  · rintro ⟨bits,_,ok⟩; exact (verify_iff ds).mp ⟨bits,ok⟩

theorem sat_wire (bs : List Bool) : SATBridge.SATLanguage bs ↔
    ∃ ds, Wire.readDegrees (SATBridge.satWire bs)=some ds ∧ ds≠[] ∧
      ∃ cert : List Bool,cert.length≤5*(ds.length+1)^3 ∧ verify ds cert=true := by
  rw [←SATBridge.sat_wire_iff]; simp only [Wire.degreeLanguage,←bounded_certificate]

/-- A consumed unary bit adds one visited-cell operation. -/
def unaryMeter : List Bool → Option (Nat × List Bool) × Nat
  | [] => (none,1)
  | false::bs => (some (0,bs),1)
  | true::bs =>
    let out := unaryMeter bs
    (out.1.map (fun (k,r) => (k+1,r)),out.2+1)

@[simp] theorem unary_value (bs : List Bool) : (unaryMeter bs).1=getNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [unaryMeter,getNat,ih]

theorem unary_visits (bs : List Bool) : (unaryMeter bs).2≤bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [unaryMeter]; omega

theorem get_suffix {bs : List Bool} {v tail} (ok : getNat bs=some (v,tail)) : tail.length≤bs.length := by
  induction bs generalizing v tail with
  | nil => contradiction
  | cons b bs ih =>
    cases b
    · simp [getNat] at ok; obtain ⟨_,rfl⟩ := ok; simp
    · cases h : getNat bs with
      | none => simp [getNat,h] at ok
      | some q =>
        obtain ⟨k,r⟩ := q
        simp [getNat,h] at ok; obtain ⟨_,rfl⟩ := ok
        exact (ih h).trans (by simp)

private theorem pair_suffix {p : Fin n × Fin n} {bs tail : List Bool} (ok : getPair n bs=some (p,tail)) :
    tail.length≤bs.length := by
  unfold getPair at ok
  cases h : getNat bs with
  | none => simp [h] at ok
  | some q =>
    obtain ⟨a,r⟩ := q
    cases k : getNat r with
    | none => simp [h,k] at ok
    | some u =>
      obtain ⟨b,t⟩ := u
      simp only [h,k,bind,Option.bind_some] at ok
      split at ok
      · obtain rfl := congrArg Prod.snd (Option.some.inj ok)
        exact (get_suffix k).trans (get_suffix h)
      · contradiction

/-- The pair decoder scans only the two attempted coordinate words. -/
def pairVisits (bs : List Bool) :=
  let a := unaryMeter bs
  a.2 + (a.1.map (fun x => (unaryMeter x.2).2)).getD 0 + 4

theorem pair_visits (bs : List Bool) : pairVisits bs≤2*(bs.length+1)+4 := by
  have first := unary_visits bs
  unfold pairVisits; simp only [unary_value]
  cases h : getNat bs with
  | none => simp; omega
  | some p =>
    obtain ⟨u,r⟩ := p
    have h₂ := unary_visits r; have dec := get_suffix h
    simp; omega

def tableMeter (n : Nat) : Nat → List Bool → Option (List (Fin n × Fin n) × List Bool) × Nat
  | 0,bs => (some ([],bs),1)
  | k+1,bs =>
    match getPair n bs with
    | none => (none,pairVisits bs+1)
    | some (p,tail) =>
      let out := tableMeter n k tail
      (out.1.map (fun (xs,r) => (p::xs,r)),pairVisits bs+out.2+2)

@[simp] theorem table_value (n k : Nat) (bs : List Bool) : (tableMeter n k bs).1=table n k bs := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih =>
    simp only [tableMeter,table]
    cases h : getPair n bs with
    | none => simp
    | some q =>
      obtain ⟨p,r⟩ := q
      simp only [ih,bind,Option.bind_some]
      cases table n k r <;> rfl

theorem table_visits (n k : Nat) (bs : List Bool) : (tableMeter n k bs).2≤k*(2*(bs.length+1)+6)+1 := by
  induction k generalizing bs with
  | zero => simp [tableMeter]
  | succ k ih =>
    simp only [tableMeter]
    split
    · have p := pair_visits bs
      calc
        _ ≤ 2*(bs.length+1)+4+1 := Nat.add_le_add_right p 1
        _ ≤ _ := by nlinarith [Nat.zero_le (k*(2*(bs.length+1)+6))]
    · rename_i p r old
      have tail := (ih r).trans (Nat.add_le_add_right (Nat.mul_le_mul_left k
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (pair_suffix old) 1)) 6)) 1)
      calc
        _ ≤ (2*(bs.length+1)+4)+(k*(2*(bs.length+1)+6)+1)+2 := Nat.add_le_add_right (Nat.add_le_add (pair_visits bs) tail) 2
        _ = _ := by ring

/-- Upper charge for scanning/packing the graph, both table streams, length
validation and conversion to the two vectors. The square also allows each
unary increment and packed-bit shift a full input-length word traversal. -/
def parseBudget (n len : Nat) :=
  8*(len+1)^2 + 2*((n*n)*(2*(len+1)+6)+1)*(len+1) + 4*(n*n+len+1)

theorem parser_polynomial (n len : Nat) (bound : len≤5*(n+1)^3) :
    parseBudget n len ≤ 1000*(n+2)^8 := by
  unfold parseBudget
  calc
    _ ≤ 8*(5*(n+1)^3+1)^2 + 2*((n*n)*(2*(5*(n+1)^3+1)+6)+1)*(5*(n+1)^3+1) +
      4*(n*n+5*(n+1)^3+1) := by gcongr
    _ ≤ _ := by ring_nf; omega

private theorem table_suffix {bs tail : List Bool} {ps : List (Fin n × Fin n)}
    (ok : table n k bs=some (ps,tail)) : tail.length≤bs.length := by
  induction k generalizing bs ps with
  | zero => obtain rfl := congrArg Prod.snd (Option.some.inj ok); rfl
  | succ k ih =>
    cases h : getPair n bs with
    | none => simp [table,h] at ok
    | some q =>
      obtain ⟨p,r⟩ := q
      cases g : table n k r with
      | none => simp [table,h,g] at ok
      | some q =>
        obtain ⟨ys,t⟩ := q
        simp [table,h,g] at ok
        obtain ⟨_,rfl⟩ := ok
        exact (ih g).trans (pair_suffix h)

private theorem bit_suffix {bs r : List Bool} {b : BitVec w} (ok : getBits w bs=some (b,r)) :
    r.length≤bs.length := by
  unfold getBits at ok; dsimp only at ok; split at ok
  · obtain rfl := congrArg Prod.snd (Option.some.inj ok); simp
  · contradiction

def chargedDecode (n : Nat) (bs : List Bool) : Option (Raw n) × Nat :=
  let base := 8*(bs.length+1)^2+4*(n*n+bs.length+1)
  match getBits (pairCount n) bs with
  | none => (none,base)
  | some (bits,r) =>
    let first := tableMeter n (n*n) r
    let cost := base+first.2*(bs.length+1)
    match first.1 with
    | none => (none,cost)
    | some (a,s) =>
      let second := tableMeter n (n*n) s
      let work := cost+second.2*(bs.length+1)
      match second.1 with
      | none => (none,work)
      | some (b,rest) =>
        (if h : a.length=n*n ∧ b.length=n*n ∧ rest=[] then
          some ⟨⟨bits⟩,⟨a.toArray,by simpa using h.1⟩,⟨b.toArray,by simpa using h.2.1⟩⟩ else none,work)

theorem charged_value (n : Nat) (bs : List Bool) : (chargedDecode n bs).1=decode n bs := by
  simp only [chargedDecode,decode,table_value]
  cases h : getBits (pairCount n) bs with
  | none => rfl
  | some pair =>
    obtain ⟨g,r⟩ := pair
    cases q : table n (n*n) r with
    | none => simp [q]
    | some pair =>
      obtain ⟨xs,s⟩ := pair
      cases v : table n (n*n) s with
      | none => simp [q,v]
      | some pair =>
        obtain ⟨ys,t⟩ := pair
        simp [q,v]

theorem charged_budget (n : Nat) (bs : List Bool) : (chargedDecode n bs).2≤parseBudget n bs.length := by
  let k := n*n
  let base := 8*(bs.length+1)^2 + 4*(n*n+bs.length+1)
  let fee := (k*(2*(bs.length+1)+6)+1)*(bs.length+1)
  have limit (r : List Bool) (small : r.length≤bs.length) :
      (tableMeter n k r).2*(bs.length+1)≤fee := Nat.mul_le_mul_right _
    ((table_visits n k r).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1))
  have eq : parseBudget n bs.length=base+fee+fee := by dsimp [base,fee,k,parseBudget]; ring
  rw [eq]; unfold chargedDecode; dsimp only
  split
  · change base≤_; omega
  · rename_i g r hr
    have sm := bit_suffix hr
    have c₁ := limit r sm
    dsimp only [k] at c₁
    split
    · change base+_≤_; omega
    · rename_i xs s hs
      rw [table_value] at hs
      have c₂ := limit s ((table_suffix hs).trans sm)
      dsimp only [k] at c₂
      split <;> change base+_+_≤_ <;> omega

/-- Joint polynomial charge of the concrete witness parser and the four
rotation-orbit checks on every admitted bit certificate. -/
theorem checking_polynomial (n len darts : Nat) (h : len≤5*(n+1)^3) (m : darts≤n*n) :
    parseBudget n len+VerifierCost.verificationBudget n darts ≤ 21000*(n+2)^8 := by
  have p := parser_polynomial n len h
  have q := VerifierCost.polynomial n darts m
  have ex := Nat.pow_le_pow_right (n:=n+2) (by omega) (by decide : 6≤8)
  omega

#print axioms charged_value
#print axioms charged_budget
#print axioms sat_wire
#print axioms checking_polynomial
end Recognition.RawWire
