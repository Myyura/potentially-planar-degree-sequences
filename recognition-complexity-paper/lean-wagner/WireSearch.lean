import ElementaryRun

/-! Two-pass recognition on the actual tagged-bit degree encoding. Bounded
decoding prevents the construction of huge binary integers on a no-instance.
The counters in the scan model fit words of logarithmic input length. -/
namespace Recognition.WireSearch
open SparseBoundary

/-- Count terminators, skipping the payload after a data tag. -/
def arity : List Bool → Nat
  | [] | [true] => 0
  | false::bs => arity bs+1
  | true::_::bs => arity bs

def countTags : List Bool → Nat × Nat
  | [] | [true] => (0,1)
  | false::bs =>
    let (a,t) := countTags bs
    (a+1,t+2)
  | true::_::bs =>
    let (a,t) := countTags bs
    (a,t+2)

theorem count_tags (bs : List Bool) :
    (countTags bs).1=arity bs ∧ (countTags bs).2≤2*bs.length+1 ∧ arity bs≤bs.length := by
  induction bs using arity.induct <;> simp_all [countTags,arity] <;> omega

private def push (cap : Nat) (bit : Bool) : Option (List Nat) → Option (List Nat)
  | some (a::as) => if 2*a+bit.toNat≤cap then some ((2*a+bit.toNat)::as) else none
  | _ => none

def scan (cap : Nat) : List Bool → Option (List Nat) × Nat
  | [] => (some [],1)
  | [true] => (none,1)
  | false::bs =>
    let (r,t) := scan cap bs
    (r.map (0::·),t+3)
  | true::b::bs =>
    let (r,t) := scan cap bs
    (push cap b r,t+7)

def parse (bs : List Bool) := (scan (arity bs) bs).1

theorem scan_charge (cap : Nat) (bs : List Bool) : (scan cap bs).2≤4*bs.length+1 := by
  induction bs using arity.induct with
  | case1 => simp [scan]
  | case2 => simp [scan]
  | case3 xs ih => simp only [scan,List.length_cons];omega
  | case4 b xs ih => simp only [scan,List.length_cons];omega

def decode (bs : List Bool) :=
  let (n,a) := countTags bs
  let (ds,b) := scan n bs
  (ds,a+b)

theorem decode_work (bs : List Bool) : (decode bs).1=parse bs ∧ (decode bs).2≤6*bs.length+2 := by
  constructor
  · simp only [decode,parse,(count_tags bs).1]
  change (countTags bs).2+(scan (countTags bs).1 bs).2≤_
  rw [(count_tags bs).1]
  have first := (count_tags bs).2.1
  have second := scan_charge (arity bs) bs
  omega

theorem arity_eq (bs : List Bool) (h : Wire.readDegrees bs=some ds) : arity bs=ds.length := by
  induction bs using arity.induct generalizing ds with
  | case1 => simp [Wire.readDegrees] at h;subst ds;rfl
  | case2 => contradiction
  | case3 xs ih =>
    cases eq : Wire.readDegrees xs with
    | none => simp [Wire.readDegrees,eq] at h
    | some ys =>
      simp [Wire.readDegrees,eq] at h;subst ds;simp [arity,ih eq]
  | case4 b xs ih =>
    cases eq : Wire.readDegrees xs with
    | none => simp [Wire.readDegrees,eq] at h
    | some ys =>
      cases ys with
      | nil => simp [Wire.readDegrees,eq] at h
      | cons a as =>
        simp [Wire.readDegrees,eq] at h;subst ds;simp [arity,ih eq]

theorem reads (cap : Nat) (bs : List Bool) (ds : List Nat) :
    (scan cap bs).1=some ds ↔ Wire.readDegrees bs=some ds ∧ ∀ a∈ds,a≤cap := by
  induction bs using arity.induct generalizing ds with
  | case1 => simp [scan,Wire.readDegrees]; aesop
  | case2 => simp [scan,Wire.readDegrees]
  | case3 bs ih =>
    cases ds with
    | nil => simp [scan,Wire.readDegrees]
    | cons a as => simp [scan,Wire.readDegrees,ih]; aesop
  | case4 b bs ih =>
    cases ds with
    | nil =>
      have left : push cap b (scan cap bs).1≠some [] := by
        cases (scan cap bs).1 with
        | none => simp [push]
        | some l => cases l <;> simp [push]
      have right : Wire.readDegrees (true::b::bs)≠some [] := by
        cases e : Wire.readDegrees bs with
        | none => simp [Wire.readDegrees,e]
        | some l => cases l <;> simp [Wire.readDegrees,e]
      simp [scan,left,right]
    | cons a as =>
      constructor
      · intro h
        cases eq : (scan cap bs).1 with
        | none => simp [scan,push,eq] at h
        | some ys =>
          cases ys with
          | nil => simp [scan,push,eq] at h
          | cons z zs =>
            obtain ⟨raw,small⟩ := (ih _).mp eq
            simp only [scan,push,eq] at h
            split at h <;> simp_all [Wire.readDegrees]
      · rintro ⟨raw,all⟩
        cases eq : Wire.readDegrees bs with
        | none => simp [Wire.readDegrees,eq] at raw
        | some ys =>
          cases ys with
          | nil => simp [Wire.readDegrees,eq] at raw
          | cons z zs =>
            simp [Wire.readDegrees,eq] at raw
            obtain ⟨rfl,rfl⟩ := raw
            have capZ := all _ List.mem_cons_self
            have bounded : ∀ y∈z::zs,y≤cap := by
              intro y mem;rcases List.mem_cons.mp mem with rfl|rest
              · omega
              · exact all _ (List.mem_cons_of_mem _ rest)
            simp [scan,(ih _).mpr ⟨eq,bounded⟩,push,capZ]

theorem parse_exact (bs ds) : parse bs=some ds ↔ Wire.readDegrees bs=some ds ∧ ∀x∈ds,x≤ds.length := by
  rw [parse,reads]
  constructor <;> rintro ⟨h,b⟩ <;> exact ⟨h,by simpa [arity_eq bs h] using b⟩

theorem degrees_fit (yes : Planaric ds) : ∀x∈ds,x≤ds.length := by
  obtain ⟨G,h,_⟩ := yes
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
  have deg := h ⟨i,hi⟩
  exact deg ▸ (List.length_filter_le (G.adj ⟨i,hi⟩) (List.finRange ds.length)).trans_eq (by simp)

/-- A successful parse retains the list, so the type of the returned graph
specifies its order even at the external bit-string interface. -/
def find (bs : List Bool) : Option ((ds : List Nat) × Graph ds.length) :=
  match parse bs with
  | some (a::as) => (ElementaryRun.find (a::as)).map (fun g => ⟨a::as,g⟩)
  | _ => none

theorem find_iff (sep : SeparatorInput.WeightedPlanarSeparator) (bs : List Bool) :
    (find bs).isSome ↔ Wire.degreeLanguage Planaric bs := by
  cases hp : parse bs with
  | none =>
    simp only [find,hp,Option.isSome_none,Bool.false_eq_true,false_iff]
    rintro ⟨ds,raw,_,yes⟩
    rw [(parse_exact ..).mpr ⟨raw,degrees_fit yes⟩] at hp
    contradiction
  | some ds =>
    have raw := ((parse_exact ..).mp hp).1
    cases ds with
    | nil => simp [find,hp,Wire.degreeLanguage,raw]
    | cons a as =>
      simp [find,hp,Wire.degreeLanguage,raw,ElementaryRun.find_iff sep]

theorem find_sound {bs ds} {G : Graph ds.length} (hit : find bs=some ⟨ds,G⟩) :
    Wire.readDegrees bs=some ds ∧ ds≠[] ∧ G.Planar ∧ G.Realizes ds := by
  cases eq : parse bs with
  | none => simp [find,eq] at hit
  | some xs =>
    cases xs with
    | nil => simp [find,eq] at hit
    | cons a as =>
      cases h : ElementaryRun.find (a::as) with
      | none => simp [find,eq,h] at hit
      | some H =>
        simp only [find,eq,h,Option.map_some,Option.some.injEq] at hit
        cases hit
        exact ⟨((parse_exact ..).mp eq).1,by simp,ElementaryRun.find_sound _ _ h⟩

/-- Sorted endpoints give one explicit pair for every edge of the output. -/
def edges (G : Graph n) : List (Fin n × Fin n) :=
  ((List.finRange n).product (List.finRange n)).filter fun (i,j) => decide (i<j) && G.adj i j

theorem edges_spec (G : Graph n) (i j : Fin n) :
    (i,j)∈edges G ↔ i<j ∧ G.adj i j=true := by simp [edges]

theorem edges_nodup (G : Graph n) : (edges G).Nodup :=
  List.filter_sublist.nodup ((List.nodup_finRange n).product (List.nodup_finRange n))

end Recognition.WireSearch
