import WireSearch
import ElementaryCost

/-! End-to-end explicit-entry recognition. Each tagged bit is read a
bounded number of times. A graph witness is carried through both the
finite small-order branch and the metered elementary frontier search. -/
namespace Recognition.WireCost
open SparseBoundary LayerCost AlgorithmCost
attribute [local irreducible] ElementaryCost.search ElementaryRun.find

private def graphOf (n a : Nat) : Graph n := ⟨BitVec.ofNat (pairCount n) a⟩
private def tryCode (ds : List Nat) (a : Nat) :=
  (Certificate.checkWith (@Certificate.testPlanar) ds (graphOf ds.length a).bits,2000)

def tiny (ds : List Nat) : Option (Graph ds.length) × Nat :=
  let codes := List.range (2^pairCount ds.length)
  let (a,c) := seek (tryCode ds) codes
  (a.map (graphOf ds.length),c+codes.length+1)

private theorem code_spec (ds : List Nat) (a : Nat) :
    (tryCode ds a).1=true ↔ (graphOf ds.length a).Planar ∧ (graphOf ds.length a).Realizes ds := by
  simp only [tryCode,Certificate.checkWith,Bool.and_eq_true,List.all_eq_true,beq_iff_eq,
    Certificate.testPlanar_iff,List.mem_finRange,forall_true_left]
  exact and_comm

theorem tiny_sound {ds : List Nat} {G : Graph ds.length} (hit : (tiny ds).1=some G) :
    G.Planar ∧ G.Realizes ds := by
  simp only [tiny,seek_val,Option.map_eq_some_iff] at hit
  obtain ⟨a,h,rfl⟩:=hit
  exact (code_spec ds a).mp (List.find?_some (p := fun x => (tryCode ds x).1) h)

theorem tiny_iff (ds : List Nat) : (tiny ds).1.isSome ↔ Planaric ds := by
  constructor
  · intro h; obtain ⟨G,hit⟩:=Option.isSome_iff_exists.mp h
    exact ⟨G,(tiny_sound hit).2,(tiny_sound hit).1⟩
  · rintro ⟨G,deg,planar⟩
    have eq : graphOf ds.length G.bits.toNat=G := by cases G;simp [graphOf]
    simp only [tiny,seek_val,Option.isSome_map,List.isSome_find?,List.any_eq_true]
    exact ⟨G.bits.toNat,List.mem_range.mpr (G.bits.toNat_lt_twoPow_of_le le_rfl),
      (code_spec ..).mpr (by rw [eq];exact ⟨planar,deg⟩)⟩

theorem tiny_bound (ds : List Nat) (small : ds.length<4) : (tiny ds).2≤17000 := by
  have h:= seek_cost (tryCode ds) (List.range (2^pairCount ds.length)) 2000 (fun _ _ => le_rfl)
  have size : pairCount ds.length≤3 := by
    have cases_ : ds.length=0 ∨ ds.length=1 ∨ ds.length=2 ∨ ds.length=3 := by omega
    rcases cases_ with h|h|h|h <;> rw [h] <;> decide
  have cap : 2^pairCount ds.length≤8 := Nat.pow_le_pow_right (by decide) size
  simp only [tiny,List.length_range] at h ⊢
  omega

def construct : (ds : List Nat) → Option (Graph ds.length) × Nat
  | [] => tiny []
  | x::xs =>
    let ds := x::xs
    let n := xs.length+1
    let overhead := 8*(n+1)
    if 6*n<ds.sum then (none,overhead)
    else if n<4 then
      let tinyResult := tiny ds
      (tinyResult.1,overhead+tinyResult.2)
    else
      let found := ElementaryCost.search x xs (2*n-5)
      (found.1,overhead+found.2)

theorem construct_sound {ds : List Nat} {G : Graph ds.length} (hit : (construct ds).1=some G) :
    G.Planar ∧ G.Realizes ds := by
  cases ds with
  | nil => exact tiny_sound hit
  | cons x xs =>
    simp only [construct] at hit
    split at hit
    · contradiction
    · rename_i volume
      split at hit
      · exact tiny_sound hit
      · rename_i order
        have proof := ElementaryCost.large_reference x xs (Nat.le_of_not_lt order) (Nat.le_of_not_lt volume)
        apply ElementaryRun.find_sound (x::xs) G
        rw [←proof]
        simpa only [List.length_cons] using hit

theorem construct_iff (sep : SeparatorInput.WeightedPlanarSeparator) (ds : List Nat) :
    (construct ds).1.isSome ↔ Planaric ds := by
  constructor
  · intro yes;obtain ⟨G,hit⟩:=Option.isSome_iff_exists.mp yes
    exact ⟨G,(construct_sound hit).2,(construct_sound hit).1⟩
  · intro yes
    cases ds with
    | nil => exact (tiny_iff []).mpr yes
    | cons x xs =>
      have bound:=MainResult.volume yes
      change (x::xs).sum≤6*(xs.length+1) at bound
      simp only [construct,ite_eq_right (Nat.not_lt.mpr bound)]
      split
      · exact (tiny_iff _).mpr yes
      · rename_i big
        simpa only [List.length_cons] using (ElementaryCost.search_iff sep x xs (Nat.le_of_not_lt big) bound).mpr yes

theorem construct_cost (ds : List Nat) : Fits ds.length 6000001 (construct ds).2 := by
  let n:=ds.length
  have overhead : Fits n 11 (8*(n+1)) :=
    (show 8*(n+1)≤8*(n+2)^1 by simp).trans (polynomial n 8 1)
  have widen {x a : Nat} (h : Fits n a x) (b : Nat) (le : a≤b) : Fits n b x :=
    h.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le))
  cases ds with
  | nil => exact widen ((tiny_bound [] (by decide)).trans (constant 0 17000)) _ (by decide)
  | cons x xs =>
    simp only [construct];split
    · exact widen overhead _ (by decide)
    · rename_i volume
      split
      · rename_i small
        have t : Fits n 17000 (tiny (x::xs)).2 := (tiny_bound (x::xs) small).trans (constant n 17000)
        exact widen (overhead.plus t) _ (by decide)
      · rename_i large
        have rest := ElementaryCost.search_cost x xs (2*(x::xs).length-5)
          (by simp only [List.length_cons];omega) (Nat.le_of_not_lt volume)
        exact widen (overhead.plus rest) _ (by decide)

def run (bs : List Bool) : Option ((ds : List Nat) × Graph ds.length) × Nat :=
  let (d,read) := WireSearch.decode bs
  match d with
  | some (a::as) =>
    let output := construct (a::as)
    (output.1.map (fun g => ⟨a::as,g⟩),read+output.2+1)
  | _ => (none,read+1)

theorem run_iff (sep : SeparatorInput.WeightedPlanarSeparator) (bs : List Bool) :
    (run bs).1.isSome ↔ Wire.degreeLanguage Planaric bs := by
  rw [←WireSearch.find_iff sep]
  simp only [run,(WireSearch.decode_work bs).1,WireSearch.find]
  cases h : WireSearch.parse bs with
  | none => rfl
  | some ds => cases ds with
    | nil => rfl
    | cons a as => simp [construct_iff sep,ElementaryRun.find_iff sep]

/-- L is the actual bit length. The order parameter counts the vertex
terminators and agrees with n on every well-formed input. -/
theorem run_cost (bs : List Bool) :
    (run bs).2≤6*bs.length+3+2^(6000001*((WireSearch.arity bs).sqrt+1)) := by
  have read := (WireSearch.decode_work bs).2
  simp only [run,(WireSearch.decode_work bs).1]
  cases h : WireSearch.parse bs with
  | none => exact (show (WireSearch.decode bs).2+1≤6*bs.length+3 by omega).trans (Nat.le_add_right ..)
  | some ds =>
    have eq := (WireSearch.parse_exact ..).mp h
    have size := WireSearch.arity_eq bs eq.1
    cases ds with
    | nil => exact (show (WireSearch.decode bs).2+1≤6*bs.length+3 by omega).trans (Nat.le_add_right ..)
    | cons a as =>
      have bound := construct_cost (a::as)
      unfold Fits at bound
      dsimp only;rw [size];omega

end Recognition.WireCost
