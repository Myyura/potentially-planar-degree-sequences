import StepCost
import StateIncidence

/-! Construct the dense coloured incidence graph used by a GI call. Arrays
of side/vertex presence are shared by support enumeration and the materialized
colour/arc tables. A field read includes the cost of a possible lazy prune. -/
namespace Recognition.IncidenceMeter
open Recognition.QuotientDP Recognition.StepCost Recognition.StateIncidence

private theorem tabFn (f : Fin m → α × Nat) : (tab f).1=fun i => (f i).1 := funext (tab_val _)
private theorem squareFn (f : Side m → α × Nat) : (square f).1=fun i => (f i).1 := funext (square_val _)

private def readFee (n : Nat) := 4*(n+2)

/-- A projected sealed flag may have to test old liveness at both endpoints.
Opening and block tests use the same conservative allowance. -/
def sidePresent (s : State n) (e : Side n) : Bool × Nat :=
  let r := anyPair fun f => (s.blocks e f || s.blocks f e,2*readFee n+1)
  (s.pending e || s.sealed e || r.1,r.2+2*readFee n+2)

@[simp] theorem sidePresent_val (s : State n) (e : Side n) : (sidePresent s e).1=hasSide s e := by
  apply Bool.eq_iff_iff.mpr; simp [sidePresent,hasSide]

def keys (s : State n) : List (Item n) × Nat :=
  let sides := square (sidePresent s)
  let nodes := tab fun x : Fin n =>
    let u := anyPair fun e => (sides.1 e && (e.1==x || e.2==x),5)
    (s.current x != 0 || u.1,u.2+readFee n+2)
  let raw := ((List.finRange n).filter nodes.1).map Sum.inl ++
    ((((List.finRange n).flatMap (fun x => (List.finRange n).map (x,·))).filter sides.1).map Sum.inr)
  (raw,sides.2+nodes.2+8*(n+n*n+1))

@[simp] theorem keys_val (s : State n) : (keys s).1=names s := by
  have live (x : Fin n) : ((s.current x != 0) ||
      (anyPair fun e : Side n => (hasSide s e && (e.1==x || e.2==x),5)).1)=hasVertex s x := by
    apply Bool.eq_iff_iff.mpr
    simp [hasVertex]
  simp only [keys,tabFn,live,squareFn,sidePresent_val,names]

private def queryBound (n : Nat) := anyPairBound n (2*readFee n+1)+2*readFee n+2

theorem keys_cost (s : State n) : (keys s).2≤squareBound n (queryBound n)+
    (n*(anyPairBound n 5+readFee n+4)+1)+8*(n+n*n+1) := by
  have sp (e : Side n) : (sidePresent s e).2≤queryBound n := by
    have v := anyPair_cost (fun f : Side n => (s.blocks e f || s.blocks f e,2*readFee n+1)) (2*readFee n+1) (fun _ => le_rfl)
    exact Nat.add_le_add_right (Nat.add_le_add_right v _) _
  have edges := square_cost (sidePresent s) _ sp
  have vs := tab_cost (fun x : Fin n =>
    let u := anyPair fun e => ((square (sidePresent s)).1 e && (e.1==x || e.2==x),5)
    (s.current x != 0 || u.1,u.2+readFee n+2)) (anyPairBound n 5+readFee n+2)
    (fun x => Nat.add_le_add_right (Nat.add_le_add_right (anyPair_cost (fun e => ((square (sidePresent s)).1 e && (e.1==x || e.2==x),5)) 5 (fun _ => le_rfl)) _) _)
  change _+_+_≤_
  exact Nat.add_le_add_right (Nat.add_le_add edges vs) _

theorem names_size (s : State n) : (names s).length≤n+n^2 := by
  have lhs := List.length_filter_le (hasVertex s) (List.finRange n)
  let es := (List.finRange n).flatMap (fun x => (List.finRange n).map (x,·))
  have len : es.length=n^2 := by simp [es,List.length_flatMap,pow_two]
  have rhs := (List.length_filter_le (hasSide s) es).trans_eq len
  simpa only [names,List.length_append,List.length_map,List.length_finRange,es] using Nat.add_le_add lhs rhs

def materialize (s : State n) : StateIso.Colored (names s).length × Nat :=
  let ls := keys s
  let a := ls.1.toArray
  let key (i : Fin (names s).length) := a[i.val]'(by simpa [a,ls] using i.isLt)
  let colors := tab fun i => (tint s (key i),readFee n+5)
  let arcs := square fun e => (arc s (key e.1) (key e.2),readFee n+8)
  (⟨colors.1,fun i j => arcs.1 (i,j)⟩,ls.2+ls.1.length+colors.2+arcs.2+1)

@[simp] theorem materialize_eq (s : State n) : (materialize s).1=graph s := by
  simp [materialize,graph,tabFn,squareFn]

theorem materialize_cost (s : State n) : (materialize s).2≤10000*(n+2)^8 := by
  let m := (names s).length
  let ls := keys s
  let a := ls.1.toArray
  let key (i : Fin m) := a[i.val]'(by simpa [a,ls,m] using i.isLt)
  have color := tab_cost (fun i => (tint s (key i),readFee n+5)) _ (fun _ => le_rfl)
  have arcs := square_cost (fun e => (arc s (key e.1) (key e.2),readFee n+8)) _ (fun _ => le_rfl)
  have l := keys_cost s
  have x : ls.1.length=m := congrArg List.length (keys_val _)
  have hmid : (materialize s).2 ≤ squareBound n (queryBound n)+
      (n*(anyPairBound n 5+readFee n+4)+1)+8*(n+n*n+1)+m+
      (m*(readFee n+5+2)+1)+squareBound m (readFee n+8)+1 := by
    unfold materialize; dsimp only
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add l x.le) color) arcs) _
  apply hmid.trans
  have cap : m≤n+n^2 := names_size s
  let Q (m : Nat) := squareBound n (queryBound n)+(n*(anyPairBound n 5+readFee n+4)+1)+8*(n+n*n+1)+m+(m*(readFee n+5+2)+1)+squareBound m (readFee n+8)+1
  change Q m≤_
  apply (show Q m≤Q (n+n^2) by dsimp only [Q,squareBound]; gcongr).trans
  dsimp only [Q,squareBound,queryBound,anyPairBound,readFee]; ring_nf; omega

/-- Scalar comparisons use multiplicity scans on the two residual lists. -/
def scalar (s t : State n) : Bool × Nat :=
  (decide (s.remaining=t.remaining ∧ s.used=t.used ∧ s.faces=t.faces),
   8*(s.remaining.card+t.remaining.card+2)^2)

theorem scalar_cost (s t : State n) (hs : s.remaining.card≤n) (ht : t.remaining.card≤n) :
    (scalar s t).2≤32*(n+2)^2 := by
  have cap : s.remaining.card+t.remaining.card+2 ≤ 2*(n+2) := by omega
  exact (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left cap 2)).trans_eq (by ring)

end Recognition.IncidenceMeter
