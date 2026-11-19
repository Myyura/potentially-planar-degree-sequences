import SparseBoundary.RimGrowth

namespace SparseBoundary.RimGrowth

private structure Seed where
  missing : Nat
  high : List Nat
  base : Nat
  bits : Nat

private def seeds : List Seed := [
  ⟨0,[],1,63⟩, ⟨1,[4],3,31335⟩, ⟨2,[],3,27239⟩, ⟨2,[5],5,242270767⟩,
  ⟨2,[4,4],4,1918511⟩, ⟨3,[4],5,240173615⟩, ⟨3,[6],7,33226270720623⟩,
  ⟨3,[5,4],6,65098760815⟩, ⟨3,[4,4,4],5,240181807⟩]

private def graph (s : Seed) : Graph (s.base+3) := ⟨BitVec.ofNat _ s.bits⟩
private def Valid (s : Seed) : Prop :=
  Ordered (graph s) ∧ (graph s).adj 0 (lastRim s.base)=true ∧
    apexDegree (graph s) + s.missing = s.base+2 ∧
    (rimDegrees (graph s)).Perm (s.high ++ List.replicate (s.base+2-s.high.length) 3) ∧
    s.high.length≤s.base+2 ∧ s.base+2=s.missing + (s.high.foldr max 3)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem valid (s : Seed) (hs : s∈seeds) : Valid s := by
  simp [seeds] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Valid Ordered <;> decide +kernel

private theorem grow (s : Seed) (hs : s∈seeds) (q : Nat) (fits : s.base+2≤q) :
    Planaric ((q-s.missing)::(s.high ++ List.replicate (q-s.high.length) 3)) := by
  obtain ⟨ord,edge,deg,pat,len,_⟩ := valid s hs
  let k := q-(s.base+2)
  have base : q=s.base+2+k := by dsimp [k]; omega
  have p := realize_growing (graph s) ord edge k
  have da : apexDegree (graph s)+k=q-s.missing := by omega
  rw [da] at p
  apply (planaric_perm (List.Perm.cons _ ?_)).mp p
  apply (pat.append_left _).trans
  have perm := List.perm_append_comm (l₁:=List.replicate k 3) (l₂:=s.high ++ List.replicate (s.base+2-s.high.length) 3)
  have eq : List.replicate (s.base+2-s.high.length) 3 ++ List.replicate k 3 =
      List.replicate (q-s.high.length) 3 := List.eq_replicate_iff.mpr ⟨by simp; omega,by simp⟩
  simpa only [List.append_assoc,eq] using perm

private theorem classify (u : List Nat) (s : Nat) (small : s≤3) (sort : u.Pairwise (· ≥ ·))
    (high : ∀ x∈u,4≤x) (sum : u.sum≤3*u.length+s) (even : (u.sum+u.length+s)%2=0) :
    ∃ e∈seeds, e.missing=s ∧ e.high=u := by
  have minsum (v : List Nat) (h : ∀ x∈v,4≤x) : 4*v.length≤v.sum := by
    induction v with
    | nil => simp
    | cons a l ih =>
      have := h a (by simp)
      have := ih (fun x hx => h x (by simp [hx]))
      simp; omega
  have bound := minsum u high
  have len : u.length≤3 := by omega
  have witness :
      (s=0 ∧ u=[]) ∨ (s=1 ∧ u=[4]) ∨ (s=2 ∧ u=[]) ∨ (s=2 ∧ u=[5]) ∨
      (s=2 ∧ u=[4,4]) ∨ (s=3 ∧ u=[4]) ∨ (s=3 ∧ u=[6]) ∨
      (s=3 ∧ u=[5,4]) ∨ (s=3 ∧ u=[4,4,4]) := by
    match u with
    | [] | [_] | [_,_] | [_,_,_] =>
      simp at high sum even sort ⊢ <;> omega
    | _::_::_::_::_ => simp at len
  rcases witness with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    simp [seeds]

/-- The strictly sparse, minimum-three case with a maximum missing at
    most three neighbors. All nine possible excess patterns are realized
    for unbounded order by enlarging an explicitly certified outer edge. -/
theorem near_max_interior (a : Nat) (us : List Nat) (sort : (a::us).Pairwise (· ≥ ·))
    (min : ∀ x∈a::us,3≤x) (cap : a≤us.length) (near : us.length≤a+3)
    (sum : a+us.sum≤4*us.length) (even : (a+us.sum)%2=0) : Planaric (a::us) := by
  let u := us.filter fun x => decide (4≤x)
  let rest := us.filter fun x => !(decide (4≤x))
  let s := us.length-a
  have p : (u++rest).Perm us := List.filter_append_perm _ _
  have high (x) (hx : x∈u) : 4≤x := of_decide_eq_true (List.mem_filter.mp hx).2
  have H : rest = List.replicate rest.length 3 := by
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl,?_⟩
    intro x hx
    have m := min x (List.mem_cons_of_mem _ (List.mem_filter.mp hx).1)
    have e := (List.mem_filter.mp hx).2
    change (!(decide (4≤x)))=true at e
    simp at e
    omega
  have len := p.length_eq
  simp only [List.length_append] at len
  have volume := p.sum_nat
  simp only [List.sum_append] at volume
  have restvol : rest.sum = rest.length*3 := by conv => lhs; rw [H]; simp [List.sum_replicate_nat]
  obtain ⟨e,he,sm,hu⟩ := classify u s (by dsimp [s]; omega) (sort.of_cons.filter _)
    high (by dsimp [s]; omega) (by dsimp [s]; omega)
  have all (x) (hx : x∈u) : x≤a :=
    List.rel_of_pairwise_cons sort (List.mem_filter.mp hx).1
  have foldle (v : List Nat) (cap : ∀ z∈v,z≤a) : v.foldr max 3 ≤ a := by
    induction v with
    | nil => exact min a (by simp)
    | cons b l ih =>
      have bnd := cap b (by simp)
      have tail := ih (fun z hz => cap z (by simp [hz]))
      simp only [List.foldr_cons]; omega
  have hm := foldle u all
  have data := (valid e he).2.2.2.2.2
  rw [sm,hu] at data
  have q := grow e he us.length (by dsimp [s] at data; omega)
  rw [hu,sm,show us.length-s=a by dsimp [s];omega] at q
  apply (planaric_perm (p.cons a)).mp
  have lrest : us.length-u.length=rest.length := by omega
  simpa only [lrest,← H] using q
end SparseBoundary.RimGrowth
