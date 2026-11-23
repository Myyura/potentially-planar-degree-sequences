import DiskFullerene.CutSides

namespace DiskFullerene
open Separation

namespace CutFamily
def crosses {V E} (p : V → Bool) (ends : E → V × V) (e : E) : Bool :=
  p (ends e).1 != p (ends e).2

private theorem steady_walk {V E : Type} {ends : E → V × V} {keep : E → Prop} {p : V → Bool}
    (fixed : ∀ e, keep e → p (ends e).1 = p (ends e).2)
    {a b} (walk : Walk (Adj ends keep) a b) : p a = p b := by
  induction walk with
  | refl => rfl
  | step _ hop ih =>
    obtain ⟨e,ok,he⟩ := hop
    have eq := fixed e ok
    rcases he with h|h <;> rw [h] at eq
    · exact ih.trans eq
    · exact ih.trans eq.symm

private theorem cutSize {V : Type} {n : Nat} (seed : Fin n) (ends : Fin n → V × V)
    (robust : ∀ i j x y, Walk (Adj ends (fun d => ¬(d=i ∨ d=j))) x y)
    (p : V → Bool) {a b} (apart : p a ≠ p b) :
    3 ≤ ((List.finRange n).filter (crosses p ends)).length := by
  let xs := (List.finRange n).filter (crosses p ends)
  have three (i j : Fin n) : ∃ d ∈ xs, d≠i ∧ d≠j := by
    apply Classical.byContradiction
    intro no
    apply apart
    apply steady_walk (keep := fun d => ¬(d=i ∨ d=j)) _ (robust i j a b)
    intro d ok
    by_cases eq : p (ends d).1 = p (ends d).2
    · exact eq
    · have hx : d∈xs := List.mem_filter.mpr ⟨List.mem_finRange d, by simpa [crosses] using eq⟩
      exact False.elim (no ⟨d,hx,by grind⟩)
  change 3≤xs.length
  cases hh : xs with
  | nil => have := three seed seed; simp [hh] at this
  | cons x xs' =>
    cases ht : xs' with
    | nil => have := three x x; simp [hh,ht] at this
    | cons y ys =>
      cases hy : ys with
      | nil => have := three x y; simp [hh,ht,hy] at this
      | cons => simp

/-- Membership in the two cuts is a two-bit label. Distinct labels give
six possible types of edge. The four counts on the bottom line measure
the boundary sizes of the four putative intersections. -/
abbrev Q := Bool × Bool
private def edgeCount (es : List (Q × Q)) (a b : Q) :=
  es.countP (fun e => (e.1 == a && e.2 == b) || (e.1 == b && e.2 == a))

private def identities (es : List (Q × Q)) : Prop :=
    let A : Q := (false,false)
    let B : Q := (false,true)
    let C : Q := (true,true)
    let D : Q := (true,false)
    let a := edgeCount es A B
    let b := edgeCount es B C
    let c := edgeCount es C D
    let d := edgeCount es D A
    let e := edgeCount es A C
    let f := edgeCount es B D
    es.countP (crosses Prod.fst id) = b+d+e+f ∧
    es.countP (crosses Prod.snd id) = a+c+e+f ∧
    es.countP (crosses (· == A) id) = a+d+e ∧
    es.countP (crosses (· == B) id) = a+b+f ∧
    es.countP (crosses (· == C) id) = b+c+e ∧
    es.countP (crosses (· == D) id) = c+d+f

private theorem singleton_stats (q : Q × Q) : identities [q] := by
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  cases a <;> cases b <;> cases c <;> cases d <;> unfold identities <;> decide

private theorem count_cons {α} (p : α → Bool) (a : α) (xs : List α) :
    (a::xs).countP p = [a].countP p + xs.countP p := by
  simp only [List.countP_cons,List.countP_nil]; omega

private theorem histogram (es : List (Q × Q)) : identities es := by
  induction es with
  | nil => unfold identities; decide
  | cons q qs ih =>
    have one := singleton_stats q
    dsimp only [identities,edgeCount] at one ih ⊢
    simp only [count_cons (a:=q) (xs:=qs)]
    omega

/-- Two three-edge cuts of a three-edge-connected graph cannot have all
four intersections nonempty. The oddness of the minimum cut is essential. -/
theorem laminar {V : Type} {n : Nat} (seed : Fin n) (ends : Fin n → V × V)
    (robust : ∀ i j x y, Walk (Adj ends (fun d => ¬(d=i ∨ d=j))) x y)
    (p q : V → Bool)
    (cp : ((List.finRange n).filter (crosses p ends)).length = 3)
    (cq : ((List.finRange n).filter (crosses q ends)).length = 3) :
    ∃ pattern : Q, ∀ v, (p v, q v) ≠ pattern := by
  classical
  apply Classical.byContradiction
  intro full
  have hit (c : Q) : ∃ v, (p v,q v) = c := by
    apply Classical.byContradiction; intro no
    exact full ⟨c,fun v eq => no ⟨v,eq⟩⟩
  let color := fun v => (p v,q v)
  let es := (List.finRange n).map fun e => (color (ends e).1,color (ends e).2)
  have stats (f : Q → Bool) : es.countP (crosses f id) =
      ((List.finRange n).filter (crosses (fun v => f (color v)) ends)).length := by
    unfold es
    rw [List.countP_map, ← List.countP_eq_length_filter]
    rfl
  have lower (c : Q) : 3 ≤ es.countP (crosses (· == c) id) := by
    rw [stats]
    obtain ⟨a,ha⟩ := hit c
    obtain ⟨b,hb⟩ := hit (!c.1,c.2)
    apply cutSize seed ends robust _ (a:=a) (b:=b)
    change ((p a,q a) == c) ≠ ((p b,q b) == c)
    rw [ha,hb]; cases c with | mk x y => cases x <;> simp
  obtain ⟨p₁,p₂,q₁,q₂,q₃,q₄⟩ := histogram es
  have f1 : es.countP (crosses Prod.fst id)=3 := (stats _).trans cp
  have f2 : es.countP (crosses Prod.snd id)=3 := (stats _).trans cq
  have := lower (false,false)
  have := lower (false,true)
  have := lower (true,true)
  have := lower (true,false)
  omega

end CutFamily
end DiskFullerene
