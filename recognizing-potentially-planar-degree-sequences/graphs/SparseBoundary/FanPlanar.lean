import SparseBoundary.GraphEncoding

namespace SparseBoundary.Fan

open Graph

/-- Every edge between nonapices joins consecutive vertices of a fixed path.
The two apices occupy labels 0 and 1. -/
def TwoApexPath (G : Graph n) : Prop :=
  ∀ u v : Fin n, 2≤u.val → 2≤v.val → G.adj u v=true →
    u.val≤v.val+1 ∧ v.val≤u.val+1

private structure Interval where
  lo : Nat
  hi : Nat
  ordered : lo≤hi

private def Represents (s : List (Fin n)) (I : Interval) : Prop :=
  I.hi < n ∧ ∀ v : Fin n, v∈s ↔ I.lo≤v.val ∧ v.val≤I.hi

private theorem interval_of_clean {G : Graph n} (hp : TwoApexPath G)
    (s : List (Fin n)) (clean : ∀ v ∈ s, 2≤v.val)
    (connected : G.connected s = true) : ∃ I, Represents s I := by
  match s with
  | [] => simp [Graph.connected] at connected
  | [v] =>
    refine ⟨⟨v.val,v.val,Nat.le_refl _⟩,v.isLt,?_⟩
    intro w
    simp only [List.mem_singleton]
    constructor
    · rintro rfl; omega
    · intro h; apply Fin.ext; omega
  | x::y::s =>
    change ((y::s).any (G.adj x) && G.connected (y::s))=true at connected
    obtain ⟨hedge,hconn⟩ := Bool.and_eq_true_iff.mp connected
    obtain ⟨w,hw,he⟩ := List.any_eq_true.mp hedge
    have oldclean : ∀ v ∈ y::s, 2≤v.val := fun v hv => clean v (.tail _ hv)
    obtain ⟨I,hn,hr⟩ := interval_of_clean hp (y::s) oldclean hconn
    have hwI := (hr w).mp hw
    have hdist := hp x w (clean x (by simp)) (oldclean _ hw) he
    have hord := I.ordered
    refine ⟨⟨min x.val I.lo,max x.val I.hi,by omega⟩,by change max x.val I.hi < n; have := x.isLt; omega,?_⟩
    intro v; rw [List.mem_cons,hr]
    change (_ ∨ _) ↔ min x.val I.lo ≤ v.val ∧ v.val ≤ max x.val I.hi
    constructor
    · rintro (rfl|q) <;> omega
    · intro q
      by_cases h : v.val=x.val
      · exact .inl (Fin.ext h)
      · exact .inr (by omega)

private def Apart (I J : Interval) : Prop := I.hi < J.lo ∨ J.hi < I.lo
private def Touch (I J : Interval) : Prop := I.hi+1=J.lo ∨ J.hi+1=I.lo

private theorem apart {s t : List (Fin n)} {I J : Interval}
    (hi : Represents s I) (hj : Represents t J)
    (hd : disjoint s t=true) : Apart I J := by
  obtain ⟨hs,hr⟩ := hi
  obtain ⟨ht,hq⟩ := hj
  have oi := I.ordered
  have oj := J.ordered
  by_cases h : I.hi < J.lo
  · exact .inl h
  by_cases g : J.hi < I.lo
  · exact .inr g
  let v : Fin n := ⟨max I.lo J.lo,by omega⟩
  have h1 : v∈s := (hr v).mpr (by dsimp [v]; omega)
  have h2 : v∈t := (hq v).mpr (by dsimp [v]; omega)
  have hd' := List.all_eq_true.mp hd v h1
  simp [h2] at hd'

private theorem touch {s t : List (Fin n)} {I J : Interval} {G : Graph n}
    (hp : TwoApexPath G) (cs : ∀ v ∈ s, 2≤v.val) (ct : ∀ v ∈ t, 2≤v.val)
    (hi : Represents s I) (hj : Represents t J)
    (hd : Apart I J) (hl : G.links s t=true) : Touch I J := by
  obtain ⟨v,hv,he⟩ := List.any_eq_true.mp hl
  obtain ⟨w,hw,hew⟩ := List.any_eq_true.mp he
  have := hp v w (cs _ hv) (ct _ hw) hew
  have := (hi.2 v).mp hv
  have := (hj.2 w).mp hw
  unfold Apart at hd; unfold Touch; omega

private def Tri (k : Nat) (r : Fin k → Fin k → Bool) (good : Fin k → Bool) : Prop :=
  ∃ i j l : Fin k, good i=true ∧ good j=true ∧ good l=true ∧
    i≠j ∧ i≠l ∧ j≠l ∧ r i j=true ∧ r j l=true ∧ r i l=true

private def Four (k : Nat) (r : Fin k → Fin k → Bool) (good : Fin k → Bool) : Prop :=
  ∃ i j l m : Fin k, good i=true ∧ good j=true ∧ good l=true ∧ good m=true ∧
    i≠j ∧ i≠l ∧ i≠m ∧ j≠l ∧ j≠m ∧ l≠m ∧ r i j=true ∧ r i l=true ∧
    ((r m j=true ∧ r m l=true) ∨ r i m=true)

private abbrev cleanExcept {k} (x y i : Fin k) := i != x && i != y

private theorem clique_triangle (x y : Fin 5) : Tri 5 clique5 (cleanExcept x y) := by
  revert x y
  unfold Tri
  decide

private theorem biclique_four (x y : Fin 6) : Four 6 biclique33 (cleanExcept x y) := by
  revert x y
  unfold Four
  set_option maxRecDepth 10000 in
  decide

private theorem obstruction {k} (r : Fin k → Fin k → Bool)
    (has : ∀ x y, Tri k r (cleanExcept x y) ∨ Four k r (cleanExcept x y))
    (defaultIdx : Fin k) {G : Graph n} (hp : TwoApexPath G)
    (bags : Fin k → List (Fin n)) (hm : minorTest G r bags=true) : False := by
  have hpairs (i : Fin k) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp hm i (List.mem_finRange i))
  have pair (i j : Fin k) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp (hpairs i).2 j (List.mem_finRange j))
  have hdis {i j : Fin k} (hne : i ≠ j) : disjoint (bags i) (bags j)=true := by
    have hh := (pair i j).1; simpa [hne] using hh
  have hedge {i j : Fin k} (he : r i j=true) : G.links (bags i) (bags j)=true := by
    have hh := (pair i j).2; simpa [he] using hh
  have sparse (z : Nat) : ∃ owner : Fin k, ∀ i, i≠owner →
      ∀ v ∈ bags i, v.val≠z := by
    classical
    by_cases h : ∃ i, ∃ v ∈ bags i, v.val=z
    · obtain ⟨j,w,hw,hwz⟩ := h
      refine ⟨j,?_⟩
      intro i hij v hv vh
      have eq : v=w := Fin.ext (by omega)
      subst v
      have no := List.all_eq_true.mp (hdis hij) w hv
      simp [hw] at no
    · exact ⟨defaultIdx,fun i _ v hv hz => h ⟨i,v,hv,hz⟩⟩
  obtain ⟨x,hx⟩ := sparse 0
  obtain ⟨y,hy⟩ := sparse 1
  let good := cleanExcept x y
  have clean (i : Fin k) (h : good i=true) (v : Fin n) (hv : v∈bags i) : 2≤v.val := by
    obtain ⟨h1,h2⟩ : i≠x ∧ i≠y := by simpa [good,cleanExcept] using h
    have := hx i h1 v hv; have := hy i h2 v hv; omega
  classical
  let I (i : Fin k) := if h : good i=true then
      Classical.choose (interval_of_clean hp (bags i) (clean i h) (hpairs i).1)
    else ⟨0,0,Nat.le_refl _⟩
  have spec (i) (h : good i=true) : Represents (bags i) (I i) := by
    dsimp [I]; simp only [dite_eq_left h]
    exact Classical.choose_spec (interval_of_clean hp (bags i) (clean i h) (hpairs i).1)
  have ap {i j} (a : good i=true) (b : good j=true) (hj : i≠j) : Apart (I i) (I j) :=
    apart (spec i a) (spec j b) (hdis hj)
  have adj {i j} (a : good i=true) (b : good j=true) (hj : i≠j) (he : r i j=true) :
      Touch (I i) (I j) :=
    touch hp (clean i a) (clean j b) (spec i a) (spec j b) (ap a b hj) (hedge he)
  rcases has x y with ⟨i,j,l,gi,gj,gl,ij,il,jl,e1,e2,e3⟩ |
      ⟨i,j,l,m,gi,gj,gl,gm,ij,il,im,jl,jm,lm,e1,e2,he⟩
  · have := adj gi gj ij e1
    have := adj gj gl jl e2
    have := adj gi gl il e3
    have := (I i).ordered; have := (I j).ordered; have := (I l).ordered
    unfold Touch at *; omega
  · have := ap gj gl jl
    have := ap gi gm im
    have := ap gj gm jm
    have := ap gl gm lm
    have := adj gi gj ij e1
    have := adj gi gl il e2
    have := (I i).ordered; have := (I j).ordered
    have := (I l).ordered; have := (I m).ordered
    rcases he with ⟨e3,e4⟩|e3
    · have := adj gm gj (Ne.symm jm) e3
      have := adj gm gl (Ne.symm lm) e4
      unfold Touch Apart at *; omega
    · have := adj gi gm im e3
      unfold Touch Apart at *; omega

/-- Actual forbidden-minor planarity of every spanning subgraph of a
double fan with these labels, for all orders. -/
theorem two_apex_path_planar {G : Graph n} (h : TwoApexPath G) : G.Planar := by
  constructor
  · rintro ⟨bags,hm⟩
    exact obstruction clique5 (fun x y => .inl (clique_triangle x y)) 0 h bags hm
  · rintro ⟨bags,hm⟩
    exact obstruction biclique33 (fun x y => .inr (biclique_four x y)) 0 h bags hm

end SparseBoundary.Fan
