import Std

namespace DiskFullerene.SpineWalk

/-- Consecutive directed pairs of an open vertex sequence. -/
def steps {α} : List α → List (α × α)
  | x::y::xs => (x,y)::steps (y::xs)
  | _ => []

theorem pair_after {α} (xs : List α) (a b : α) (ys : List α) : (a,b)∈steps (xs++a::b::ys) := by
  induction xs with
  | nil => simp [steps]
  | cons z zs ih =>
    cases zs with
    | nil => simp [steps]
    | cons w ws => exact List.mem_cons_of_mem _ ih

def Follows {α} (E : α → α → Prop) (xs : List α) := ∀ a b, (a,b)∈steps xs → E a b

def Leaf {α} (E : α → α → Prop) (u : α) := ∃ v, E u v ∧ ∀ w, E u w → w=v

/-- Each permitted edge is the only edge on which its private cut changes
color. The cut also separates the two marked ends. -/
def Separates {α} (E : α→α→Prop) (left right : α) := ∀ a b, E a b → ∃ p : α→Bool,
  p left≠p right ∧ p a≠p b ∧ ∀ u v, E u v → p u≠p v → (u=a ∧ v=b) ∨ (u=b ∧ v=a)

private theorem monochrome {α} (p : α→Bool) {x : α} {xs : List α}
    (same : ∀ a b, (a,b)∈steps (x::xs) → p a=p b) : ∀ y∈x::xs, p y=p x := by
  induction xs generalizing x with
  | nil => simp
  | cons a as ih =>
    intro y m; rcases List.mem_cons.mp m with rfl|m
    · rfl
    · exact (ih (x:=a) (fun u v h=>same u v (by simp [steps,h])) y m).trans
        (same x a (by simp [steps])).symm

theorem step_members {α} {xs : List α} {x y : α} (m : (x,y)∈steps xs) : x∈xs ∧ y∈xs := by
  induction xs with
  | nil => simp [steps] at m
  | cons a as ih =>
    cases as with
    | nil => simp [steps] at m
    | cons b bs =>
      rw [steps,List.mem_cons] at m
      rcases m with eq|m
      · rcases Prod.mk.inj eq with ⟨rfl,rfl⟩; simp
      · exact ⟨List.mem_cons_of_mem _ (ih m).1,List.mem_cons_of_mem _ (ih m).2⟩

private theorem fresh {α} {E : α→α→Prop} {left right x y z : α} {xs : List α}
    (cut : Separates E left right) (simple : (x::y::xs).Nodup) (line : Follows E (x::y::xs))
    (xz : E x z) (ny : z≠y) (noLoop : ∀ v, ¬E v v) : z∉x::y::xs := by
  obtain ⟨p,_,change,only⟩ := cut x z xz
  have away := (List.nodup_cons.mp simple).1
  have xy : E x y := line x y (by simp [steps])
  have first : p x=p y := by
    apply Classical.byContradiction; intro diff
    rcases only x y xy diff with eq|eq
    · exact ny eq.2.symm
    · exact noLoop x (eq.1 ▸ xz)
  have same (a b) (edge : (a,b)∈steps (y::xs)) : p a=p b := by
    have ⟨ha,hb⟩ := step_members edge
    apply Classical.byContradiction; intro opposite
    have mark := only a b (line a b (by simp [steps,edge])) opposite
    rcases mark with eq|eq
    · exact away (eq.1 ▸ ha)
    · exact away (eq.2 ▸ hb)
  intro old
  rcases List.mem_cons.mp old with rfl|mem
  · exact noLoop _ xz
  · exact change (first.trans (monochrome p same z mem).symm)

private theorem grow {α} [DecidableEq α] (all : List α) (complete : ∀ x, x∈all)
    (E : α→α→Prop) (symm : ∀ a b,E a b→E b a) (noLoop : ∀ v,¬E v v)
    (left right : α) (cuts : Separates E left right) (x y : α) (xs : List α)
    (simple : (x::y::xs).Nodup) (line : Follows E (x::y::xs)) :
    ∃ tip ts extra, tip::ts=extra++x::y::xs ∧ Leaf E tip ∧
      (tip::ts).Nodup ∧ Follows E (tip::ts) := by
  classical
  by_cases yes : Leaf E x
  · exact ⟨x,y::xs,[],rfl,yes,simple,line⟩
  have another : ∃ z, E x z ∧ z≠y := by
    apply Classical.byContradiction; intro none
    exact yes ⟨y,line x y (by simp [steps]),fun w ew=>Classical.byContradiction (fun nw=>none ⟨w,ew,nw⟩)⟩
  obtain ⟨z,xz,zy⟩ := another
  have fr := fresh cuts simple line xz zy noLoop
  have nd := List.nodup_cons.mpr ⟨fr,simple⟩
  have foll : Follows E (z::x::y::xs) := by
    intro a b hit
    rcases List.mem_cons.mp hit with eq|hit
    · rcases Prod.mk.inj eq with ⟨rfl,rfl⟩; exact symm _ _ xz
    · exact line a b hit
  obtain ⟨t,ts,pre,e,leaf,nd',foll'⟩ := grow all complete E symm noLoop left right cuts z x (y::xs) nd foll
  exact ⟨t,ts,pre++[z],by simpa [List.append_assoc] using e,leaf,nd',foll'⟩
termination_by all.length-(x::y::xs).length
decreasing_by
  have b := nd.length_le_of_subset (fun {a} _=>complete a)
  simp only [List.length_cons] at b ⊢; omega

structure Path {α} (E : α→α→Prop) (left right : α) where
  middle : List α
  simple : (left::middle++[right]).Nodup
  chain : Follows E (left::middle++[right])
  covers : ∀ a b, E a b → (a,b)∈steps (left::middle++[right]) ∨ (b,a)∈steps (left::middle++[right])

/-- A family of separating edges with only two possible leaves forms a
single simple path. Completeness follows from the change of color between
the two ends for each edge, including any putative unused edge. -/
theorem path {α} [DecidableEq α] (all : List α) (complete : ∀ x, x∈all) (E : α→α→Prop)
    (symm : ∀ a b,E a b→E b a) (noLoop : ∀ v,¬E v v) (left right : α)
    (cuts : Separates E left right) (start : ∃ z,E z right)
    (leaves : ∀ z, Leaf E z → z=left ∨ z=right) : Nonempty (Path E left right) := by
  obtain ⟨z,start⟩ := start
  have zr : z≠right := fun eq=>noLoop right (eq ▸ start)
  have base : Follows E [z,right] := by
    intro a b e
    have eq : (a,b)=(z,right) := by simpa [steps] using e
    rcases Prod.mk.inj eq with ⟨rfl,rfl⟩
    exact start
  obtain ⟨tip,ts,extra,eq,leaf,nd,edges⟩ := grow all complete E symm noLoop left right cuts z right [] (by simp [zr]) base
  obtain ⟨middle,tail⟩ : ∃ s, ts=s++[right] := by
    cases extra with
    | nil => exact ⟨[],(List.cons.inj eq).2⟩
    | cons e es => exact ⟨es++[z],by simpa [List.append_assoc] using (List.cons.inj eq).2⟩
  subst ts
  have notEnd : tip≠right := fun same => (List.nodup_cons.mp nd).1 (by simp [same])
  have tipEq := (leaves tip leaf).resolve_right notEnd
  subst tip
  refine ⟨⟨middle,nd,edges,?_⟩⟩
  intro a b ab
  obtain ⟨p,change,_,only⟩ := cuts a b ab
  apply Classical.byContradiction; intro absent
  have same (u v) (m : (u,v)∈steps (left::middle++[right])) : p u=p v := by
    apply Classical.byContradiction; intro opposite
    rcases only u v (edges u v m) opposite with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact absent (Or.inl m)
    · exact absent (Or.inr m)
  exact change (monochrome p same right (by simp)).symm

end DiskFullerene.SpineWalk
