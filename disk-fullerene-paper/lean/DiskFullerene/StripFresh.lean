import DiskFullerene.CircuitCut
import DiskFullerene.FacialIso

namespace DiskFullerene.StripFresh
open Dual Separation

private theorem inv {n} (i : Fin (n+1)) : cyclicNext (cyclicPrev i)=i := by
  apply Fin.ext; dsimp [cyclicNext,cyclicPrev]; split <;> split <;> omega

private theorem prev_ne {n} (enough : 1≤n) (i : Fin (n+1)) : cyclicPrev i≠i := by
  intro e; have k := congrArg Fin.val e; dsimp [cyclicPrev] at k; split at k <;> omega

private theorem neighbours {C : List α} (nd : C.Nodup) (len : 3≤C.length)
    {p q v x : α} (pv : OnCycle C v p) (qv : OnCycle C v q) (xv : OnCycle C v x) (pq : p≠q) :
    x=p ∨ x=q := by
  have vC : v∈C := pv.elim (fun m=>(endsOfWordSide m).1) (fun m=>(endsOfWordSide m).2)
  obtain ⟨_,_,_,_,_,_,_,possible⟩ := cycle_at nd len vC
  have := possible _ pv; have := possible _ qv; have := possible _ xv
  grind

private theorem noLoop {C : List α} (nd : C.Nodup) (len : 3≤C.length) (x : α) : ¬OnCycle C x x := by
  rintro (xx|xx) <;> obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp xx <;>
    rw [sides_size] at hk <;> rw [side_at C k hk] at eq <;>
    have e := index_eq nd hk (next_bound hk) ((Prod.mk.inj eq).1.trans (Prod.mk.inj eq).2.symm) <;>
    change k=next C.length k at e <;> unfold next at e <;> split at e <;> omega

/-- A closed trail in a simple cycle is the entire cycle, once. Only
undirected edge nonrepetition is assumed; vertex nonrepetition and
exhaustion are conclusions. -/
theorem closed_trail {α : Type} [DecidableEq α] {C : List α} (nd : C.Nodup)
    (len : 3≤C.length) {n} (enough : 1≤n) (f : Fin (n+1) → α)
    (step : ∀ i, OnCycle C (f i) (f (cyclicNext i)))
    (rare : ∀ i j, ((f i=f j ∧ f (cyclicNext i)=f (cyclicNext j)) ∨
      (f i=f (cyclicNext j) ∧ f (cyclicNext i)=f j)) → i=j) :
    Function.Injective f ∧ (∀ x, x∈C ↔ ∃ i, f i=x) ∧ n+1=C.length := by
  have back (i) : OnCycle C (f i) (f (cyclicPrev i)) := by simpa [inv] using (step (cyclicPrev i)).symm
  have two (i) : f (cyclicPrev i)≠f (cyclicNext i) := by
    intro same
    exact prev_ne enough i (rare _ _ (.inr ⟨same,by rw [inv]⟩))
  have member (i) : f i∈C := (step i).elim (fun e=>(endsOfWordSide e).1) (fun e=>(endsOfWordSide e).2)
  have inj : Function.Injective f := by
    intro i j same
    have atI : OnCycle C (f i) (f (cyclicNext j)) := same ▸ step j
    rcases neighbours nd len (back i) (step i) atI (two i) with prev|nxt
    · have e : j=cyclicPrev i := rare _ _ (.inr ⟨by simpa [inv] using same.symm,prev⟩)
      have loop := back i
      rw [←e,←same] at loop
      exact False.elim (noLoop nd len _ loop)
    · exact rare _ _ (.inl ⟨same,nxt.symm⟩)
  have cover {x} (hx : x∈C) : ∃ i, f i=x := by
    have walk := traverseWord C id (OnCycle C) (fun _ _ e=>e.symm)
      (fun _ _ e=>Walk.step .refl (.inl e)) (member 0) hx
    change Walk (OnCycle C) (f 0) x at walk
    have reached {x} (p : Walk (OnCycle C) (f 0) x) : ∃ i,f i=x := by
      induction p with
      | refl => exact ⟨0,rfl⟩
      | step _ ed ih =>
        obtain ⟨i,rfl⟩ := ih
        rcases neighbours nd len (back i) (step i) ed (two i) with l|r
        · exact ⟨_,l.symm⟩
        · exact ⟨_,r.symm⟩
    exact reached walk
  have both (x) : x∈C ↔ ∃ i,f i=x := ⟨cover,fun ⟨i,e⟩=>e ▸ member i⟩
  have p : ((List.finRange _).map f).Perm C := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).map f (fun _ _ ne ee => ne (inj ee))) nd).mpr
    intro t; simp [both]
  exact ⟨inj,both,by simpa using p.length_eq⟩

end DiskFullerene.StripFresh

namespace DiskFullerene.StripFresh
open Dual EndLabels Separation

/-- Each edge of the outer link is used by at most one nonapical triangle.
The other incident triangle contains the apex. -/
theorem unique_rim_triangle {M} (G : IsDiskFullerene M h) (hh : 3≤h) {a b : Face M}
    (ab : OnCycle (dualRow G (apex M)) a b) {s t : Fin M.ord} (so : apex M∉triangle s) (toff : apex M∉triangle t)
    (as' : a∈triangle s) (bs : b∈triangle s) (at' : a∈triangle t) (bt : b∈triangle t) : s=t := by
  have ne : a≠b := fun eq=>noLoop (boundary_cycle G hh).1 (by rw [(boundary_cycle G hh).2.1];omega) a (eq ▸ ab)
  have outside {p q} (link : (p,q)∈sides (dualRow G (apex M))) :
      ∃ (e : Edge M) (v : Fin M.ord), Across (dual G) e p q ∧
        (v=(primal G e).1 ∨ v=(primal G e).2) ∧ apex M∈triangle v := by
    obtain ⟨e,v,c,ends,inA,_⟩ := cornerEdge G link
    exact ⟨e,v,c,ends,(mem_triangle v _).2 inA⟩
  have first : ∃ (e : Edge M) (v : Fin M.ord), Across (dual G) e a b ∧
      (v=(primal G e).1 ∨ v=(primal G e).2) ∧ apex M∈triangle v := by
    rcases ab with p|q
    · exact outside p
    · obtain ⟨e,v,hit,z,o⟩ := outside q; exact ⟨e,v,hit.symm,z,o⟩
  obtain ⟨e,v,edge,ends,pole⟩ := first
  obtain ⟨c,pc,sc⟩ := common_edge_at G hh ne as' bs
  obtain ⟨d,pd,td⟩ := common_edge_at G hh ne at' bt
  obtain rfl := uniqueAcross G hh pc edge; obtain rfl := uniqueAcross G hh pd pc
  have vs : v≠s := fun eq=>so (eq ▸ pole)
  have vt : v≠t := fun eq=>toff (eq ▸ pole)
  grind

/-- Closed lists of boundary sides from distinct actual nonapical triangles
give every outer vertex exactly once and have exactly h entries. -/
theorem actual_perimeter {M} (G : IsDiskFullerene M h) (hh : 3≤h) {n} (enough : 1≤n)
    (f : Fin (n+1) → Face M) (t : Fin (n+1) → Fin M.ord) (distinct : Function.Injective t)
    (steps : ∀ i, OnCycle (dualRow G (apex M)) (f i) (f (cyclicNext i)))
    (used : ∀ i, apex M∉triangle (t i) ∧ f i∈triangle (t i) ∧ f (cyclicNext i)∈triangle (t i)) :
    Function.Injective f ∧ (∀ v, IsBoundary G v ↔ ∃ i, f i=v) ∧ n+1=h := by
  have unique (i j) (eq : (f i=f j ∧ f (cyclicNext i)=f (cyclicNext j)) ∨
      (f i=f (cyclicNext j) ∧ f (cyclicNext i)=f j)) : i=j := by
    obtain ⟨a1,b1,c1⟩ := used i; obtain ⟨a2,b2,c2⟩ := used j
    apply distinct
    apply unique_rim_triangle G hh (steps i) a1 a2 b1 c1
    · rcases eq with ⟨r,_⟩|⟨r,_⟩ <;> rw [r] <;> assumption
    · rcases eq with ⟨_,r⟩|⟨_,r⟩ <;> rw [r] <;> assumption
  obtain ⟨nd,bc,_⟩ := boundary_cycle G hh
  obtain ⟨injection,onto,sz⟩ := closed_trail nd (by omega) enough f steps unique
  exact ⟨injection,onto,sz.trans bc⟩

end DiskFullerene.StripFresh

namespace DiskFullerene.StripFresh
open Dual EndLabels Separation

variable {M : MapData} (G : IsDiskFullerene M h)

/-- One boundary edge and the actual nonapical primal triangle using it. -/
structure RimEdge (x y : Face M) where
  label : Fin M.ord
  cyclic : OnCycle (dualRow G (apex M)) x y
  nonapex : apex M∉triangle label
  first : x∈triangle label
  last : y∈triangle label

def RimEdge.rev {G : IsDiskFullerene M h} {x y} (e : RimEdge G x y) : RimEdge G y x :=
  ⟨e.label,e.cyclic.symm,e.nonapex,e.last,e.first⟩

inductive RimWalk : Face M → Face M → Type
  | nil (x) : RimWalk x x
  | cons {x y z} (edge : RimEdge G x y) (tail : RimWalk y z) : RimWalk x z

namespace RimWalk
variable {G}

def single {a b} (edge : RimEdge G a b) : RimWalk G a b := .cons edge (.nil b)
def starts {a b} : RimWalk G a b → List (Face M)
  | .nil _ => []
  | .cons (x:=x) _ t => x::starts t
def labels {a b} : RimWalk G a b → List (Fin M.ord)
  | .nil _ => []
  | .cons edge t => edge.label::labels t
def vertices {a b} (p : RimWalk G a b) := p.starts++[b]

theorem length_eq {a b} (p : RimWalk G a b) : p.labels.length=p.starts.length := by
  induction p with | nil => rfl | cons _ _ ih => simp [labels,starts,ih]

theorem head_of_pos {a b} (p : RimWalk G a b) (pos : 0<p.starts.length) :
    p.starts[0]=a := by cases p with | nil => contradiction | cons => rfl

def follow {a b c} (p : RimWalk G a b) (q : RimWalk G b c) : RimWalk G a c :=
  match p with | .nil _ => q | .cons e t => .cons e (follow t q)

@[simp] theorem starts_follow {a b c} (p : RimWalk G a b) (q : RimWalk G b c) :
    (p.follow q).starts=p.starts++q.starts := by
  induction p with | nil => rfl | cons _ t ih => simp [follow,starts,ih]

@[simp] theorem labels_follow {a b c} (p : RimWalk G a b) (q : RimWalk G b c) :
    (p.follow q).labels=p.labels++q.labels := by
  induction p with | nil => rfl | cons _ t ih => simp [follow,labels,ih]

def reverse {a b} : RimWalk G a b → RimWalk G b a
  | .nil x => .nil x
  | .cons edge tail => tail.reverse.follow (single edge.rev)

@[simp] theorem labels_reverse {a b} (p : RimWalk G a b) : p.reverse.labels=p.labels.reverse := by
  induction p with | nil => rfl | cons e t ih => simp [reverse,ih,labels,single,RimEdge.rev]

@[simp] theorem vertices_reverse {a b} (p : RimWalk G a b) : p.reverse.vertices=p.vertices.reverse := by
  induction p with
  | nil => rfl
  | @cons x y z e t ih =>
    change (t.reverse.follow (single e.rev)).starts++[x] = ((x::t.starts)++[z]).reverse
    rw [starts_follow]; change (t.reverse.starts ++ [y]) ++ [x] = _
    change t.reverse.vertices ++ [x] = _
    rw [ih]; simp [vertices]

noncomputable def edgeAt {a b} (p : RimWalk G a b) (i : Fin p.starts.length) :
    RimEdge G (p.starts[i.val]) (p.vertices[i.val+1]'(by simp [vertices])) := by
  induction p with
  | nil => exact Fin.elim0 i
  | @cons x y z e t ih =>
    obtain ⟨k,lt⟩ := i
    cases k with
    | zero =>
      cases t with
      | nil => exact e
      | cons => exact e
    | succ k =>
      have kt : k<t.starts.length := by simpa [starts] using lt
      exact ih ⟨k,kt⟩

theorem at_label {a b} (p : RimWalk G a b) (i : Fin p.starts.length) :
    (p.edgeAt i).label=p.labels[i.val]'(by rw [length_eq];exact i.isLt) := by
  induction p with
  | nil => exact Fin.elim0 i
  | @cons x y z e t ih =>
    obtain ⟨k,lt⟩ := i
    cases k with
    | zero => cases t <;> rfl
    | succ k => exact ih ⟨k,by simpa [starts] using lt⟩

theorem boundary_permutation {a} (p : RimWalk G a a) (hh : 3≤h)
    (length : 2≤p.starts.length) (rare : p.labels.Nodup) :
    p.starts.Perm (dualRow G (apex M)) := by
  generalize nEq : p.starts.length=m at *
  cases m with
  | zero => omega
  | succ n =>
    let f (i : Fin (n+1)) := p.starts[i.val]'(by omega)
    let t (i : Fin (n+1)) := p.labels[i.val]'(by rw [length_eq];omega)
    have inj : Function.Injective t := fun i j eq => Fin.ext (index_eq rare (by rw [length_eq];omega) (by rw [length_eq];omega) eq)
    have wit (i : Fin (n+1)) : OnCycle (dualRow G (apex M)) (f i) (f (cyclicNext i)) ∧
        apex M∉triangle (t i) ∧ f i∈triangle (t i) ∧ f (cyclicNext i)∈triangle (t i) := by
      let k : Fin p.starts.length := ⟨i.val,by omega⟩
      let edge := p.edgeAt k
      have eqTag : edge.label=t i := p.at_label k
      have endEq : p.vertices[i.val+1]'(by simp [vertices];omega) = f (cyclicNext i) := by
        by_cases inside : i.val+1<n+1
        · have lt : i.val+1<p.starts.length := by omega
          simp [vertices,List.getElem_append_left lt,f,cyclicNext,inside]
        · have eq : i.val+1=p.starts.length := by omega
          have first := head_of_pos p (by omega)
          change (p.starts++[a])[i.val+1]'(by simp;omega) = _
          rw [List.getElem_concat_length eq]; simpa [f,cyclicNext,inside] using first.symm
      exact ⟨endEq ▸ edge.cyclic,eqTag ▸ edge.nonapex,eqTag ▸ edge.first,eqTag ▸ endEq ▸ edge.last⟩
    obtain ⟨once,cover,_⟩ := actual_perimeter G hh (by omega) f t inj (fun i=>(wit i).1) (fun i=>(wit i).2)
    have simple : p.starts.Nodup := by
      apply List.pairwise_iff_getElem.mpr;intro i j hi hj ij eq
      have fi : f ⟨i,by omega⟩=f ⟨j,by omega⟩ := eq
      have := congrArg Fin.val (once fi); dsimp at this;omega
    apply (List.perm_ext_iff_of_nodup simple (boundary_cycle G hh).1).2
    intro x; rw [show x∈dualRow G (apex M) ↔ ∃ i,f i=x from cover x]
    constructor
    · intro m;obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp m;exact ⟨⟨k,by omega⟩,rfl⟩
    · rintro ⟨i,rfl⟩;exact List.getElem_mem _

end RimWalk
end DiskFullerene.StripFresh

namespace DiskFullerene.StripFresh
open Dual EndLabels Separation

/-- An ordered strip uses a single boundary side of each middle triangle.
The other two sides are its successive chords. The current pair is
ordered so the vertex kept in a move comes first in the next pair. -/
inductive Trace {M : MapData} (G : IsDiskFullerene M h) : Face M → Face M → Face M → Face M → Type
  | done (x y) : Trace G x y x y
  | keepFirst {x y z a b} (edge : RimEdge G y z) (tail : Trace G x z a b) : Trace G x y a b
  | keepSecond {x y z a b} (edge : RimEdge G x z) (tail : Trace G y z a b) : Trace G x y a b

namespace Trace
variable {M : MapData} {G : IsDiskFullerene M h}

def grow {x y a b} (trace : Trace G x y a b) (p : RimWalk G x y) : RimWalk G a b :=
  match trace with
  | .done _ _ => p
  | .keepFirst e t => t.grow (p.follow (.single e))
  | .keepSecond e t => t.grow (p.reverse.follow (.single e))

def newVertices {x y a b} : Trace G x y a b → List (Face M)
  | .done _ _ => []
  | .keepFirst (z:=z) _ t | .keepSecond (z:=z) _ t => z::t.newVertices

def triangles {x y a b} : Trace G x y a b → List (Fin M.ord)
  | .done _ _ => []
  | .keepFirst e t | .keepSecond e t => e.label::t.triangles

theorem length_eq {x y a b} (t : Trace G x y a b) : t.newVertices.length=t.triangles.length := by
  induction t <;> simp_all [newVertices,triangles]

theorem labels_grow {x y a b} (t : Trace G x y a b) (p : RimWalk G x y) :
    (t.grow p).labels.Perm (p.labels ++ t.triangles) := by
  induction t with
  | done => simp [grow,triangles]
  | keepFirst e t ih =>
    simpa [grow,triangles,RimWalk.single,RimWalk.labels] using ih (p.follow (.single e))
  | keepSecond e t ih =>
    have shape := ih (p.reverse.follow (.single e))
    simp only [RimWalk.labels_follow, RimWalk.labels_reverse] at shape
    exact shape.trans (by simpa [triangles,RimWalk.single,RimWalk.labels] using
      (List.reverse_perm p.labels).append_right (e.label::t.triangles))

private theorem add_node {x y z} (p : RimWalk G x y) (e : RimEdge G y z) :
    (p.follow (.single e)).vertices=p.vertices++[z] := by simp [RimWalk.vertices,RimWalk.single,RimWalk.starts]

theorem vertices_grow {x y a b} (t : Trace G x y a b) (p : RimWalk G x y) :
    (t.grow p).vertices.Perm (p.vertices++t.newVertices) := by
  induction t with
  | done => simp [grow,newVertices]
  | keepFirst e t ih =>
    simpa [grow,newVertices,add_node] using ih (p.follow (.single e))
  | @keepSecond x y z a b e t ih =>
    have shape := ih (p.reverse.follow (.single e))
    rw [add_node,RimWalk.vertices_reverse,List.append_assoc] at shape
    exact shape.trans ((List.reverse_perm p.vertices).append_right (z::t.newVertices))

/-- The five edges at each end and the single boundary edge of each
middle triangle suffice to count and label the full outer rim. Label
distinctness here refers only to genuine nonapical primal triangles. -/
theorem fresh_and_length {x y a b} (t : Trace G x y a b)
    (left : RimWalk G x y) (right : RimWalk G b a)
    (hh : 3≤h) (fiveL : left.labels.length=5) (fiveR : right.labels.length=5)
    (rare : (left.labels ++ t.triangles ++ right.labels).Nodup) :
    let all := left.vertices ++ t.newVertices ++ right.starts.tail
    all.Nodup ∧ all.Perm (dualRow G (apex M)) ∧ t.triangles.length+10=h := by
  let grown := t.grow left
  let closed := grown.follow right
  have same : closed.labels.Perm (left.labels ++ t.triangles ++ right.labels) := by
    simpa [closed,grown] using (t.labels_grow left).append_right right.labels
  have count := same.length_eq
  simp only [List.length_append,fiveL,fiveR] at count
  have total : closed.starts.length=t.triangles.length+10 := by rw [←closed.length_eq];omega
  have perm := closed.boundary_permutation hh (by omega) (same.nodup_iff.mpr rare)
  have rLen : 0<right.starts.length := by rw [←right.length_eq,fiveR]; decide
  have first := right.head_of_pos rLen
  have R : right.starts=b::right.starts.tail := by
    cases right with | nil => contradiction | cons => rfl
  have refactor : closed.starts=grown.vertices++right.starts.tail := by
    change (grown.follow right).starts=_
    rw [RimWalk.starts_follow]
    conv => lhs;rw [R]
    simp [RimWalk.vertices]
  have M : closed.starts.Perm (left.vertices++t.newVertices++right.starts.tail) := by
    rw [refactor]; exact (t.vertices_grow left).append_right _
  have final := M.symm.trans perm
  exact ⟨final.nodup_iff.mpr (boundary_cycle G hh).1,final,
    total.symm.trans (perm.length_eq.trans (boundary_cycle G hh).2.1)⟩

end Trace
end DiskFullerene.StripFresh
