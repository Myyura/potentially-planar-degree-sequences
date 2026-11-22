import QuotientDP
import StateIso

/-! A small directed, coloured graph for comparing two frontier states.
A directed side has separate incidences for its first and second endpoint.
Block membership is read from the relation between side nodes. -/
namespace Recognition.StateIncidence
open Recognition.QuotientDP
abbrev Item (n : Nat) := Fin n ⊕ Side n

def hasSide (s : State n) (e : Side n) := s.pending e || s.sealed e ||
  decide (∃ f, s.blocks e f=true ∨ s.blocks f e=true)
def hasVertex (s : State n) (x : Fin n) := s.current x != 0 ||
  decide (∃ e, hasSide s e=true ∧ (e.1=x ∨ e.2=x))
def present (s : State n) : Item n → Bool := Sum.elim (hasVertex s) (hasSide s)
abbrev Node (s : State n) := {i : Item n // present s i=true}

def tint (s : State n) : Item n → Nat
  | .inl x => 4+s.current x
  | .inr e => 2*(s.pending e).toNat+(s.sealed e).toNat

def arc (s : State n) : Item n → Item n → Bool
  | .inl _,.inl _ => false
  | .inl x,.inr e => x==e.1
  | .inr e,.inl x => e.2==x
  | .inr e,.inr f => s.blocks e f

def names (s : State n) : List (Item n) :=
  ((List.finRange n).filter (hasVertex s)).map Sum.inl ++
  ((((List.finRange n).flatMap (fun x => (List.finRange n).map (x,·))).filter (hasSide s)).map Sum.inr)

theorem names_mem (s : State n) (x : Item n) : x∈names s ↔ present s x=true := by
  cases x with
  | inl x => simp [names,present]
  | inr e => rcases e with ⟨x,y⟩; simp [names,present,List.mem_flatMap]

theorem names_nd (s : State n) : (names s).Nodup := by
  let xs := List.finRange n
  have cart : (xs.flatMap (fun x => xs.map (x,·))).Nodup := by
    apply List.pairwise_flatMap.mpr
    refine ⟨fun x _ => (List.nodup_finRange n).map (fun _ _ h => (Prod.mk.inj h).2),?_⟩
    apply (List.nodup_finRange n).imp
    rintro x y ne a ha b hb eq
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hb
    exact ne (Prod.mk.inj eq).1
  apply List.nodup_append.mpr
  refine ⟨((List.nodup_finRange n).filter _).map Sum.inl_injective,
    (cart.filter _).map Sum.inr_injective,?_⟩
  intro a ha b hb
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hb
  exact Sum.inl_ne_inr

private noncomputable def numbering (s : State n) : Fin (names s).length ≃ Node s :=
  Equiv.ofBijective (fun i => ⟨(names s).get i,(names_mem s _).mp (List.get_mem ..)⟩) (by
    constructor
    · intro i j h
      exact (List.nodup_iff_injective_get.mp (names_nd s)) (congrArg Subtype.val h)
    · rintro ⟨x,h⟩
      obtain ⟨i,hi,eq⟩ := List.getElem_of_mem ((names_mem s x).mpr h)
      exact ⟨⟨i,hi⟩,Subtype.ext eq⟩)

def graph (s : State n) : StateIso.Colored (names s).length where
  color i := tint s ((names s).get i)
  edge i j := arc s ((names s).get i) ((names s).get j)

private def Niso (s t : State n) := ∃ h : Node s ≃ Node t,
    (∀ x, tint s x.val=tint t (h x).val) ∧ ∀ x y, arc s x.val y.val=arc t (h x).val (h y).val

private theorem graph_iff (s t : State n) : StateIso.Iso (graph s) (graph t) ↔ Niso s t := by
  have proj (u : State n) (i) : ((numbering u) i).val=(names u).get i := rfl
  constructor
  · rintro ⟨h,c,a⟩
    let e := ((numbering s).symm.trans h).trans (numbering t)
    refine ⟨e,?_,?_⟩
    · intro x; obtain ⟨i,rfl⟩:= (numbering s).surjective x
      simpa [e,proj,graph] using c i
    · intro x y; obtain ⟨i,rfl⟩:= (numbering s).surjective x
      obtain ⟨j,rfl⟩:= (numbering s).surjective y
      simpa [e,proj,graph] using a i j
  · rintro ⟨h,c,a⟩
    let e := ((numbering s).trans h).trans (numbering t).symm
    have out (i) : (numbering t) (e i)=h ((numbering s) i) := by simp [e]
    refine ⟨e,?_,?_⟩
    · intro i; change tint s _=tint t _
      rw [←proj,←proj,out]; exact c _
    · intro i j; change arc s _ _=arc t _ _
      rw [←proj s,←proj s,←proj t,←proj t,out,out]; exact a _ _

private theorem hasSide_map {p : Equiv.Perm (Fin n)} {s t : State n} (h : Iso p s t) (e : Side n) :
    hasSide t (edgeMap p e)=hasSide s e := by
  unfold hasSide
  have ex : (∃ f, t.blocks (edgeMap p e) f=true ∨ t.blocks f (edgeMap p e)=true) ↔
      ∃ f, s.blocks e f=true ∨ s.blocks f e=true := by
    rw [←(edgeMap p).exists_congr_right]
    simp only [h.blocks]
  simp [h.pending,h.sealed,ex]

private theorem hasVertex_map {p : Equiv.Perm (Fin n)} {s t : State n} (h : Iso p s t) (x) :
    hasVertex t (p x)=hasVertex s x := by
  unfold hasVertex
  have ex : (∃ e, hasSide t e=true ∧ (e.1=p x ∨ e.2=p x)) ↔
      ∃ e, hasSide s e=true ∧ (e.1=x ∨ e.2=x) := by
    rw [←(edgeMap p).exists_congr_right]
    simp only [hasSide_map h]; simp [edgeMap]
  simp [h.value,ex]

private theorem node_map {p : Equiv.Perm (Fin n)} {s t : State n} (h : Iso p s t) : Niso s t := by
  let e := p.sumCongr (edgeMap p)
  have mem (i : Item n) : present s i=true ↔ present t (e i)=true := by
    cases i <;> simp [present,e,hasSide_map h,hasVertex_map h]
  let q : Node s ≃ Node t := e.subtypeEquiv (p := fun x => present s x=true) (q := fun x => present t x=true) mem
  refine ⟨q,?_,?_⟩
  · rintro ⟨x,hx⟩; cases x <;> simp [q,e,tint,h.value,h.pending,h.sealed]
  · rintro ⟨x,hx⟩ ⟨y,hy⟩
    cases x <;> cases y <;> simp [q,e,arc,edgeMap]
    exact (h.blocks _ _).symm


private abbrev AV (s : State n) := {x : Fin n // hasVertex s x=true}
private abbrev ES (s : State n) := {e : Side n // hasSide s e=true}
private def vn {s : State n} (x : AV s) : Node s := ⟨.inl x.val,x.property⟩
private def en {s : State n} (x : ES s) : Node s := ⟨.inr x.val,x.property⟩

private theorem small (s : State n) (e : Side n) : tint s (.inr e)<4 := by
  change 2*(s.pending e).toNat+(s.sealed e).toNat<4
  cases s.pending e <;> cases s.sealed e <;> decide

private theorem endpoints {s : State n} (e : ES s) :
    hasVertex s e.val.1=true ∧ hasVertex s e.val.2=true := by
  constructor <;> unfold hasVertex <;> apply Bool.or_eq_true_iff.mpr <;> right <;>
    apply decide_eq_true <;> exact ⟨e.val,e.property,by simp⟩

private theorem node_back {s t : State n} (iso : Niso s t) (rem : t.remaining=s.remaining)
    (used : t.used=s.used) (faces : t.faces=s.faces) : Same s t := by
  classical
  obtain ⟨h,tints,arcs⟩ := iso
  have lhs {x : AV s} : ∃ y : AV t,h (vn x)=vn y := by
    generalize eq : h (vn x)=image
    obtain ⟨a,ha⟩ := image
    cases a with
    | inl y => exact ⟨⟨y,ha⟩,rfl⟩
    | inr e =>
      have hc := tints (vn x); rw [eq] at hc
      have := small t e; change 4+s.current x=tint t (.inr e) at hc; omega
  have ontoLeft (y : AV t) : ∃ x : AV s,h (vn x)=vn y := by
    obtain ⟨⟨a,ha⟩,eq⟩ := h.surjective (vn y)
    cases a with
    | inl a => exact ⟨⟨a,ha⟩,eq⟩
    | inr e =>
      have hc := tints ⟨.inr e,ha⟩
      rw [eq] at hc
      have := small s e
      change tint s (.inr e)=4+t.current y at hc; omega
  let f (x : AV s) := (lhs (x := x)).choose
  have fh (x : AV s) : h (vn x)=vn (f x) := (lhs (x := x)).choose_spec
  have vi (u : State n) : Function.Injective (@vn n u) := by
    intro a b eq; exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val eq))
  let l := Equiv.ofBijective f (by
    constructor
    · intro x y eq; apply vi s; apply h.injective; rw [fh,fh,eq]
    · intro y; obtain ⟨x,eq⟩ := ontoLeft y; exact ⟨x,vi t ((fh x).symm.trans eq)⟩)
  let p := l.extendSubtype
  have onLeft (x : AV s) : (h (vn x)).val=.inl (p x.val) := by
    rw [fh,l.extendSubtype_apply_of_mem _ x.property]; rfl
  have leftIff (x : Fin n) : hasVertex t (p x)=true ↔ hasVertex s x=true :=
    ⟨fun hx => Classical.byContradiction fun ne => (l.extendSubtype_not_mem _ ne) hx,fun hx => l.extendSubtype_mem _ hx⟩
  have rightImage (e : ES s) : ∃ y : ES t,h (en e)=en y := by
    generalize eq : h (en e)=a
    obtain ⟨a,ha⟩ := a
    cases a with
    | inr e => exact ⟨⟨e,ha⟩,rfl⟩
    | inl x =>
      have hc := tints (en e); rw [eq] at hc
      have := small s e
      change tint s (.inr e.val)=4+t.current x at hc; omega
  have onRight (e : ES s) : (h (en e)).val = .inr (edgeMap p e.val) := by
    obtain ⟨y,eq⟩ := rightImage e
    let x₁ : AV s := ⟨e.val.1,(endpoints e).1⟩
    let x₂ : AV s := ⟨e.val.2,(endpoints e).2⟩
    have a := arcs (vn x₁) (en e)
    have b := arcs (en e) (vn x₂)
    rw [onLeft,eq] at a b
    change (e.val.1==e.val.1)=(p e.val.1==y.val.1) at a
    change (e.val.2==e.val.2)=(y.val.2==p e.val.2) at b
    have a' : p e.val.1=y.val.1 := beq_iff_eq.mp (by simpa using a.symm)
    have b' : y.val.2=p e.val.2 := beq_iff_eq.mp (by simpa using b.symm)
    rw [eq]; exact congrArg Sum.inr (Prod.ext a'.symm b')
  have rightIff (e : Side n) : hasSide t (edgeMap p e)=true ↔ hasSide s e=true := by
    constructor
    · intro yes
      obtain ⟨⟨q,mem⟩,hq⟩ := h.surjective (en ⟨_,yes⟩)
      cases q with
      | inl x =>
        have nope := onLeft ⟨x,mem⟩; change (h ⟨.inl x,mem⟩).val=_ at nope
        rw [hq] at nope; cases nope
      | inr a =>
        have got := onRight ⟨a,mem⟩; change (h ⟨.inr a,mem⟩).val=_ at got
        rw [hq] at got
        exact (edgeMap p).injective (Sum.inr.inj got) ▸ mem
    · intro yes
      have g := (h (en ⟨e,yes⟩)).property
      rwa [onRight] at g
  have missing (u : State n) (e : Side n) (no : hasSide u e≠true) :
      u.pending e=false ∧ u.sealed e=false ∧
      (∀ a, u.blocks e a=false ∧ u.blocks a e=false) := by
    simpa [hasSide,not_or,and_assoc] using no
  have fields (e : Side n) : t.pending (edgeMap p e)=s.pending e ∧ t.sealed (edgeMap p e)=s.sealed e := by
    by_cases yes : hasSide s e=true
    · have hc := tints (en ⟨e,yes⟩); rw [onRight] at hc
      change 2*(s.pending e).toNat+(s.sealed e).toNat=2*(t.pending (edgeMap p e)).toNat+(t.sealed (edgeMap p e)).toNat at hc
      have inj : ∀ a b c d : Bool, 2*a.toNat+b.toNat=2*c.toNat+d.toNat → c=a ∧ d=b := by decide
      exact inj _ _ _ _ hc
    · obtain ⟨a,b,_⟩ := missing s e yes
      obtain ⟨c,d,_⟩ := missing t _ (mt (rightIff e).mp yes)
      exact ⟨c.trans a.symm,d.trans b.symm⟩
  refine ⟨p,fun e => (fields e).1,fun e => (fields e).2,?_,?_,rem,used,faces⟩
  · intro e f
    by_cases he : hasSide s e=true
    · by_cases hf : hasSide s f=true
      · have a := arcs (en ⟨e,he⟩) (en ⟨f,hf⟩); rw [onRight,onRight] at a
        exact a.symm
      · exact ((missing t _ (mt (rightIff f).mp hf)).2.2 _).2.trans ((missing s f hf).2.2 e).2.symm
    · exact ((missing t _ (mt (rightIff e).mp he)).2.2 _).1.trans ((missing s e he).2.2 f).1.symm
  · intro x
    by_cases yes : hasVertex s x=true
    · have hc := tints (vn ⟨x,yes⟩); rw [onLeft] at hc
      change 4+s.current x=4+t.current (p x) at hc; omega
    · have no := mt (leftIff x).mp yes
      simp [hasVertex] at no yes
      exact no.1.trans yes.1.symm

/-- Graph isomorphism on only the supported names and sides suffices. The
three global fields are compared independently. -/
theorem same_iff (s t : State n) : Same s t ↔ s.remaining=t.remaining ∧ s.used=t.used ∧
    s.faces=t.faces ∧ StateIso.Iso (graph s) (graph t) := by
  constructor
  · rintro ⟨p,h⟩
    exact ⟨h.remaining.symm,h.used.symm,h.faces.symm,(graph_iff s t).mpr (node_map h)⟩
  · rintro ⟨r,u,f,g⟩; exact node_back ((graph_iff s t).mp g) r.symm u.symm f.symm

def compare (s t : State n) := decide (s.remaining=t.remaining ∧ s.used=t.used ∧ s.faces=t.faces) &&
  StateIso.compare (graph s) (graph t)

theorem compare_iff (s t : State n) : compare s t=true ↔ Same s t := by
  rw [same_iff]; simp [compare,StateIso.compare_iff,and_assoc]

end Recognition.StateIncidence
