import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-! Color-preserving isomorphism of finite incidence structures by
inclusion–exclusion over forbidden target vertices. -/
namespace Recognition.StateIso
open Finset

/-- Vertex classes and labels may be encoded in a natural-number color. Both
directions of every incidence edge are present in an undirected state graph. -/
structure Colored (n : Nat) where
  color : Fin n → Nat
  edge : Fin n → Fin n → Bool

def Preserves (A : Colored n) (B : Colored m) (f : Fin n → Fin m) : Prop :=
  (∀ i, A.color i = B.color (f i)) ∧ ∀ i j, A.edge i j = true → B.edge (f i) (f j) = true

instance (A : Colored n) (B : Colored m) (f : Fin n → Fin m) : Decidable (Preserves A B f) := by
  unfold Preserves; infer_instance

def Iso (A : Colored n) (B : Colored m) : Prop :=
  ∃ f : Fin n ≃ Fin m, (∀i, A.color i = B.color (f i)) ∧ ∀ i j, A.edge i j = B.edge (f i) (f j)

def arcs (A : Colored n) := Finset.univ.filter fun e : Fin n × Fin n => A.edge e.1 e.2

def homs (A : Colored n) (B : Colored m) : Finset (Fin n → Fin m) :=
  Finset.univ.filter (Preserves A B)

def missed (f : Fin n → Fin m) := Finset.univ \ Finset.univ.image f

/-- Number of color- and adjacency-preserving maps avoiding each target in Y. -/
def homCount (A : Colored n) (B : Colored m) (Y : Finset (Fin m)) : Nat :=
  ((homs A B).filter fun f => Y ⊆ missed f).card

def alternating (h : Finset (Fin m) → Nat) : Int :=
  ∑ Y ∈ (Finset.univ : Finset (Fin m)).powerset, (-1:Int)^Y.card * (h Y : Int)

theorem inclusion_exclusion (A : Colored n) (B : Colored m) :
    alternating (homCount A B) =
      (((homs A B).filter fun f => missed f = ∅).card : Int) := by
  let subsets := (Finset.univ : Finset (Fin m)).powerset
  have indicators (Y : Finset (Fin m)) : (homCount A B Y : Int) =
      ∑ f ∈ homs A B, if Y ⊆ missed f then (1:Int) else 0 :=
    (Finset.sum_boole _ _).symm
  calc
    alternating (homCount A B) = ∑ Y ∈ subsets, ∑ f ∈ homs A B,
        if Y ⊆ missed f then (-1:Int)^Y.card else 0 := by
      unfold alternating
      apply Finset.sum_congr rfl
      intro Y _
      rw [indicators,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _; split <;> simp
    _ = ∑ f ∈ homs A B, ∑ Y ∈ subsets, if Y ⊆ missed f then (-1:Int)^Y.card else 0 :=
      Finset.sum_comm
    _ = ∑ f ∈ homs A B, if missed f=∅ then (1:Int) else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      rw [←Finset.sum_filter]
      have restrict : subsets.filter (fun Y => Y ⊆ missed f) = (missed f).powerset := by
        ext Y; simp [subsets]
      rw [restrict,Finset.sum_powerset_neg_one_pow_card]
    _ = _ := Finset.sum_boole _ _

private theorem missed_empty (f : Fin n → Fin m) : missed f = ∅ ↔ Function.Surjective f := by
  constructor
  · intro h y
    by_contra no
    have mem : y ∈ missed f := by simpa [missed] using no
    rw [h] at mem; exact Finset.notMem_empty _ mem
  · intro all
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y
    obtain ⟨a,hit⟩ := all y
    simp [missed,←hit]

private theorem arc_image {A : Colored n} {B : Colored m} (f : Fin n → Fin m)
    (pres : Preserves A B f) : (arcs A).image (Prod.map f f) ⊆ arcs B := by
  intro e he
  obtain ⟨⟨i,j⟩,mem,rfl⟩ := Finset.mem_image.mp he
  simpa [arcs] using pres.2 i j (by simpa [arcs] using mem)

/-- Equal vertex and incidence counts turn a surjective homomorphism into
an isomorphism. The equality of counts is checked separately by the comparator. -/
theorem iso_of_cover {A : Colored n} {B : Colored m} (size : n=m)
    (edges : (arcs A).card = (arcs B).card)
    (f : Fin n → Fin m) (pres : Preserves A B f) (onto : Function.Surjective f) : Iso A B := by
  have bi := (Fintype.bijective_iff_surjective_and_card f).mpr ⟨onto,by simpa using size⟩
  let equ := Equiv.ofBijective f bi
  have inj : Function.Injective (Prod.map f f) := fun x y h =>
    Prod.ext (bi.1 (congrArg Prod.fst h)) (bi.1 (congrArg Prod.snd h))
  have same : (arcs A).image (Prod.map f f) = arcs B :=
    Finset.eq_of_subset_of_card_le (arc_image f pres) (by rw [Finset.card_image_of_injective _ inj,edges])
  refine ⟨equ,pres.1,fun i j => ?_⟩
  apply Bool.eq_iff_iff.mpr
  refine ⟨pres.2 i j,?_⟩
  intro back
  change B.edge (f i) (f j)=true at back
  have h : (f i,f j) ∈ (arcs A).image (Prod.map f f) := same ▸ (by simpa [arcs] using back)
  obtain ⟨u,hu,he⟩ := Finset.mem_image.mp h
  have eq : u=(i,j) := inj he
  subst u
  simpa [arcs] using hu

private theorem iso_counts {A : Colored n} {B : Colored m} (iso : Iso A B) :
    n=m ∧ (arcs A).card=(arcs B).card := by
  obtain ⟨e,color,edge⟩ := iso
  have one {r s} {X : Colored r} {Y : Colored s} (g : Fin r ≃ Fin s)
      (col : ∀v, X.color v=Y.color (g v)) (ed : ∀i j, X.edge i j=Y.edge (g i) (g j)) :
      (arcs X).card ≤ (arcs Y).card := by
    have h := Finset.card_le_card (arc_image g ⟨col, fun i j a => (ed i j).symm.trans a⟩)
    rwa [Finset.card_image_of_injective _ (fun x y eq =>
      Prod.ext (g.injective (congrArg Prod.fst eq)) (g.injective (congrArg Prod.snd eq)))] at h
  exact ⟨by simpa using Fintype.card_congr e,Nat.le_antisymm (one e color edge)
    (one e.symm (fun v => by simpa using (color (e.symm v)).symm)
      (fun i j => by simpa using (edge (e.symm i) (e.symm j)).symm))⟩

def compare (A : Colored n) (B : Colored m) : Bool :=
  decide (n=m ∧ (arcs A).card=(arcs B).card ∧ 0 < alternating (homCount A B))

theorem compare_iff (A : Colored n) (B : Colored m) : compare A B = true ↔ Iso A B := by
  rw [compare,decide_eq_true_eq,inclusion_exclusion,Int.natCast_pos,Finset.card_pos]
  constructor
  · rintro ⟨nm,edges,f,mem⟩
    obtain ⟨h,empty⟩ := Finset.mem_filter.mp mem
    exact iso_of_cover nm edges f (Finset.mem_filter.mp h).2 ((missed_empty f).mp empty)
  · intro iso
    obtain ⟨c,e⟩ := iso_counts iso
    obtain ⟨eq,col,edges⟩ := iso
    exact ⟨c,e,eq,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,col,fun i j h => (edges i j).symm.trans h⟩,(missed_empty _).mpr eq.surjective⟩⟩

theorem count_le (A : Colored n) (B : Colored m) (Y : Finset (Fin m)) : homCount A B Y ≤ m^n := by
  apply (Finset.card_filter_le ..).trans
  exact (Finset.card_filter_le ..).trans (by simp)

theorem number_of_terms (m : Nat) : ((Finset.univ : Finset (Fin m)).powerset).card=2^m := by simp

end Recognition.StateIso
