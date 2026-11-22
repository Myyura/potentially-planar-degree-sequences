import SparseCompare
import Outline
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Elimination orders from balanced separator trees, including contracted
pieces of a host whose vertices have been split into boundedly many lanes. -/
namespace Recognition.MinorWidth
open Finset StateIso PlanarDegrees.Frontier

def spine (home : Fin n → List Nat) (p : List Nat) :=
  univ.filter fun i => home i <+: p

structure Hierarchy (A : Colored n) (w : Nat) where
  home : Fin n → List Nat
  adjacent : ∀i j,A.edge i j=true → home i <+: home j ∨ home j <+: home i
  cap : ∀p,(spine home p).card≤w

theorem ancestor_prefix (a b : List Nat) : Outline.isAncestor a b ↔ a <+: b := by
  induction a generalizing b with
  | nil => simp [Outline.isAncestor]
  | cons x xs ih => cases b <;> simp [Outline.isAncestor,List.cons_prefix_iff,ih,eq_comm]

def adjacency (A : Colored n) (i j : Nat) :=
  ∃x y : Fin n,x.val=i ∧ y.val=j ∧ A.edge x y=true

/-- A balanced separator oracle on the host supplies the hierarchy, with
uniform costs and at most 28(√n+1) vertices on any chain. -/
theorem from_separator (A : Colored n)
    (sep : Outline.Separators (List.range n) (adjacency A) (fun _ => 1)) :
    Nonempty (Hierarchy A (28*(n.sqrt+1))) := by
  obtain ⟨D⟩ := Outline.layout _ _ (by simp) sep List.nodup_range
  let home (i : Fin n) := D.home i.val
  refine ⟨⟨home,?_,?_⟩⟩
  · intro i j edge
    exact (D.nested i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
      ⟨i,j,rfl,rfl,edge⟩).imp (ancestor_prefix ..).mp (ancestor_prefix ..).mp
  · intro p
    obtain ⟨xs,cs,_,nd,mass,chain,includes⟩ := D.path p
    have incl : (spine home p).image Fin.val⊆xs.toFinset := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      exact List.mem_toFinset.mpr (includes _ (List.mem_range.mpr x.isLt) ((ancestor_prefix ..).mpr (mem_filter.mp hx).2))
    have card := Finset.card_le_card incl
    rw [card_image_of_injective _ Fin.val_injective,List.toFinset_card_of_nodup nd] at card
    have h := separator_chain_bound chain
    simp [Outline.weight,Outline.mass] at h mass
    have sq := Nat.lt_succ_sqrt n
    nlinarith

def relabel (A : Colored n) (p : Equiv.Perm (Fin n)) : Colored n :=
  ⟨fun i => A.color (p i),fun i j => A.edge (p i) (p j)⟩

theorem relabel_iso (A : Colored n) (p : Equiv.Perm (Fin n)) : Iso (relabel A p) A :=
  ⟨p,fun _ => rfl,fun _ _ => rfl⟩

/-- Sorting the vertices by decreasing home depth gives an elimination
layout with the same chain bound. -/
theorem elimination (A : Colored n) (D : Hierarchy A w) :
    ∃p : Equiv.Perm (Fin n), Nonempty (BagHom.Layout (relabel A p) w) := by
  let depth (i : Fin n) : Natᵒᵈ := OrderDual.toDual (D.home i).length
  let p := Tuple.sort depth
  let home (i : Fin n) := D.home (p i)
  let later (i : Fin n) := spine home (home i)
  have order {i j : Fin n} (lt : i≤j) : (home j).length≤(home i).length := Tuple.monotone_sort depth lt
  have orient (i j : Fin n) (edge : A.edge (p i) (p j)=true) :
      home i <+: home j ∨ home j <+: home i := D.adjacent _ _ edge
  refine ⟨p,⟨⟨later,?_,?_,?_⟩⟩⟩
  · intro i
    have map_ : (later i).map p.toEmbedding=spine D.home (home i) := by
      ext y;obtain ⟨j,rfl⟩:=p.surjective y;simp [later,spine,home]
    simpa only [←map_,Finset.card_map] using D.cap (home i)
  · intro i j edge _
    have h := orient i j edge
    split <;> rename_i cmp
    · exact mem_filter.mpr ⟨mem_univ _,h.elim (fun x => (x.eq_of_length_le (order cmp)) ▸ List.prefix_rfl) id⟩
    · exact mem_filter.mpr ⟨mem_univ _,h.elim id (fun x => (x.eq_of_length_le (order (le_of_not_ge cmp))) ▸ List.prefix_rfl)⟩
  · intro r i hi j hj lt
    exact mem_filter.mpr ⟨mem_univ _,List.prefix_of_prefix_length_le (mem_filter.mp hj).2
      (mem_filter.mp hi).2 (order lt.le)⟩

/-- A model obtained by splitting vertices, deleting edges, and contracting
connected branches. Congestion counts how many target branches use a host vertex. -/
structure Model (A : Colored n) (H : Colored m) (c : Nat) where
  pieces : Fin n → Finset (Fin m)
  nonempty : ∀v,(pieces v).Nonempty
  connected : ∀v,∀x∈pieces v,∀y∈pieces v,
    Walk (fun i j => i∈pieces v ∧ j∈pieces v ∧ (H.edge i j=true ∨ H.edge j i=true)) x y
  meets : ∀i j,A.edge i j=true → ∃x∈pieces i,∃y∈pieces j,x=y ∨ H.edge x y=true ∨ H.edge y x=true
  load : ∀x,(univ.filter (fun i => x∈pieces i)).card≤c

theorem contract (A : Colored n) (H : Colored m) (M : Model A H c) (D : Hierarchy H w) :
    Nonempty (Hierarchy A (c*w)) := by
  classical
  have minimal (v) := (M.pieces v).exists_min_image (fun x => (D.home x).length) (M.nonempty v)
  let root (v) := (minimal v).choose
  have inside (v) : root v∈M.pieces v := (minimal v).choose_spec.1
  have minLength (v) (x) (hx : x∈M.pieces v) : (D.home (root v)).length≤(D.home x).length :=
    (minimal v).choose_spec.2 _ hx
  have ancestor (v) (x) (mem : x∈M.pieces v) : D.home (root v) <+: D.home x := by
    have walk := M.connected v _ (inside v) x mem
    induction walk with
    | refl => exact List.prefix_rfl
    | @step y z _ next ih =>
      obtain ⟨hy,hz,step⟩ := next
      specialize ih hy
      have cmp : D.home y <+: D.home z ∨ D.home z <+: D.home y :=
        step.elim (D.adjacent _ _) (fun h => (D.adjacent _ _ h).symm)
      exact cmp.elim ih.trans (fun h => List.prefix_of_prefix_length_le ih h (minLength v z hz))
  let home (v) := D.home (root v)
  refine ⟨⟨home,?_,?_⟩⟩
  · intro i j e
    obtain ⟨x,hx,y,hy,contact⟩ := M.meets i j e
    have a:=ancestor i x hx
    have b:=ancestor j y hy
    rcases contact with rfl|edge|edge
    · exact List.prefix_or_prefix_of_prefix a b
    · rcases D.adjacent _ _ edge with xy|yx
      · exact List.prefix_or_prefix_of_prefix (a.trans xy) b
      · exact List.prefix_or_prefix_of_prefix a (b.trans yx)
    · rcases D.adjacent _ _ edge with yx|xy
      · exact List.prefix_or_prefix_of_prefix a (b.trans yx)
      · exact List.prefix_or_prefix_of_prefix (a.trans xy) b
  · intro p
    apply (Finset.card_le_mul_card_image_of_maps_to (f := root) (t := spine D.home p)
      (fun _ mem => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp mem).2⟩) c ?_).trans (Nat.mul_le_mul_left _ (D.cap p))
    intro x _
    apply (card_le_card ?_).trans (M.load x)
    intro i mem
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp mem).2 ▸ inside i⟩

/-- The homomorphism comparator on the relabelled pattern evaluates only
single-exponentially many cached rows in all inclusion–exclusion terms. -/
theorem comparator_rows (A : Colored n) (B : Colored m) (H : Colored h) (K c : Nat)
    (source : n≤K) (target : m≤K) (size : h≤K) (M : Model A H c)
    (sep : Outline.Separators (List.range h) (adjacency H) (fun _ => 1)) (fill : Fin m) :
    ∃p : Equiv.Perm (Fin n),
      (∑ Y ∈ (univ : Finset (Fin m)).powerset, BagHom.tableRows fill (List.finRange n)
        (BagHom.constraints (relabel A p) B Y)) ≤ 2^((2+9*(c*28))*(K+1)) := by
  obtain ⟨D⟩:=from_separator H sep
  obtain ⟨T⟩:=contract A H M D
  obtain ⟨p,⟨O⟩⟩:=elimination A T
  refine ⟨p,BagHom.square_root_table_bound _ _ K (c*28) source target
    {O with cap := fun v => (O.cap v).trans ?_} fill⟩
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sqrt_le_sqrt size) _))

end Recognition.MinorWidth
