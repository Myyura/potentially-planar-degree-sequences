import DiskFullerene.Construction
import DiskFullerene.FacialIso

namespace DiskFullerene.CanonicalIso
open Dual Construction

/-- The cap and strip construction only has to exhibit its edges in the
input. The spherical edge count proves that these account for every edge. -/
structure Labeling {M} (G : IsDiskFullerene M (n+12)) where
  label : Vertex → Face M
  inject : ∀ a∈vertices n, ∀ b∈vertices n, label a=label b → a=b
  contains : ∀ a∈vertices n, ∀ b∈vertices n, adj n a b=true → label b∈dualRow G (label a)

private theorem sameSet {α} [DecidableEq α] {a b : List α} (na : a.Nodup) (nb : b.Nodup)
    (sub : a⊆b) (sz : a.length=b.length) : a.Perm b := by
  apply (List.perm_ext_iff_of_nodup na nb).mpr
  intro x; refine ⟨fun m=>sub m,?_⟩; intro bx
  by_cases yes : x∈a
  · exact yes
  · have large := (List.nodup_cons.mpr ⟨yes,na⟩).length_le_of_subset (List.cons_subset.mpr ⟨bx,sub⟩)
    simp [sz] at large; omega

private theorem total_canonical (n : Nat) : ((vertices n).map (degree n)).sum=6*n+138 := by
  let K := vertices n
  have all (v) (m : v∈K) : degree n v=n+12 ∨ degree n v=5 ∨ degree n v=6 := by
    cases v with
    | pole => exact Or.inl (degreePole _)
    | cap b u => rw [degreeCap]; split <;> simp
    | spine i =>
      have size : i<n+4 := by simpa [K,vertices] using m
      rw [degreeSpine _ _ size]; split <;> simp
  have step (xs : List Vertex) (valid : xs⊆K) :
      (xs.map (degree n)).sum = (n+12)*xs.countP (fun v => degree n v == n+12)+
          5*xs.countP (fun v => degree n v == 5) + 6*xs.countP (fun v=>degree n v==6) := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      have ⟨ha,ms⟩ := List.cons_subset.mp valid
      have tail := ih ms
      have l : n+12≠5 := by omega
      have r : n+12≠6 := by omega
      rcases all a ha with h|h|h <;>
        simp [h,Nat.mul_add,tail] <;> omega
  have stats := degreeInventory n
  rw [step _ (fun _ m=>m),stats.1,stats.2.1,stats.2.2]; omega

private theorem total_actual {M} (G : IsDiskFullerene M (n+12)) (six : M.hexagons=6) :
    ((List.finRange M.faces.length).map (fun i => (dualRow G i).length)).sum=6*n+138 := by
  have lengths : (List.finRange M.faces.length).map (fun i => (dualRow G i).length) =
      M.faces.map List.length := by
    apply List.ext_getElem
    · simp
    · intro i hi bound; simp [row_length]
  have cov := G.coverage.length_eq
  rw [List.length_flatMap] at cov
  simp only [Dual.sides_size] at cov
  change (M.faces.map List.length).sum=M.darts.length at cov
  have sz := extremalOrder G six
  rw [lengths]
  have darts := cubic_dart_count G.cubic
  omega

theorem Labeling.surjective {M} {G : IsDiskFullerene M (n+12)} (L : Labeling G)
    (six : M.hexagons=6) : ((vertices n).map L.label).Perm (List.finRange M.faces.length) := by
  have size := G.sphere
  rw [cubic_dart_count G.cubic,extremalOrder G six] at size
  apply sameSet (List.pairwise_map.mpr ((vertices_nodup n).imp_of_mem
    (fun ha hb ne he => ne (L.inject _ ha _ hb he)))) (List.nodup_finRange _) (fun _ _ => List.mem_finRange _)
  simp only [List.length_map,vertexCount,List.length_finRange]; omega

private theorem sum_tight {α} (xs : List α) (f g : α→Nat) (le : ∀ v∈xs, f v≤g v) :
    (xs.map f).sum ≤ (xs.map g).sum ∧ ((xs.map f).sum=(xs.map g).sum → ∀ v∈xs, f v=g v) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := le a (by simp)
    have ⟨cl,cs⟩ := ih (fun v hv=>le v (by simp [hv]))
    simp only [List.map_cons,List.sum_cons,List.mem_cons]
    refine ⟨by omega,?_⟩
    intro total v q; rcases q with rfl|tail
    · omega
    · exact cs (by omega) _ tail

theorem Labeling.full_edges {M} {G : IsDiskFullerene M (n+12)}
    (L : Labeling G) (six : M.hexagons=6) (x y : Vertex) (hx : x∈vertices n) (hy : y∈vertices n) :
    adj n x y=true ↔ L.label y∈dualRow G (L.label x) := by
  let K := vertices n
  let neigh := fun x => (K.filter (adj n x)).map L.label
  have unique (x) : (neigh x).Nodup := List.pairwise_map.mpr
    (((vertices_nodup n).filter (adj n x)).imp_of_mem
      (fun ha hb ne eq => ne (L.inject _ (List.mem_filter.mp ha).1 _ (List.mem_filter.mp hb).1 eq)))
  have sub (x) (m : x∈K) : neigh x⊆dualRow G (L.label x) := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
    have ⟨v,e⟩ := List.mem_filter.mp hy
    exact L.contains _ m _ v e
  have length (x) : (neigh x).length=degree n x := by simp [neigh,K,degree,List.countP_eq_length_filter]
  have less (x) (m : x∈K) : degree n x ≤ (dualRow G (L.label x)).length :=
    length x ▸ (unique x).length_le_of_subset (sub x m)
  have perm := (L.surjective six).map (fun i => (dualRow G i).length)
  have sumperm {a b : List Nat} (p : a.Perm b) : a.sum=b.sum := by
    induction p with
    | nil => rfl
    | cons _ _ ih => simp [ih]
    | swap => simp; omega
    | trans _ _ ih ik => exact ih.trans ik
  have total := sumperm perm
  have expected := total_canonical n
  have actual := total_actual G six
  simp only [List.map_map,Function.comp_def] at total
  have equal := (sum_tight K (degree n) (fun x => (dualRow G (L.label x)).length) less).2
    (by dsimp [K]; omega) x hx
  have p := sameSet (unique x) (row_nodup G (noRepeatOnSphere G (by omega)) _) (sub x hx) ((length x).trans equal)
  constructor
  · exact L.contains _ hx _ hy
  · intro yes
    obtain ⟨v,mem,eq⟩ := List.mem_map.mp (p.mem_iff.mpr yes)
    have ⟨vm,edge⟩ := List.mem_filter.mp mem
    exact (L.inject _ vm _ hy eq) ▸ edge

theorem same_graph {M N} {G : IsDiskFullerene M (n+12)} {H : IsDiskFullerene N (n+12)}
    (L : Labeling G) (R : Labeling H) (g6 : M.hexagons=6) (h6 : N.hexagons=6) : GraphIso M N := by
  classical
  have reached {M} {G : IsDiskFullerene M (n+12)} (L : Labeling G) (six : M.hexagons=6) (f : Face M) :
      ∃ x∈vertices n,L.label x=f := List.mem_map.mp ((L.surjective six).mem_iff.mpr (List.mem_finRange _))
  let preL := fun f => (reached L g6 f).choose
  let preR := fun f => (reached R h6 f).choose
  have l (f) : preL f∈vertices n ∧ L.label (preL f)=f := (reached L g6 f).choose_spec
  have r (f) : preR f∈vertices n ∧ R.label (preR f)=f := (reached R h6 f).choose_spec
  apply SkeletonIso.primal (A:=G) (B:=H) (S := {f:=fun f => R.label (preL f),g:=fun f => L.label (preR f),left:=?_,right:=?_,edge:=?_}) (by omega) (by omega)
  · intro x
    rw [R.inject _ (r _).1 _ (l x).1 (r _).2,(l x).2]
  · intro x
    rw [L.inject _ (l _).1 _ (r x).1 (l _).2,(r x).2]
  · intro x y
    have lft := L.full_edges g6 _ _ (l x).1 (l y).1
    have rgt := R.full_edges h6 _ _ (l x).1 (l y).1
    rw [(l x).2,(l y).2] at lft
    exact lft.symm.trans rgt

end DiskFullerene.CanonicalIso
