import Augmentation
import GraphCounts
import LeanPool.K5MinorFreeChoosability.Wagner.RotRing

/-! At a universal vertex of an Euler-tight simple planar graph, the plane
rotation gives a Hamiltonian cycle on all the other vertices. The list
records the closing edge as an ordinary modular successor as well. -/
namespace Recognition.ConeLink
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Recognition.Wagner
open SparseBoundary

variable {V : Type*} {G : SimpleGraph V}

/-- The link is labelled, without repeated vertices, and has an edge even
between the last and the first entry. -/
def IsRim (G : SimpleGraph V) (apex : V) (rim : List V) : Prop :=
  rim.Nodup ∧ (∀ v, v ∈ rim ↔ v ≠ apex) ∧
    ∀ i : Fin rim.length, G.Adj (rim.get i) (rim.get ⟨(i.val+1) % rim.length, Nat.mod_lt _ (Nat.zero_le i.val |>.trans_lt i.isLt)⟩)

private theorem consecutive_adj (M : PlaneMap G)
    (three : ∀ d, M.facePerm (M.facePerm (M.facePerm d)) = d) (d : G.Dart) :
    G.Adj d.snd (M.rot d).snd := by
  let φ := M.facePerm
  have start (t : G.Dart) : (φ t).fst = t.snd := facePerm_fst M.isRotationSystem t
  have close (t : G.Dart) : (φ (φ t)).snd = t.fst :=
    (start (φ (φ t))).symm.trans (congrArg (fun w : G.Dart => w.fst) (three t))
  have step : φ d.symm = M.rot d := by simp [φ,PlaneMap.facePerm_apply]
  have edge := (φ (φ d.symm)).adj.symm
  rw [close, start, step] at edge
  exact edge

noncomputable def rimRow [Finite V] (M : PlaneMap G) (start : G.Dart) : List V :=
  List.ofFn (fun i : Fin (M.rper start) => (M.rd start i.val).snd)

/-- Listing the rotation orbit at the apex gives an explicit cyclic order
with adjacent consecutive neighbours. -/
theorem rotation_rim [Finite V] (M : PlaneMap G)
    (three : ∀ d, M.facePerm (M.facePerm (M.facePerm d)) = d)
    (apex : V) (universal : ∀ v, v ≠ apex → G.Adj apex v) (start : G.Dart)
    (tail : start.fst = apex) : IsRim G apex (rimRow M start) := by
  classical
  have tails (j : Nat) := (M.rd_fst start j).trans tail
  refine ⟨?_, ?_, ?_⟩
  · apply List.nodup_ofFn.mpr
    intro i j eq
    have eqD : M.rd start i.val = M.rd start j.val :=
      SimpleGraph.Dart.ext _ _ (Prod.ext ((tails i.val).trans (tails j.val).symm) eq)
    apply Fin.ext
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact M.rd_injOn start lt (by omega) eqD
    · exact M.rd_injOn start gt (by omega) eqD.symm
  · intro v
    constructor
    · intro mem
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp mem
      exact fun bad => (M.rd start i.val).adj.ne ((tails _).trans bad.symm)
    · intro diff
      let d : G.Dart := ⟨(apex, v), universal v diff⟩
      obtain ⟨i,hi,eq⟩ := M.exists_rd_eq start (d := d) tail.symm
      exact List.mem_ofFn.mpr ⟨⟨i,hi⟩, congrArg (fun t : G.Dart => t.snd) eq⟩
  · intro i
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simpa [rimRow, M.rd_mod, M.rd_succ] using consecutive_adj M three (M.rd start i.val)

/-- Numbering the rim from zero, disjoint chords cannot alternate. -/
def NonCrossing (G : SimpleGraph V) (rim : List V) : Prop :=
  ∀ a b c d : Fin rim.length, a < b → b < c → c < d →
    G.Adj (rim.get a) (rim.get c) → ¬G.Adj (rim.get b) (rim.get d)

/-- The four disjoint arcs between alternating endpoints and the singleton
apex are explicit connected branch sets. The two chord edges complete K₅. -/
theorem crossing_minor [Fintype V] [DecidableEq V] (M : PlaneMap G) (start : G.Dart)
    (sep : NoSmallSep G Finset.univ) (comp : numComponents M.rot (dartSymm G) ≤ 1)
    {a b c d : Nat} (ab : a<b) (bc : b<c) (cd : c<d) (bound : d<M.rper start)
    (ac : G.Adj (M.rd start a).snd (M.rd start c).snd)
    (bd : G.Adj (M.rd start b).snd (M.rd start d).snd) : Nonempty (CliqueMinorModel G 5) := by
  classical
  let p := M.rper start
  have da : d < a+p := by dsimp [p]; omega
  have two : 2 ≤ M.rper start := by omega
  let R := M.ring start
  have covers (u v : V) (_ : G.Adj u v) : u ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  have noA (i j : Nat) : Disjoint ({start.fst} : Finset V) (R i j) :=
    Finset.disjoint_singleton_left.mpr (M.not_mem_ring_fst start covers sep comp i j)
  have disj {i j k l : Nat} (ord : j≤k) (one : l ≤ i+p) : Disjoint (R i j) (R k l) :=
    M.disjoint_ring start covers sep comp ord one
  have d12 : Disjoint (R a b) (R b c) := disj le_rfl (by omega)
  have d13 : Disjoint (R a b) (R c d) := disj (by omega) (by omega)
  have d14 : Disjoint (R a b) (R d (a+p)) := disj (by omega) le_rfl
  have d23 : Disjoint (R b c) (R c d) := disj le_rfl (by omega)
  have d24 : Disjoint (R b c) (R d (a+p)) := disj (by omega) (by omega)
  have d34 : Disjoint (R c d) (R d (a+p)) := disj le_rfl (by omega)
  have mb := M.snd_mem_ring' start two ab
  have mc := M.snd_mem_ring' start two bc
  have md := M.snd_mem_ring' start two cd
  have ma := M.snd_mem_ring' start two da
  rw [show M.rd start (a+p) = M.rd start a from M.rd_add_rper start a] at ma
  have fromA {i x y : Nat} (inArc : (M.rd start i).snd ∈ R x y) : Touch G {start.fst} (R x y) :=
    ⟨start.fst,Finset.mem_singleton_self _, _, inArc, M.rd_fst start i ▸ (M.rd start i).adj⟩
  have t12 := M.touch_ring start two ab bc
  have t23 := M.touch_ring start two bc cd
  have t34 := M.touch_ring start two cd da
  have t41 : Touch G (R d (a+p)) (R a b) := by
    have t := M.touch_ring start two da (by omega : a+p<b+p)
    rwa [M.ring_add_rper] at t
  have t13 : Touch G (R a b) (R c d) := ⟨_,mb,_,md,bd⟩
  have t42 : Touch G (R d (a+p)) (R b c) := ⟨_,ma,_,mc,ac⟩
  refine ⟨CliqueMinorModel.ofConnSet
    ![{start.fst}, R a b, R b c, R c d, R d (a+p)] (fun i => ?_) (fun i j ij => ?_) (fun i j ij => ?_)⟩
  · fin_cases i
    · exact connSet_finset_singleton _
    · exact M.connSet_ring start two ab
    · exact M.connSet_ring start two bc
    · exact M.connSet_ring start two cd
    · exact M.connSet_ring start two da
  · fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl ij | exact noA _ _ | exact (noA _ _).symm
      | exact d12 | exact d12.symm | exact d13 | exact d13.symm | exact d14 | exact d14.symm
      | exact d23 | exact d23.symm | exact d24 | exact d24.symm | exact d34 | exact d34.symm
  · have t01 := fromA mb
    have t02 := fromA mc
    have t03 := fromA md
    have t04 := fromA ma
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl ij
      | exact t01 | exact t01.symm | exact t02 | exact t02.symm | exact t03 | exact t03.symm
      | exact t04 | exact t04.symm | exact t12 | exact t12.symm | exact t23 | exact t23.symm
      | exact t34 | exact t34.symm | exact t41 | exact t41.symm | exact t13 | exact t13.symm
      | exact t42 | exact t42.symm

/-- Every simple spherical graph of order at least four achieving the
Euler edge bound is already maximal on its vertex set. -/
private theorem maximal_of_tight [Finite V] (apex : V) (plane : IsPlanar G)
    (order : 4 ≤ Nat.card V) (tight : Nat.card G.edgeSet + 6 = 3 * Nat.card V) :
    Maximal IsPlanar G := by
  classical
  let _ := Fintype.ofFinite V
  let _ : Nonempty V := ⟨apex⟩
  obtain ⟨H, sub, maximal⟩ := Recognition.Augment.exists_maximal G plane
  obtain ⟨M⟩ := maximal.1
  have h := (Recognition.Augment.maximal_tight M maximal (Recognition.Augment.maximal_connected maximal) order).2
  have eqcard : G.edgeFinset.card = H.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card, ←Nat.card_eq_fintype_card, ←Nat.card_eq_fintype_card]
    omega
  have eq : G = H := SimpleGraph.edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le (by simpa using sub) eqcard.ge)
  exact eq ▸ maximal

/-- No given embedding, degree condition on the rim, or preselected outer
face is required. The rim has exactly one fewer vertex than the graph. -/
theorem tight_cone_rim [Finite V] (plane : IsPlanar G) (apex : V)
    (order : 4 ≤ Nat.card V) (tight : Nat.card G.edgeSet + 6 = 3 * Nat.card V)
    (universal : ∀ v, v ≠ apex → G.Adj apex v) :
    ∃ rim : List V, IsRim G apex rim ∧ NonCrossing G rim ∧ rim.length + 1 = Nat.card V := by
  classical
  let _ := Fintype.ofFinite V
  let _ : Nonempty V := ⟨apex⟩
  obtain ⟨M⟩ := plane
  have maximal := maximal_of_tight apex ⟨M⟩ order tight
  have low := (Recognition.Augment.maximal_tight M maximal (Recognition.Augment.maximal_connected maximal) order).1
  have two (x : V) := (by decide : 2 ≤ 3) |>.trans (low x)
  obtain ⟨one,tri⟩ := tight_faces M two ⟨apex⟩ tight
  obtain ⟨z⟩ := (Nat.card_pos_iff.mp (by have := low apex; omega : 0 < Nat.card {y // G.Adj apex y})).1
  let start : G.Dart := ⟨(apex,z.val),z.property⟩
  let rim := rimRow M start
  have ok := rotation_rim M tri apex universal start rfl
  have sep := Recognition.Augment.maximal_no_small_sep M maximal (Recognition.Augment.maximal_connected maximal)
  have noncross : NonCrossing G rim := by
    intro a b c d ab bc cd ac bd
    have bound : d.val < M.rper start := by simpa [rim,rimRow] using d.isLt
    rw [List.get_eq_getElem, List.get_eq_getElem] at ac bd
    have x : G.Adj (M.rd start a.val).snd (M.rd start c.val).snd := by
      simpa only [rim,rimRow,List.get_eq_getElem,List.getElem_ofFn] using ac
    have y : G.Adj (M.rd start b.val).snd (M.rd start d.val).snd := by
      simpa only [rim,rimRow,List.get_eq_getElem,List.getElem_ofFn] using bd
    exact (cliqueMinorFree_five_of_isPlanar (G := G) ⟨M⟩)
      (crossing_minor M start sep one.le ab bc cd bound x y)
  refine ⟨rim,ok,noncross,?_⟩
  have rimSet : rim.toFinset = Finset.univ.erase apex := by
    ext x
    simpa only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true] using ok.2.1 x
  have cnt := congrArg Finset.card rimSet
  rw [List.toFinset_card_of_nodup (show rim.Nodup from ok.1), Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ←Nat.card_eq_fintype_card] at cnt
  omega

/-- A labelled realization of a tight degree list whose first vertex is
universal supplies the ordered polygon on the remaining labels. -/
theorem table_cone_rim_with_hub (t : List Nat) (valid : Reduction.TableValid (t.length :: t))
    (yes : Planaric (t.length :: t)) :
    ∃ G : Graph (t.length+1), G.Realizes (t.length :: t) ∧ G.Planar ∧
      (∀ v : Fin (t.length+1), v ≠ 0 → G.adj 0 v = true) ∧
      ∃ rim : List (Fin (t.length+1)), IsRim (toSimple G) 0 rim ∧
        NonCrossing (toSimple G) rim ∧ rim.length = t.length := by
  obtain ⟨G, deg, flat⟩ := yes
  have edges := (order_counts G valid deg).2
  have size : 4 ≤ Nat.card (Fin (t.length+1)) := by
    have len := valid.1
    simp only [List.length_cons] at len
    simpa using (show 4 ≤ t.length+1 by omega)
  have hub : G.degree 0 = t.length := deg 0
  have every : ∀ v : Fin (t.length+1), v ≠ 0 → (toSimple G).Adj 0 v := by
    intro v
    refine Fin.cases (fun ne => (ne rfl).elim) (fun j _ => Graph.root_universal hub j) v
  obtain ⟨rim, ring, noncross, card⟩ := tight_cone_rim ((planar_iff_rotation G).mp flat) 0 size edges every
  exact ⟨G, deg, flat, every, rim, ring, noncross, by simpa using card⟩

/-- The ordered polygon, with its length specialized to the tail of the degree list. -/
theorem table_cone_rim (t : List Nat) (valid : Reduction.TableValid (t.length :: t))
    (yes : Planaric (t.length :: t)) :
    ∃ G : Graph (t.length+1), G.Realizes (t.length :: t) ∧ G.Planar ∧
      ∃ rim : List (Fin (t.length+1)), IsRim (toSimple G) 0 rim ∧
        NonCrossing (toSimple G) rim ∧ rim.length = t.length := by
  obtain ⟨G, deg, flat, _, rim⟩ := table_cone_rim_with_hub t valid yes
  exact ⟨G, deg, flat, rim⟩

end Recognition.ConeLink
