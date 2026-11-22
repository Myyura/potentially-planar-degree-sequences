import OrbitTable
import PackedMinor
import Certificate

/-! A finite polynomial-size graph and rotation certificate. Components are
computed by materialized relabelling tables for each permutation generator. -/
namespace Recognition.RotationVerifier
open SparseBoundary LeanPool.K5MinorFreeChoosability Recognition.Wagner Recognition.OrbitTable
open Equiv Equiv.Perm

private def pairs (G : Graph n) := ((List.finRange n).product (List.finRange n)).filter
  (fun p => G.adj p.1 p.2)

private def dartOf (G : Graph n) (p : {p // p ∈ pairs G}) : (toSimple G).Dart :=
  ⟨p.val,(List.mem_filter.mp p.property).2⟩

def darts (G : Graph n) := (pairs G).attach.map (dartOf G)

private theorem all_darts (G : Graph n) (d : (toSimple G).Dart) : d ∈ darts G := by
  have h : d.toProd ∈ pairs G := List.mem_filter.mpr ⟨List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩,d.adj⟩
  exact List.mem_map.mpr ⟨⟨_,h⟩,List.mem_attach ..,rfl⟩

private theorem unique_darts (G : Graph n) : (darts G).Nodup := by
  have h : (pairs G).Nodup := List.filter_sublist.nodup ((List.nodup_finRange n).product (List.nodup_finRange n))
  apply h.attach.map
  intro x y equ
  exact Subtype.ext (congrArg SimpleGraph.Dart.toProd equ)

theorem dart_count (G : Graph n) : (darts G).length ≤ n*n := by
  simp only [darts,List.length_map,List.length_attach]
  unfold pairs
  calc
    _ ≤ ((List.finRange n).product (List.finRange n)).length := List.length_filter_le ..
    _ = _ := (List.length_product (List.finRange n) (List.finRange n)).trans (by simp)

private theorem dart_card (G : Graph n) : (darts G).length = Nat.card (toSimple G).Dart := by
  classical
  have h : (darts G).toFinset = Finset.univ := Finset.eq_univ_of_forall (fun d => List.mem_toFinset.mpr (all_darts G d))
  rw [← List.toFinset_card_of_nodup (unique_darts G),h,Finset.card_univ,Nat.card_eq_fintype_card]

private def arcs (xs : List D) (f : D → D) := xs.map (fun x => (x,f x))
private def orbit [DecidableEq D] (xs : List D) (f : D → D) := run xs (arcs xs f)

private theorem cycle_rel [DecidableEq D] (xs : List D) (full : ∀ x, x ∈ xs) (f : Perm D) (x y) :
    key (orbit xs f) x = key (orbit xs f) y ↔ SameCycle f x y := by
  apply generated xs full _ (SameCycle.setoid f)
  · intro e he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    exact sameCycle_apply_right.mpr (SameCycle.refl _ _)
  · intro s h
    exact fun _ _ => sameCycle_of_step s (fun a => h (a,f a) (List.mem_map.mpr ⟨a,full a,rfl⟩))

private theorem cycle_count [DecidableEq D] (xs : List D) (full : ∀ x, x ∈ xs) (f : Perm D) :
    count (orbit xs f) = cycleCount f :=
  count_correct full _ (SameCycle.setoid f) (cycle_rel xs full f)

private theorem joint_count [DecidableEq D] (xs : List D) (full : ∀ x, x ∈ xs) (f g : Perm D) :
    count (run xs (arcs xs f ++ arcs xs g)) = numComponents f g := by
  apply count_correct full _ (compSetoid f g)
  apply generated xs full
  · intro p hp
    rcases List.mem_append.mp hp with hf|hg
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hf
      exact compSetoid_left f g x
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp hg
      exact compSetoid_right f g x
  · intro s h
    exact fun _ _ => compSetoid_le s
      (fun x => h _ (List.mem_append_left _ (List.mem_map.mpr ⟨x,full x,rfl⟩)))
      (fun x => h _ (List.mem_append_right _ (List.mem_map.mpr ⟨x,full x,rfl⟩)))

/-- Each of the two tables has at most one row per dart in a canonical
certificate. A row is a pair of darts, hence four vertex names. -/
structure Code (G : Graph n) where
  forward : Rows (toSimple G).Dart
  backward : Rows (toSimple G).Dart

def checkRotation (G : Graph n) (C : Code G) : Bool :=
  let ds := darts G
  let f := key C.forward
  let g := key C.backward
  let rev := SimpleGraph.Dart.symm (G := toSimple G)
  let R := orbit ds f
  let comp := run ds (arcs ds f ++ arcs ds rev)
  (C.forward.length ≤ ds.length && C.backward.length ≤ ds.length) &&
  ds.all (fun x => g (f x) == x && f (g x) == x && (f x).fst == x.fst &&
    ds.all (fun y => x.fst != y.fst || key R x == key R y)) &&
  decide (ds.length+2*count comp = count R + count (orbit ds rev) + count (orbit ds (f ∘ rev)))

private theorem check_spec (G : Graph n) (C : Code G) :
    checkRotation G C ↔
      (C.forward.length ≤ (darts G).length ∧ C.backward.length ≤ (darts G).length) ∧
      (∀ x, key C.backward (key C.forward x) = x ∧ key C.forward (key C.backward x) = x ∧
        (key C.forward x).fst = x.fst ∧ ∀ y : (toSimple G).Dart, x.fst = y.fst →
          key (orbit (darts G) (key C.forward)) x = key (orbit (darts G) (key C.forward)) y) ∧
      let xs := darts G
      let f := key C.forward
      let rev := SimpleGraph.Dart.symm (G := toSimple G)
      xs.length + 2*count (run xs (arcs xs f ++ arcs xs rev)) =
        count (orbit xs f) + count (orbit xs rev) + count (orbit xs (f ∘ rev)) := by
  simp only [checkRotation,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,all_darts,true_implies,
    beq_iff_eq,Bool.or_eq_true,bne_iff_ne]
  grind

private theorem euler {G : Graph n} (f : Perm (toSimple G).Dart) :
    let xs := darts G
    let rev := SimpleGraph.Dart.symm (G := toSimple G)
    (xs.length + 2*count (run xs (arcs xs f ++ arcs xs rev)) =
      count (orbit xs f) + count (orbit xs rev) + count (orbit xs (f ∘ rev))) ↔
      eulerDefect f (dartSymm (toSimple G)) = 0 := by
  dsimp only
  let α := dartSymm (toSimple G)
  change (_+2*count (run _ (arcs _ f ++ arcs _ α)) = count (orbit _ f)+count (orbit _ α)+count (orbit _ (f*α))) ↔ _
  rw [joint_count _ (all_darts G),cycle_count _ (all_darts G),cycle_count _ (all_darts G),cycle_count _ (all_darts G),dart_card]
  unfold eulerDefect
  dsimp only [α] at *
  omega

theorem accepted_iff (G : Graph n) : (∃ C : Code G, checkRotation G C) ↔ G.Planar := by
  classical
  rw [planar_iff_rotation]
  constructor
  · rintro ⟨C,yes⟩
    obtain ⟨_,keys,eq⟩ := (check_spec G C).mp yes
    let f : Perm (toSimple G).Dart := ⟨key C.forward,key C.backward,(fun x => (keys x).1),
      fun x => (keys x).2.1⟩
    exact ⟨⟨f,⟨fun x => (keys x).2.2.1,fun x y h => (cycle_rel _ (all_darts G) f x y).mp ((keys x).2.2.2 y h)⟩,
      (euler f).mp eq⟩⟩
  · rintro ⟨M⟩
    let xs := darts G
    let C : Code G := ⟨tabulate xs M.rot,tabulate xs M.rot.symm⟩
    have ff : key C.forward = M.rot := funext (fun x => get_entry xs M.rot (all_darts G x))
    have gg : key C.backward = M.rot.symm := funext (fun x => get_entry xs M.rot.symm (all_darts G x))
    refine ⟨C,(check_spec G C).mpr ?_⟩
    rw [ff,gg]
    refine ⟨by simp [C,xs,tabulate],?_,(euler M.rot).mpr M.eulerDefect_eq_zero⟩
    exact fun x => ⟨M.rot.symm_apply_apply x,M.rot.apply_symm_apply x,M.isRotationSystem.fst_apply x,
      fun y h => (cycle_rel xs (all_darts G) M.rot x y).mpr (M.isRotationSystem.sameCycle x y h)⟩

/-- The graph bits and two bounded tables give an ordinary positive
certificate for the input, including graphs with isolated vertices. -/
theorem planaric_certificate (d : List Nat) :
    (∃ (G : Graph d.length) (C : Code G), G.Realizes d ∧ checkRotation G C) ↔ Planaric d := by
  constructor
  · rintro ⟨G,C,h,ok⟩; exact ⟨G,h,(accepted_iff G).mp ⟨C,ok⟩⟩
  · rintro ⟨G,h,p⟩; obtain ⟨C,c⟩ := (accepted_iff G).mpr p; exact ⟨G,C,h,c⟩
end Recognition.RotationVerifier

namespace Recognition.RotationVerifier
open SparseBoundary Recognition.Wagner Recognition.OrbitTable

/-- Two dense successor/inverse tables. Each cell contains a target pair of
labels. The checker tests both targets before using them as darts. -/
structure Raw (n : Nat) where
  graph : Graph n
  next : Vector (Fin n × Fin n) (n*n)
  prev : Vector (Fin n × Fin n) (n*n)

private def cell {G : Graph n} (d : (toSimple G).Dart) : Fin (n*n) :=
  ⟨d.fst.val*n+d.snd.val,by
    have a := d.snd.isLt
    calc
      _ < (d.fst.val+1)*n := by rw [Nat.succ_mul]; omega
      _ ≤ n*n := Nat.mul_le_mul_right n d.fst.isLt⟩

private def table (G : Graph n) (a : Vector (Fin n × Fin n) (n*n)) :
    Option (Rows (toSimple G).Dart) := (darts G).mapM fun d =>
  let p := a[(cell d).val]
  if h : G.adj p.1 p.2 = true then some (d,⟨p,h⟩) else none

def verify (d : List Nat) (C : Raw d.length) : Bool :=
  match table C.graph C.next,table C.graph C.prev with
  | some f,some g => (List.finRange d.length).all (fun i => C.graph.degree i == d[i]) &&
      checkRotation C.graph ⟨f,g⟩
  | _,_ => false

private theorem cell_inj {G : Graph n} {a b : (toSimple G).Dart} (eq : cell a = cell b) : a=b := by
  have e := congrArg Fin.val eq
  change a.fst.val*n+a.snd.val = b.fst.val*n+b.snd.val at e
  have a0 := a.snd.isLt
  have b0 := b.snd.isLt
  have non : n ≠ 0 := by omega
  have first : a.fst.val = b.fst.val := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lo | hi
    · have h := Nat.mul_le_mul_right n lo
      rw [Nat.succ_mul] at h; omega
    · have h := Nat.mul_le_mul_right n hi
      rw [Nat.succ_mul] at h; omega
  rw [first] at e
  exact SimpleGraph.Dart.ext _ _ (Prod.ext (Fin.ext first) (Fin.ext (by omega)))

private noncomputable def rawTable {G : Graph n} (f : (toSimple G).Dart → (toSimple G).Dart) :
    Vector (Fin n × Fin n) (n*n) := by
  classical
  exact Vector.ofFn fun i =>
    if h : ∃ d : (toSimple G).Dart, cell d = i then (f h.choose).toProd
    else (⟨0,Nat.pos_of_ne_zero (by rintro rfl; exact Fin.elim0 i)⟩,⟨0,Nat.pos_of_ne_zero (by rintro rfl; exact Fin.elim0 i)⟩)

private theorem decode_table {G : Graph n} (f : (toSimple G).Dart → (toSimple G).Dart) :
    table G (rawTable f) = some (tabulate (darts G) f) := by
  classical
  have entry (d : (toSimple G).Dart) : (rawTable f)[(cell d).val]=(f d).toProd := by
    have h : ∃ a : (toSimple G).Dart, cell a=cell d := ⟨d,rfl⟩
    simp [rawTable,h,cell_inj h.choose_spec]
  let read (d : (toSimple G).Dart) : Option ((toSimple G).Dart × (toSimple G).Dart) :=
    let p := (rawTable f)[(cell d).val]
    if h : G.adj p.1 p.2 = true then some (d,⟨p,h⟩) else none
  have each (d : (toSimple G).Dart) : read d = some (d,f d) := by
    have yes : G.adj (f d).fst (f d).snd = true := (f d).adj
    simp only [read,entry d]
    rw [dite_eq_left yes]
  change (darts G).mapM read = _
  induction darts G with
  | nil => rfl
  | cons x xs ih => rw [List.mapM_cons,each]; simp [ih,tabulate]

theorem verify_iff (d : List Nat) : (∃ C : Raw d.length, verify d C) ↔ Planaric d := by
  constructor
  · rintro ⟨C,h⟩
    unfold verify at h
    split at h
    · obtain ⟨degrees,rot⟩ := Bool.and_eq_true_iff.mp h
      exact ⟨C.graph,fun i => beq_iff_eq.mp (List.all_eq_true.mp degrees i (List.mem_finRange i)),
        (accepted_iff _).mp ⟨_,rot⟩⟩
    · contradiction
  · rintro ⟨G,h,planar⟩
    obtain ⟨M⟩ := (planar_iff_rotation G).mp planar
    refine ⟨⟨G,rawTable M.rot,rawTable M.rot.symm⟩,?_⟩
    simp only [verify,decode_table,Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr (fun i _ => beq_iff_eq.mpr (h i)),(check_spec ..).mpr ?_⟩
    have en (f : (toSimple G).Dart → (toSimple G).Dart) :
        key (tabulate (darts G) f)=f := funext (fun i => get_entry (darts G) f (all_darts G i))
    dsimp only
    rw [en,en]
    refine ⟨by simp [tabulate],?_,(euler M.rot).mpr M.eulerDefect_eq_zero⟩
    exact fun x => ⟨M.rot.symm_apply_apply x,M.rot.apply_symm_apply x,M.isRotationSystem.fst_apply x,
        fun y eq => (cycle_rel _ (all_darts G) M.rot x y).mpr (M.isRotationSystem.sameCycle x y eq)⟩

/-- The graph bits and the four vertex words per dense cell are all of the
certificate fields. The arithmetic bound includes order zero. -/
def rawWidth (n : Nat) := SparseBoundary.pairCount n + 4*(n*n)*(n.log2+1)

theorem raw_width_bound (n : Nat) : rawWidth n ≤ 5*(n+1)^3 := by
  have pairs := Recognition.Certificate.certificate_width n
  have log := Nat.log2_le_self n
  unfold rawWidth
  calc
    _ ≤ n*n+4*(n*n)*(n+1) := Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
    _ ≤ 5*(n+1)^3 := by nlinarith

end Recognition.RotationVerifier
