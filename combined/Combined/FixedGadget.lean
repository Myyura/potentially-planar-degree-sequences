import Combined.EdgePatch
import Combined.FixedBudget
import SparseBoundary.LeafReduction

/-! Local graphs for the fixed-budget reduction, iterated on disjoint pairs. -/
namespace Combined.FixedGadget

open SparseBoundary SparseBoundary.Graph Combined.EdgePatch

private def up (e : Fin n × Fin n) : Fin (n+1) × Fin (n+1) := (e.1.succ, e.2.succ)

private theorem beq_succ (a b : Fin n) : (a.succ == b.succ) = (a == b) :=
  (Fin.succ_injective n).beq_eq

private theorem inc_succ (es : List (Fin n × Fin n)) (i : Fin n) :
    increments (es.map up) i.succ = increments es i := by
  simp [increments, up, List.countP_map, Function.comp_def, pairRow, beq_succ]

private theorem inc_zero (es : List (Fin n × Fin n)) : increments (es.map up) 0 = 0 := by
  have no (x : Fin n) : (0 == x.succ) = false :=
    beq_eq_false_iff_ne.mpr (Ne.symm (Fin.succ_ne_zero _))
  simp [increments, up, List.countP_map, Function.comp_def, pairRow, no]

private def distinct (es : List (Fin n × Fin n)) := (es.flatMap (fun e => [e.1,e.2])).Nodup

private theorem distinct_up {es : List (Fin n × Fin n)} (h : distinct es) : distinct (es.map up) := by
  have eq : (es.map up).flatMap (fun e => [e.1, e.2]) =
      (es.flatMap (fun e => [e.1, e.2])).map Fin.succ := by
    clear h
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.map_cons,List.flatMap_cons,List.map_append,List.map_cons,List.map_nil,ih]; rfl
  unfold distinct
  rw [eq]
  exact h.map (Fin.succ_injective _)

private theorem endpoints {es : List (Fin n × Fin n)} {a b : Fin n}
    (h : distinct ((a,b) :: es)) :
    a ≠ b ∧ distinct es ∧ ∀ e ∈ es, e.1 ≠ a ∧ e.1 ≠ b := by
  simp only [distinct, List.flatMap_cons, List.cons_append, List.nil_append,
    List.nodup_cons, List.mem_cons, not_or] at h
  refine ⟨h.1.1, h.2.2, fun e he => ⟨?_, ?_⟩⟩ <;> intro bad <;>
    have present : e.1 ∈ es.flatMap (fun e => [e.1, e.2]) := List.mem_flatMap.mpr ⟨e, he, by simp⟩
  · exact h.1.2 (bad ▸ present)
  · exact h.2.1 (bad ▸ present)

private def withPair (G : Graph n) (a b : Fin n) : Graph n := G.editEdge a b true

private theorem pair_adj (G : Graph n) {a b : Fin n} (ne : a ≠ b) (x y : Fin n) :
    (withPair G a b).adj x y =
      (if (x=a ∧ y=b) ∨ (x=b ∧ y=a) then true else G.adj x y) := by
  unfold withPair editEdge
  apply adj_ofRelation
  · intro i j
    change (if _ then true else G.adj i j) = (if _ then true else G.adj j i)
    rw [G.adj_comm i j]
    grind
  · intro i
    change (if _ then true else G.adj i i) = false
    simp; grind

private theorem eq_dec (x y : Fin n) : (x == y) = decide (x=y) := Bool.eq_iff_iff.mpr (by simp)

private theorem pair_degree (G : Graph n) {a b : Fin n} (ne : a ≠ b) (miss : G.adj a b=false)
    (i : Fin n) : (withPair G a b).degree i = G.degree i + (pairRow a b i).toNat := by
  have h := degree_edit ne G true i
  by_cases ha : i = a <;> by_cases hb : i = b <;> simpa [withPair, miss, pairRow, ha, hb, eq_dec] using h

def result (G : Graph n) (es : List (Fin n × Fin n)) :=
  List.ofFn (fun i => G.degree i + 3 * increments es i)

private theorem bump_cons (G : Graph n) (a b : Fin n) (es : List (Fin n × Fin n)) (i : Fin n) :
    G.degree i + 3 * (pairRow a b i).toNat + 3 * increments es i =
      G.degree i + 3 * increments ((a,b)::es) i := by
  cases h : pairRow a b i <;> simp [increments, h]; omega

/-- For existing edges, each pair gains three at each end and introduces two
cubic vertices and one vertex of degree two in a simple planar graph. -/
theorem planar_gadgets (G : Graph n) (es : List (Fin n × Fin n)) (hp : G.Planar)
    (hd : (es.flatMap (fun e => [e.1,e.2])).Nodup)
    (edges : ∀ e ∈ es, G.adj e.1 e.2 = true) :
    Planaric (List.replicate (2*es.length) 3 ++ List.replicate es.length 2 ++ result G es) := by
  have prove (k : Nat) : ∀ {n} (G : Graph n) (es : List (Fin n × Fin n)),
      es.length = k → G.Planar → distinct es → (∀ e ∈ es, G.adj e.1 e.2 = true) →
      Planaric (List.replicate (2*k) 3 ++ List.replicate k 2 ++ result G es) := by
    induction k with
    | zero =>
      intro n G es sz flat _ _
      have : es = [] := List.length_eq_zero_iff.mp sz
      simpa [this, result, increments] using planaric_profile flat
    | succ k ih =>
      intro n G es sz flat ds good
      cases es with
      | nil => simp at sz
      | cons e es =>
        obtain ⟨a,b⟩ := e
        have size : es.length=k := Nat.succ.inj sz
        have edge := good (a,b) (by simp)
        let T := twins G a b true
        let K := T.parallelPath a.succ.succ b.succ.succ
        have old (x y : Fin n) : T.adj x.succ.succ y.succ.succ = G.adj x y := by
          simp [T, twins, parallelPath, incident]
        have shifted : T.adj a.succ.succ b.succ.succ = true := (old a b).trans edge
        have flatK := parallelPath_planar (twins_planar flat edge true) shifted
        let next := (((es.map up).map up).map up)
        have flat' := ih K next (by simp [next,size]) flatK
          (distinct_up (distinct_up (distinct_up (endpoints ds).2.1))) (by
            intro e he
            obtain ⟨z, hz, rfl⟩ := List.mem_map.mp he
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
            simpa [K, up, parallelPath, incident, old] using good v (by simp [hv]))
        have twin := twins_new edge true
        have profile : result K next = 2 :: 3 :: 3 :: result G ((a,b)::es) := by
          simp only [result, List.ofFn_succ, next, inc_zero, inc_succ, Nat.mul_zero, Nat.add_zero]
          congr 1
          · exact parallelPath_new_degree shifted
          congr 1
          · rw [parallelPath_old_degree]
            have zero : ∀ x : Fin (n+1), (0 == x.succ) = false := fun x => beq_eq_false_iff_ne.mpr (Ne.symm (Fin.succ_ne_zero x))
            simpa [T,pairRow,zero] using twin.1
          congr 1
          · rw [parallelPath_old_degree]
            have zero : ∀ x : Fin n, (0 == x.succ) = false := fun x => beq_eq_false_iff_ne.mpr (Ne.symm (Fin.succ_ne_zero x))
            change T.degree (0 : Fin (n+1)).succ + (pairRow a.succ.succ b.succ.succ (0 : Fin (n+1)).succ).toNat = 3
            simp only [pairRow, beq_succ, zero, Bool.or_self, Bool.toNat_false, Nat.add_zero]
            exact twin.2
          apply congrArg List.ofFn
          funext i
          rw [parallelPath_old_degree, twins_old]
          simp only [pairRow, beq_succ]
          have step := bump_cons G a b es i
          unfold pairRow at step
          omega
        rw [profile] at flat'
        apply (planaric_perm _).mp flat'
        apply List.perm_iff_count.mpr
        intro x
        simp [Nat.mul_succ, List.replicate_succ, List.count_cons]
        omega
  exact prove _ G es rfl hp hd edges

/-- For missing pairs the same degree increments are graphic without the twos. -/
theorem graphic_gadgets (G : Graph n) (es : List (Fin n × Fin n))
    (hd : (es.flatMap (fun e => [e.1,e.2])).Nodup)
    (missing : ∀ e ∈ es, G.adj e.1 e.2 = false) :
    Graphic (List.replicate (2*es.length) 3 ++ result G es) := by
  have prove (k : Nat) : ∀ {n} (G : Graph n) (es : List (Fin n × Fin n)),
      es.length = k → distinct es → (∀ e ∈ es, G.adj e.1 e.2 = false) →
      Graphic (List.replicate (2*k) 3 ++ result G es) := by
    induction k with
    | zero =>
      intro n G es sz _ _
      have : es = [] := List.length_eq_zero_iff.mp sz
      have hg : Graphic (List.ofFn G.degree) := by
        have make {ds : List Nat} {m : Nat} (sz : ds.length=m)
            (H : Graph m) (given : ∀ i : Fin m, H.degree i = ds[i.val]'(by omega)) :
            Graphic ds := by
          subst m
          exact ⟨H,given⟩
        exact make List.length_ofFn G (by simp)
      simpa [this, result, increments] using hg
    | succ k ih =>
      intro n G es sz ds miss
      cases es with
      | nil => simp at sz
      | cons e es =>
        obtain ⟨a,b⟩ := e
        have size : es.length=k := Nat.succ.inj sz
        obtain ⟨ne, ind, away⟩ := endpoints ds
        have absent := miss (a,b) (by simp)
        let J := withPair G a b
        have edge : J.adj a b = true := by simp [J, pair_adj _ ne]
        let K := twins J a b true
        let next := (es.map up).map up
        have nextG := ih K next (by simp [next,size]) (distinct_up (distinct_up ind)) (by
          intro e he
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
          have safe := away v hv
          simpa [K,J,up,twins,parallelPath,incident,pair_adj _ ne,safe.1,safe.2] using miss v (by simp [hv]))
        have twin := twins_new edge true
        have profile : result K next = 3 :: 3 :: result G ((a,b)::es) := by
          simp only [result,List.ofFn_succ,next,inc_zero,inc_succ,Nat.mul_zero,Nat.add_zero]
          congr 1
          · exact twin.1
          congr 1
          · exact twin.2
          apply congrArg List.ofFn
          funext i
          rw [twins_old, pair_degree _ ne absent]
          have step := bump_cons G a b es i
          omega
        rw [profile] at nextG
        apply (graphic_perm _).mp nextG
        apply List.perm_iff_count.mpr
        intro x
        simp [Nat.mul_succ,List.replicate_add,List.count_cons]
  exact prove _ G es rfl hd missing

end Combined.FixedGadget
