import Combined.SupportSuppress
import Combined.Budget

/-! Expand the multigraph into a simple planar graph. Additional copies of an
edge give parallel paths, each loop gives a triangle, and unused degree slots
receive leaves. All three operations are on the packed simple graphs. -/

namespace Combined.Support.Multi
open SparseBoundary SparseBoundary.Graph

private def copies : {n : Nat} → (Fin n → Nat) → List (Fin n)
  | 0, _ => []
  | n+1, f => List.replicate (f 0) 0 ++ (copies (fun i : Fin n => f i.succ)).map Fin.succ

private theorem copies_length (f : Fin n → Nat) : (copies f).length = vsum f := by
  induction n with
  | zero => simp [copies]
  | succ n ih => simp [copies, ih, vsum_succ]

private theorem copies_count (f : Fin n → Nat) (i : Fin n) :
    (copies f).count i = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [copies, List.count_eq_zero.mpr (show 0 ∉
        (copies (fun j : Fin n => f j.succ)).map Fin.succ by simp [Fin.succ_ne_zero])]
    · simp [copies, List.count_replicate, Ne.symm (Fin.succ_ne_zero _),
        List.count_map_of_injective _ _ (Fin.succ_injective _), ih]

private def extra (r : Fin n → Nat) (i : Fin n) := r i - present (r i)

private def paths : (M : Multi n) → List (Fin n × Fin n)
  | .nil => []
  | .cons _ r M =>
    (copies (extra r)).map (fun j => (0,j.succ)) ++
      M.paths.map (fun (i,j) => (i.succ,j.succ))

private def petals : (M : Multi n) → Fin n → Nat
  | .nil => Fin.elim0
  | .cons k _ M => Fin.cases k M.petals

private theorem paths_valid (M : Multi n) : ∀ ab ∈ M.paths, M.support.adj ab.1 ab.2 = true := by
  induction M with
  | nil => simp [paths]
  | cons L r M ih =>
    intro ab hab
    rcases List.mem_append.mp hab with ha | hb
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      have cnt := List.count_pos_iff.mpr hj
      rw [copies_count] at cnt
      simp only [extra] at cnt
      simp [support, incident, show 0 < r j by omega]
    · obtain ⟨⟨i,j⟩, hij, rfl⟩ := List.mem_map.mp hb
      simpa [support, incident] using ih (i,j) hij

private theorem paths_cost (M : Multi n) : M.paths.length + 2 * vsum M.petals = M.cost := by
  induction M with
  | nil => rfl
  | cons L r M ih =>
    simp only [paths, List.length_append, List.length_map, copies_length, cost, vsum_succ, petals,
      Fin.cases_zero, Fin.cases_succ]
    change vsum (extra r) + M.paths.length + 2 * (L + vsum M.petals) =
      2*L + vsum (extra r) + M.cost
    omega

private theorem simple_row (r : Fin n → Nat) :
    ((List.finRange n).filter (fun i => decide (0 < r i))).length +
      vsum (extra r) = vsum r := by
  rw [← count_true, ← vsum_add]
  congr 1
  funext i
  cases val : r i <;> simp [extra, val, present, Nat.add_comm]

private theorem zero_succ (x : Fin n) : ((0 : Fin (n+1)) == x.succ) = false := by simp [beq_eq_false_iff_ne, Ne.symm (Fin.succ_ne_zero x)]
private theorem succ_zero (x : Fin n) : (x.succ == 0) = false := by simp [beq_eq_false_iff_ne, Fin.succ_ne_zero x]
private theorem succ_beq (x y : Fin n) : (x.succ == y.succ) = (x == y) := (Fin.succ_injective n).beq_eq

private theorem paths_degree (M : Multi n) (i : Fin n) :
    M.support.degree i + increments M.paths i + 2 * M.petals i = M.degree i := by
  induction M with
  | nil => exact i.elim0
  | cons L r M ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [paths, support, degree_adjoin_zero, increments, List.countP_append, List.countP_map,
        Function.comp_def, pairRow, zero_succ, copies_length, petals, degree]
      have := simple_row r
      omega
    · have cnt := copies_count (extra r) j
      have old := ih j
      simp only [paths, support, degree_adjoin_succ, increments, List.countP_append,
        List.countP_map, petals, degree, Fin.cases_succ] at *
      simp [Function.comp_def, pairRow, succ_zero, succ_beq] at *
      have cnt' : (copies (extra r)).countP (fun x => j == x) = extra r j := by
        simpa only [List.count_eq_countP, Bool.beq_comm (a := j)] using cnt
      rw [cnt']
      have step : (decide (0 < r j)).toNat + extra r j = r j := by
        cases e : r j <;> simp [extra, e, present, Nat.add_comm]
      omega

private theorem attach {a : Nat} {tail : List Nat} (hp : Planaric (a :: tail)) (k : Nat) :
    Planaric ((a+k) :: (List.replicate k 1 ++ tail)) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    obtain ⟨G, real, flat⟩ := ih
    let v : Fin ((a+k)::(List.replicate k 1 ++ tail)).length := 0
    have next : Planaric (1 :: (a+k+1) :: (List.replicate k 1 ++ tail)) := by
      refine ⟨G.withLeaf v, Fin.cases (withLeaf_new_degree ..) (fun i => ?_), withLeaf_planar flat v⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [withLeaf_old_degree]; simpa [v] using (real 0)
      · simpa [withLeaf_old_degree, v, Fin.succ_ne_zero] using real j.succ
    simpa [List.replicate_succ, Nat.add_assoc] using
      (planaric_perm (List.Perm.swap _ _ _)).mp next

private theorem decorate (d loops leaves : Fin n → Nat) (tail : List Nat)
    (hp : Planaric (List.ofFn d ++ tail)) :
    Planaric (List.ofFn (fun i => d i + 2*loops i + leaves i) ++
      List.replicate (2*vsum loops) 2 ++ List.replicate (vsum leaves) 1 ++ tail) := by
  induction n generalizing tail with
  | zero => simpa using hp
  | succ n ih =>
    rw [List.ofFn_succ] at hp
    have head := attach (planaric_petals hp (loops 0)) (leaves 0)
    let D := d 0 + 2*loops 0 + leaves 0
    let T := D :: (List.replicate (leaves 0) 1 ++ List.replicate (2*loops 0) 2 ++ tail)
    have init : Planaric (List.ofFn (fun i : Fin n => d i.succ) ++ T) := by
      apply (planaric_perm _).mp head
      apply List.perm_iff_count.mpr
      intro x
      simp [T, D, List.count_cons, List.count_append]
      omega
    have done := ih (fun i => d i.succ) (fun i => loops i.succ) (fun i => leaves i.succ) T init
    apply (planaric_perm _).mp done
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.ofFn_succ, vsum_succ, Nat.mul_add, List.replicate_add, T, D,
      List.count_cons, List.count_append, List.append_assoc, List.cons_append]
    omega

/-- A concrete simple planar realization at the subdivision cost, with the
prescribed deficit filled by independent pendant vertices. -/
theorem realize {h : List Nat} {ℓ : Nat} (M : Multi h.length) (flat : M.support.Planar)
    (cap : ∀ i : Fin h.length, M.degree i ≤ h[i.val])
    (balance : 2 * M.edges + ℓ = h.sum) : Combined.Budget.Feasible h ℓ M.cost := by
  let d (i : Fin h.length) := M.support.degree i + increments M.paths i
  let v (i : Fin h.length) := h[i.val] - M.degree i
  have hp := expanded_planaric flat M.paths (paths_valid M)
  have init : Planaric (List.ofFn d ++ List.replicate M.paths.length 2) :=
    (planaric_perm List.perm_append_comm).mp hp
  have built := decorate d M.petals v _ init
  have target : (fun i => d i + 2 * M.petals i + v i) = (fun i : Fin h.length => h[i.val]) := by
    funext i
    dsimp [d, v]
    rw [paths_degree]
    have := cap i
    omega
  have deficits : vsum v = ℓ := by
    have eq : (fun i => M.degree i + v i) = fun i : Fin h.length => h[i.val] := by
      funext i; dsimp [v]; have := cap i; omega
    have total := vsum_add M.degree v
    rw [eq, M.handshake] at total
    change (List.ofFn (fun i : Fin h.length => h[i.val])).sum = 2 * M.edges + vsum v at total
    rw [List.ofFn_getElem] at total
    omega
  rw [target, List.ofFn_getElem, deficits] at built
  unfold Combined.Budget.Feasible
  apply (planaric_perm _).mp built
  apply List.perm_iff_count.mpr
  intro x
  rw [← paths_cost M]
  simp only [List.count_append, List.count_replicate]
  split_ifs <;> omega

end Combined.Support.Multi
