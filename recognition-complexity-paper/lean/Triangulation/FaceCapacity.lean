import Std

namespace Recognition.FaceCapacity

private def tagged (o : Fin n → Fin 7) (k : Nat) : List (Fin n) :=
  (List.finRange n).filter fun j => (o j).val == k

private def realCodes (o : Fin n → Fin 7) : List (List (Fin n)) :=
  ((List.finRange n).filter fun j => 3 ≤ (o j).val).map fun j => [j]

private def pairCodes (o : Fin 3 → Fin 7) : List (List (Fin 3)) :=
  realCodes o ++ (tagged o 1).flatMap fun a => (tagged o 2).map fun b => [a,b]

private def tripleCodes (o : Fin 4 → Fin 7) : List (List (Fin 4)) :=
  realCodes o ++ (tagged o 0).flatMap fun a =>
    (tagged o 1).flatMap fun b => (tagged o 2).map fun c => [a,b,c]

private theorem tagged_mem {o : Fin n → Fin 7} (h : (o j).val = k) :
    j ∈ tagged o k := by simp [tagged, h, List.mem_finRange]

private theorem real_mem {o : Fin n → Fin 7} (h : 3 ≤ (o j).val) :
    [j] ∈ realCodes o := by
  apply List.mem_map.mpr
  exact ⟨j, List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using h⟩, rfl⟩

private theorem no_injection {α : Type} (L : List α) (f : Fin 3 → α)
    (mem : ∀i, f i ∈ L) (inj : ∀i j, f i = f j → i = j) (short : L.length ≤ 2) : False := by
  have ab : f 0 ≠ f 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (inj _ _ h)
  have ac : f 0 ≠ f 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (inj _ _ h)
  have bc : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (inj _ _ h)
  have m0 := mem 0
  have m1 := mem 1
  have m2 := mem 2
  match L with
  | [] | [_] | [_,_] => simp_all [List.mem_cons] <;> grind
  | _ :: _ :: _ :: _ => simp at short

private theorem slots_bound (L : List (Fin n)) (o : Fin n → Fin 7) :
    (L.filter (fun j => 3 ≤ (o j).val)).length +
    (L.filter (fun j => (o j).val == 0)).length +
    (L.filter (fun j => (o j).val == 1)).length +
    (L.filter (fun j => (o j).val == 2)).length ≤ L.length := by
  induction L with
  | nil => simp
  | cons j L ih =>
    simp only [List.filter_cons, List.length_cons]
    split <;> split <;> split <;> split <;> simp_all <;> omega

private theorem rectangle (L : List α) (f : α → List β) (k : Nat) (h : ∀a, (f a).length = k) :
    (L.flatMap f).length = L.length * k := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, h, Nat.add_mul, Nat.add_comm]

private theorem count_slots (o : Fin n → Fin 7) :
    (realCodes o).length + (tagged o 0).length + (tagged o 1).length + (tagged o 2).length ≤ n := by
  simpa [realCodes, tagged] using slots_bound (List.finRange n) o

private theorem pair_bound (o : Fin 3 → Fin 7) (u : tagged o 1 ≠ []) (v : tagged o 2 ≠ []) :
    (pairCodes o).length ≤ 2 := by
  have count := count_slots o
  have u' := List.length_pos_iff.mpr u
  have v' := List.length_pos_iff.mpr v
  unfold pairCodes
  rw [List.length_append, rectangle _ _ (tagged o 2).length (by simp)]
  rcases (show (tagged o 1).length = 1 ∨ (tagged o 2).length = 1 by omega) with h | h <;>
    simp [h] <;> omega

private theorem triple_bound (o : Fin 4 → Fin 7) (u : tagged o 0 ≠ [])
    (v : tagged o 1 ≠ []) (w : tagged o 2 ≠ []) : (tripleCodes o).length ≤ 2 := by
  have count := count_slots o
  have u' := List.length_pos_iff.mpr u
  have v' := List.length_pos_iff.mpr v
  have w' := List.length_pos_iff.mpr w
  unfold tripleCodes
  rw [List.length_append, rectangle _ _ ((tagged o 1).length * (tagged o 2).length)
    (by intro a; apply rectangle; simp)]
  rcases (show ((tagged o 0).length = 1 ∧ (tagged o 1).length = 1) ∨
      ((tagged o 0).length = 1 ∧ (tagged o 2).length = 1) ∨
      ((tagged o 1).length = 1 ∧ (tagged o 2).length = 1) by omega) with
    ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ <;> simp [a,b] <;> omega

private theorem assemble {n : Nat} (o : Fin n → Fin 7) (virtual : Fin 3 → Bool)
    (real : ∀r, virtual r = false → ∃j, (o j).val = 3+r.val)
    (code : Fin 3 → List (Fin n)) (full : List (List (Fin n)))
    (rmem : ∀j, 3 ≤ (o j).val → [j] ∈ full)
    (vmem : ∀r, virtual r = true → code r ∈ full)
    (many : ∀r j, code r ≠ [j])
    (inj : ∀r s, virtual r=true → virtual s=true → code r = code s → r=s)
    (short : full.length ≤ 2) : False := by
  classical
  let f (r : Fin 3) := if h : virtual r = false then [(real r h).choose] else code r
  apply no_injection full f _ _ short
  · intro r
    dsimp [f]
    split
    next h => exact rmem _ (by have := (real r h).choose_spec; omega)
    next h => exact vmem r (by cases hv : virtual r <;> simp_all)
  · intro r s h
    dsimp [f] at h
    split at h <;> rename_i hr <;> split at h <;> rename_i hs
    · simp only [List.cons.injEq, and_true] at h
      have a := (real r hr).choose_spec
      have b := (real s hs).choose_spec
      rw [h] at a
      exact Fin.ext (by omega)
    · exact False.elim (many s _ h.symm)
    · exact False.elim (many r _ h)
    · exact inj r s (by cases hv : virtual r <;> simp_all) (by cases hv : virtual s <;> simp_all) h

/-- Three slots on a triangle cannot carry three right vertices if an ordered 1–2 pair is used. -/
theorem no_three (o : Fin 3 → Fin 7) (virtual : Fin 3 → Bool)
    (real : ∀r, virtual r = false → ∃j, (o j).val = 3+r.val)
    (has : ∃r, virtual r = true) (p q : Fin 3 → Fin 3)
    (tags : ∀r, virtual r=true → (o (p r)).val=1 ∧ (o (q r)).val=2)
    (inj : ∀r s, virtual r=true → virtual s=true → p r=p s → q r=q s → r=s) : False := by
  obtain ⟨r,hr⟩ := has
  have hu := tagged_mem (tags r hr).1
  have hv := tagged_mem (tags r hr).2
  apply assemble o virtual real (fun s => [p s,q s]) (pairCodes o)
  · intro j hj; exact List.mem_append_left _ (real_mem hj)
  · intro s hs
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨_, tagged_mem (tags s hs).1, List.mem_map.mpr ⟨_, tagged_mem (tags s hs).2, rfl⟩⟩)
  · simp
  · intro s t hs ht he; exact inj s t hs ht (List.cons.inj he).1 (List.cons.inj (List.cons.inj he).2).1
  · apply pair_bound
    · intro e; simp [e] at hu
    · intro e; simp [e] at hv

/-- Four tetrahedral slots carrying all three left tags cannot also carry three distinct right codes. -/
theorem no_tetra (o : Fin 4 → Fin 7) (virtual : Fin 3 → Bool)
    (real : ∀r, virtual r = false → ∃j, (o j).val = 3+r.val)
    (left : ∀l : Fin 3, ∃j,(o j).val=l.val) (p q t : Fin 3 → Fin 4)
    (tags : ∀r, virtual r=true → (o (p r)).val=0 ∧ (o (q r)).val=1 ∧ (o (t r)).val=2)
    (inj : ∀r s, virtual r=true → virtual s=true → p r=p s → q r=q s → t r=t s → r=s) : False := by
  apply assemble o virtual real (fun s => [p s,q s,t s]) (tripleCodes o)
  · intro j hj; exact List.mem_append_left _ (real_mem hj)
  · intro s hs
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨_, tagged_mem (tags s hs).1, List.mem_flatMap.mpr
        ⟨_, tagged_mem (tags s hs).2.1, List.mem_map.mpr ⟨_, tagged_mem (tags s hs).2.2, rfl⟩⟩⟩)
  · simp
  · intro s z hs hz he
    simp only [List.cons.injEq, and_true] at he
    exact inj s z hs hz he.1 he.2.1 he.2.2
  · have nonempty (k : Fin 3) : tagged o k.val ≠ [] := by
      obtain ⟨j,hj⟩ := left k
      have m := tagged_mem hj
      intro e; simp [e] at m
    exact triple_bound o (nonempty 0) (nonempty 1) (nonempty 2)

end Recognition.FaceCapacity
