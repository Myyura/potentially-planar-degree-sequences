import RecognizingPotentiallyPlanarDegreeSequences.FixedGadget
import RecognizingPotentiallyPlanarDegreeSequences.FixedForward
import RecognizingPotentiallyPlanarDegreeSequences.FixedGraphic

/-! The fixed matching and its resulting degree row have the manuscript's
labels in all three rounds, for both the planar and ordinary constructions. -/

namespace RecognizingPotentiallyPlanarDegreeSequences.FixedLabels
open SparseBoundary SparseBoundary.Graph RecognizingPotentiallyPlanarDegreeSequences.FixedBudget
open Recognition.Reduction (TableValid)

private def pairs (n r N : Nat) (_fit : r ≤ n) (room : n+r ≤ N) : List (Fin N × Fin N) :=
  (List.finRange r).map (fun i => (⟨i.val, by omega⟩, ⟨n+i.val, by omega⟩))

private theorem independent {n r N : Nat} (fit : r ≤ n) (room : n+r ≤ N) :
    ((pairs n r N fit room).flatMap (fun e => [e.1,e.2])).Nodup := by
  rw [pairs, List.flatMap_map, List.nodup_flatMap]
  constructor
  · intro i _
    have ne : (⟨i.val, by omega⟩ : Fin N) ≠ ⟨n+i.val, by omega⟩ := by
      intro eq; have := congrArg Fin.val eq; simp only at this; omega
    simpa [Function.comp_def] using ne
  · apply (List.nodup_finRange r).imp
    intro i j neq x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    have ij : i.val ≠ j.val := fun e => neq (Fin.ext e)
    rcases hx with hx|hx <;> rcases hy with hy|hy <;>
      have e := congrArg Fin.val (hx.symm.trans hy) <;> dsimp at e <;> omega

private theorem inc_count {N : Nat} (es : List (Fin N × Fin N))
    (ds : (es.flatMap (fun e => [e.1,e.2])).Nodup) (v : Fin N) :
    increments es v = (es.flatMap (fun e => [e.1,e.2])).count v := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨a,b⟩ := e
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, not_or] at ds
    have rest := ih ds.2.2
    unfold increments at *
    simp only [List.countP_cons, List.flatMap_cons, List.cons_append, List.nil_append, List.count_cons]
    rw [rest]
    by_cases l : v=a <;> by_cases r : v=b
    all_goals simp_all [pairRow, Bool.beq_eq_decide_eq] <;> grind

private theorem increment {n r N : Nat} (fit : r ≤ n) (room : n+r ≤ N) (i : Fin N) :
    increments (pairs n r N fit room) i = ((marks n r).contains i.val).toNat := by
  rw [inc_count _ (independent fit room)]
  let ends := (pairs n r N fit room).flatMap (fun e => [e.1,e.2])
  have eq : i ∈ ends ↔ i.val ∈ marks n r := by
    rw [marks, List.mem_append, List.mem_range, List.mem_range']
    constructor
    · intro hm
      obtain ⟨e, he, hi⟩ := List.mem_flatMap.mp hm
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with h | h
      · exact Or.inl ((congrArg Fin.val h).symm ▸ j.isLt)
      · exact Or.inr ⟨j.val,j.isLt,by simpa using congrArg Fin.val h⟩
    · intro hm
      have insert (j : Fin r) (match' : i.val=j.val ∨ i.val=n+j.val) : i ∈ ends := by
        apply List.mem_flatMap.mpr
        refine ⟨_, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact match'.imp Fin.ext Fin.ext
      rcases hm with h | ⟨j,hj,eq⟩
      · exact insert ⟨i.val,h⟩ (Or.inl rfl)
      · exact insert ⟨j,hj⟩ (Or.inr (by simpa using eq))
  by_cases mem : i ∈ ends
  · have cnt := List.count_eq_one_of_mem (independent fit room) mem
    rw [List.contains_iff_mem.mpr (eq.mp mem)]
    exact cnt
  · have no : (marks n r).contains i.val=false := Bool.eq_false_iff.mpr
      (fun h => mem (eq.mpr (List.contains_iff_mem.mp h)))
    rw [no]
    exact List.count_eq_zero.mpr mem

private theorem result_row {d : List Nat} {r : Nat} (valid : TableValid d) (fit : r ≤ d.length) :
    let x := full (full d)
    let N := (full x).length
    ∀ (room : d.length+r ≤ N) (G : Graph N), G.Realizes (full x) →
      FixedGadget.result G (pairs d.length r N fit room) =
        oldRow x (marks d.length r) ++ List.replicate (2*x.length-4) 3 := by
  intro x N room G real
  have lenx : d.length+r ≤ x.length := by
    have := valid.1; dsimp [x]; rw [full_length, full_length]; omega
  apply List.ext_getElem
  · simp [FixedGadget.result, oldRow, N, full_length]
  · intro i hi hj
    have il : i < N := by simpa [FixedGadget.result] using hi
    let j : Fin N := ⟨i,il⟩
    have dg := real j
    change G.degree j = (full x)[i] at dg
    simp only [FixedGadget.result,List.getElem_ofFn]
    change G.degree j + 3 * increments _ j = _
    rw [increment, dg]
    by_cases h : i < x.length
    · have old : i < (oldRow x (marks d.length r)).length := by simpa [oldRow] using h
      rw [List.getElem_append_left old]
      have get := oldRow_get x (marks d.length r) h
      rw [List.getElem?_eq_getElem old, List.getElem?_eq_getElem h] at get
      simpa [full, List.getElem_append_left (by simpa using h : i < (x.map (2*·)).length), j] using get.symm
    · have old : (oldRow x (marks d.length r)).length ≤ i := by simp [oldRow]; omega
      have high : (x.map (2*·)).length ≤ i := by simp; omega
      have un : i ∉ marks d.length r := fun mem => by have := marks_bounded fit mem; omega
      simp [full,List.getElem_append_right high,List.getElem_append_right old,j,un]

theorem apply_planar {d : List Nat} {r : Nat} (valid : TableValid d) (fit : r ≤ d.length)
    (plan : Planaric d) : Planaric (core d r ++ List.replicate r 2) := by
  let x := full (full d)
  let N := (full x).length
  obtain ⟨G,real,flat,edges⟩ := FixedForward.planar_matching valid fit plan
  have room : d.length+r ≤ N := by
    have := valid.1; dsimp [N,x]; rw [full_length, full_length, full_length]; omega
  let es := pairs d.length r N fit room
  have yes := FixedGadget.planar_gadgets G es flat (independent fit room) (by
    intro e he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    exact edges _ _ i.isLt rfl)
  rw [result_row valid fit room G real] at yes
  apply (planaric_perm _).mp yes
  apply List.perm_iff_count.mpr
  intro k
  simp only [es,pairs,List.length_map,List.length_finRange,core,List.count_append,List.count_replicate,x]
  split_ifs <;> omega

/-- Nonedges between the very same labels give the ordinary graphic promise. -/
theorem apply_graphic {d : List Nat} {r : Nat} (valid : TableValid d) (fit : r ≤ d.length)
    (G : Graph (full (full (full d))).length) (real : G.Realizes (full (full (full d))))
    (missing : ∀ x y : Fin (full (full (full d))).length, x.val < r →
      y.val = d.length+x.val → G.adj x y = false) : Graphic (core d r) := by
  let x := full (full d)
  let N := (full x).length
  have room : d.length+r ≤ N := by
    have := valid.1; dsimp [N,x]; rw [full_length, full_length, full_length]; omega
  let es := pairs d.length r N fit room
  have yes := FixedGadget.graphic_gadgets G es (independent fit room) (by
    intro e he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    exact missing _ _ i.isLt rfl)
  rw [result_row valid fit room G real] at yes
  apply (graphic_perm _).mp yes
  apply List.perm_iff_count.mpr
  intro k
  simp only [es,pairs,List.length_map,List.length_finRange,core,List.count_append,List.count_replicate,x]
  split_ifs <;> omega

end RecognizingPotentiallyPlanarDegreeSequences.FixedLabels

namespace RecognizingPotentiallyPlanarDegreeSequences.FixedBudget
open SparseBoundary
open Recognition.Reduction (TableValid)

theorem core_graphic {d : List Nat} {r : Nat} (valid : TableValid d)
    (fit : r+3 ≤ d.length) (gr : Graphic d) : Graphic (core d r) := by
  obtain ⟨G, real, miss⟩ := three_full_nonedges valid fit gr
  apply RecognizingPotentiallyPlanarDegreeSequences.FixedLabels.apply_graphic valid (by omega) G real
  intro x y hx eq
  rw [← adjAt_fin,eq]
  exact miss x.val hx

end RecognizingPotentiallyPlanarDegreeSequences.FixedBudget
