import HardnessReductions.Numbers.Partition3
import Wire
import EmbeddingBridge

/-! Indexed blocks of size three and occurrence-labelled bin assignments. -/
namespace Recognition.SATBridge
open Reduction SparseBoundary

private def fiber {n m : Nat} (f : Fin n → Fin m) (r : Fin m) :=
  Finset.univ.filter fun i => f i = r

private theorem fiber_data {n m : Nat} (f : Fin n → Fin m) (w : Fin n → Nat) (r : Fin m) :
    let row := binWeights (List.ofFn fun i => (f i,w i)) r
    row.length = (fiber f r).card ∧ row.sum = (fiber f r).sum w := by
  classical
  let ids := (List.finRange n).filter fun i => f i == r
  have nd : ids.Nodup := List.filter_sublist.nodup (List.nodup_finRange n)
  have seteq : ids.toFinset = fiber f r := by
    ext i
    simp [ids,fiber]
  change (binWeights _ r).length = _ ∧ (binWeights _ r).sum = _
  unfold binWeights
  rw [List.ofFn_eq_map,List.filter_map,List.map_map,←seteq]
  change (ids.map w).length = ids.toFinset.card ∧ (ids.map w).sum = ids.toFinset.sum w
  rw [List.length_map,List.toFinset_card_of_nodup nd,List.sum_toFinset _ nd]
  exact ⟨rfl,rfl⟩

private theorem indexed_assignment (I : Instance) :
    ThreePartition I ↔ ∃ f : Fin I.weights.length → Fin I.bins,
      ∀r, (fiber f r).card = 3 ∧ (fiber f r).sum (fun i => I.weights[i]) = I.capacity := by
  constructor
  · rintro ⟨d,eq,bins⟩
    have len : d.length = I.weights.length := by simpa using congrArg List.length eq
    let f (i : Fin I.weights.length) := d[i.val]'(by omega) |>.1
    have canon : (List.ofFn fun i => (f i,I.weights[i])) = d := by
      apply List.ext_getElem
      · simp [len]
      · intro k hk hd
        simp only [List.getElem_ofFn]
        apply Prod.ext
        · rfl
        · simp only
          have h : I.weights[k]'(by omega) = (d.map Prod.snd)[k]'(by simp [hd]) :=
            by congr 1; exact eq.symm
          exact h.trans (List.getElem_map ..)
    refine ⟨f,fun r => ?_⟩
    have a := fiber_data f (fun i => I.weights[i]) r
    rw [canon] at a
    exact ⟨a.1.symm.trans (bins r).2,a.2.symm.trans (bins r).1⟩
  · rintro ⟨f,good⟩
    refine ⟨List.ofFn (fun i => (f i,I.weights[i])), ?_,fun r => ?_⟩
    · rw [List.map_ofFn]; exact List.ofFn_getElem
    · have h := fiber_data f (fun i => I.weights[i]) r
      exact ⟨h.2.trans (good r).2,h.1.trans (good r).1⟩

/-- The upstream empty instance has the empty partition for every target. -/
def importPartition (x : Hardness.NumberTargetInstance) : Instance :=
  if x.nums.isEmpty then ⟨[1,1,1],1,3⟩ else ⟨x.nums,x.nums.length / 3,x.target⟩

private theorem empty_yes (x : Hardness.NumberTargetInstance) (e : x.nums = []) :
    Hardness.ThreePartitionWindow x ∧ Hardness.THREE_PARTITION x := by
  cases x with
  | mk xs t =>
    change xs = [] at e
    subst xs
    refine ⟨by simp [Hardness.ThreePartitionWindow], ∅, ?_⟩
    constructor <;> simp

private theorem one_yes : Valid ⟨[1,1,1],1,3⟩ ∧ ThreePartition ⟨[1,1,1],1,3⟩ := by
  constructor
  · decide
  · refine ⟨[(0,1),(0,1),(0,1)],rfl,?_⟩
    decide

/-- Both input formats recognize exactly the same windowed 3-PARTITION instances. -/
theorem partition_input_iff (x : Hardness.NumberTargetInstance) :
    (Hardness.ThreePartitionWindow x ∧ Hardness.THREE_PARTITION x) ↔
    Valid (importPartition x) ∧ ThreePartition (importPartition x) := by
  classical
  by_cases emp : x.nums = []
  · rw [importPartition,show x.nums.isEmpty = true by simp [emp]]
    exact iff_of_true (empty_yes x emp) one_yes
  simp only [importPartition,List.isEmpty_iff,emp,ite_false]
  let m := x.nums.length / 3
  let I : Instance := ⟨x.nums,m,x.target⟩
  change _ ↔ Valid I ∧ ThreePartition I
  constructor
  · rintro ⟨⟨range,total⟩,parts,good⟩
    have count := good.card_univ
    change Fintype.card (Fin x.nums.length) = parts.card * 3 at count
    rw [Fintype.card_fin] at count
    have mc : parts.card = m := by dsimp [m]; omega
    have len : x.nums.length = 3*m := by omega
    refine ⟨⟨by have := List.length_pos_iff.mpr emp; dsimp [I]; omega, len, ?_,range⟩, ?_⟩
    · change x.nums.sum = m*x.target
      rw [len,Nat.mul_assoc] at total
      omega
    · apply (indexed_assignment I).mpr
      let pick (i : Fin x.nums.length) : parts := ⟨(good.exists_mem i).choose,(good.exists_mem i).choose_spec.1⟩
      let num : parts ≃ Fin m := Fintype.equivFinOfCardEq (by simp [mc])
      let f (i : Fin x.nums.length) := num (pick i)
      refine ⟨f,fun r => ?_⟩
      have eq : fiber f r = (num.symm r).val := by
        ext i
        simp only [fiber,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hit
          have pe : pick i = num.symm r := num.eq_symm_apply.mpr hit
          rw [←pe]; exact (good.exists_mem i).choose_spec.2
        · intro hit
          have pe : pick i = num.symm r := Subtype.ext (good.eq_of_mem (pick i).property
            (num.symm r).property (good.exists_mem i).choose_spec.2 hit)
          exact num.eq_symm_apply.mp pe
      rw [eq]
      exact good.2 _ (num.symm r).property
  · rintro ⟨v,alloc⟩
    have len := v.2.1
    have sm := v.2.2.1
    change x.nums.length = 3*m at len
    change x.nums.sum=m*x.target at sm
    refine ⟨⟨v.2.2.2,by rw [len,sm,Nat.mul_assoc]⟩,?_⟩
    obtain ⟨f,good⟩ := (indexed_assignment I).mp alloc
    refine ⟨_,Hardness.isSizedPartition_image (fiber f) (fun i => x.nums[i]) 3 x.target ?_
      (fun r => (good r).1) (fun r => (good r).2)⟩
    intro i
    exact ⟨f i,by simp [fiber], fun j hj => (by simpa [fiber] using hj : f i = j).symm⟩

end Recognition.SATBridge
