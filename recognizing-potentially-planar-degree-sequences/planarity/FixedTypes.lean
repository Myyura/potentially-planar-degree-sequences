import Mathlib.Data.List.Sort
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-! Fixed order and fixed number of types. A zero multiplicity marks an
unused slot even if degree zero occurs in the input. -/
namespace Recognition.FixedTypes

def support (ds : List Nat) (n : Nat) :=
  (List.range (n+1)).filter (fun d => ds.contains d)

structure Profile (n j : Nat) where
  degrees : List Nat
  order : degrees.length = n
  bounded : ∀ d ∈ degrees, d ≤ n
  sorted : degrees.Pairwise (· ≥ ·)
  few : (support degrees n).length ≤ j

private def slotList (p : Profile n j) := (support p.degrees n).map
  (fun d => (d,p.degrees.count d))

def code (p : Profile n j) (i : Fin j) : Fin (n+1) × Fin (n+1) :=
  let s := (slotList p)[i.val]?.getD (0,0)
  (Fin.ofNat (n+1) s.1,Fin.ofNat (n+1) s.2)

private theorem slot {p : Profile n j} {i : Fin j} {s : Nat × Nat}
    (entry : (slotList p)[i.val]?=some s) :
    s.1≤n ∧ s.2=p.degrees.count s.1 ∧ 0<s.2 := by
  have mem := List.mem_of_getElem? entry
  obtain ⟨d,hm,rfl⟩ := List.mem_map.mp mem
  have h := List.mem_filter.mp hm
  exact ⟨by have := List.mem_range.mp h.1;omega,rfl,
    List.count_pos_iff.mpr (List.contains_iff_mem.mp h.2)⟩

private theorem code_value (p : Profile n j) (i : Fin j) :
    ((code p i).1.val,(code p i).2.val) = (slotList p)[i.val]?.getD (0,0) := by
  unfold code
  cases h : (slotList p)[i.val]? with
  | none => simp
  | some s =>
    obtain ⟨d,ct,_⟩ := slot h
    have k := List.count_le_length (l:=p.degrees) (a:=s.1)
    have o := p.order
    simp [Nat.mod_eq_of_lt (show s.1<n+1 by omega),Nat.mod_eq_of_lt (show s.2<n+1 by omega)]

private theorem code_covers (p : Profile n j) {d} (mem : d∈p.degrees) :
    ∃ i : Fin j, ((code p i).1.val,(code p i).2.val) = (d,p.degrees.count d) := by
  have h : (d,p.degrees.count d)∈slotList p :=
    List.mem_map.mpr ⟨d,List.mem_filter.mpr ⟨List.mem_range.mpr (by have := p.bounded d mem;omega),
      List.contains_iff_mem.mpr mem⟩,rfl⟩
  obtain ⟨i,b,e⟩ := List.mem_iff_getElem.mp h
  have cap : (slotList p).length ≤ j := by simpa [slotList] using p.few
  refine ⟨⟨i,by omega⟩,?_⟩
  rw [code_value]
  simp [List.getElem?_eq_getElem b,e]

theorem code_injective (n j : Nat) : Function.Injective (@code n j) := by
  intro p q equal
  have transfer (a b : Profile n j) (eq : code a=code b) (d) (mem : d∈a.degrees) :
      b.degrees.count d=a.degrees.count d := by
    obtain ⟨i,hi⟩ := code_covers a mem
    rw [eq,code_value] at hi
    cases h : (slotList b)[i.val]? with
    | none =>
      rw [h] at hi
      have pos := List.count_pos_iff.mpr mem
      exact False.elim (by have := congrArg Prod.snd hi; simp at this;omega)
    | some s =>
      rw [h] at hi
      obtain ⟨_,ct,_⟩ := slot h
      have a := congrArg Prod.fst hi
      have b := congrArg Prod.snd hi
      simp at a b
      rw [← a,← ct,b,a]
  have perm : p.degrees.Perm q.degrees := by
    apply List.perm_iff_count.mpr
    intro d
    by_cases a : d∈p.degrees
    · exact (transfer p q equal d a).symm
    by_cases b : d∈q.degrees
    · exact transfer q p equal.symm d b
    simp [List.count_eq_zero.mpr a,List.count_eq_zero.mpr b]
  have rows := perm.eq_of_pairwise (fun _ _ _ _ h k => Nat.le_antisymm k h) p.sorted q.sorted
  cases p;cases q;congr

theorem finite_profiles (n j : Nat) : Finite (Profile n j) :=
  Finite.of_injective _ (code_injective n j)

theorem count_bound (n j : Nat) : Nat.card (Profile n j) ≤ (n+1)^(2*j) := by
  have b := Nat.card_le_card_of_injective _ (code_injective n j)
  simpa [Nat.card_eq_fintype_card,pow_mul,pow_two] using b

end Recognition.FixedTypes
