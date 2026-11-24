import TargetLanguages
import TargetLanguagesStacked

/-! Positive certificates at the external tagged degree-string interface.
Malformed encodings and positive arity are handled before row verification.
The bounded decoder is shared by all three languages. -/
namespace Recognition.TargetLanguages
open SparseBoundary

inductive Class where | maximal | stacked | polyhedral

def Class.row : Class → List Nat → Prop
  | .maximal => MaximalRow
  | .stacked => fun ds => StackedHistory.SequentialRealization ds
  | .polyhedral => PolyhedralRow

def Class.check : Class → List Nat → List Bool → Bool
  | .maximal => checkMaximal
  | .stacked => fun ds w => (StackedCertificate.verify ds w).value
  | .polyhedral => checkPolyhedral

def Class.width (c : Class) (n : Nat) :=
  match c with
  | .stacked => 3*n
  | _ => 5*(n+1)^3

private theorem fits (c : Class) {ds} (yes : c.row ds) : ∀ v∈ds,v≤ds.length := by
  cases c with
  | maximal => exact WireSearch.degrees_fit ((maximal_row_iff _).mp yes).2
  | polyhedral => exact WireSearch.degrees_fit ((polyhedral_row_iff _).mp yes).2.2
  | stacked =>
    obtain ⟨M,h,ns,_,seen,d⟩ := yes
    have reg := SourceBridge.regular h
    intro x mem
    have elem : x∈(ds : Multiset Nat) := mem
    rw [←d] at elem
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp elem
    have verts := (seen v).mpr hv
    have count := (reg.nodup v verts).length_le_of_subset
      (fun {u} present => (seen u).mp (reg.neighbor v u verts present))
    have len : ns.length=ds.length := by simpa using congrArg Multiset.card d
    omega

theorem row_certificate (c : Class) (ds : List Nat) :
    c.row ds ↔ ∃ w : List Bool,w.length≤c.width ds.length ∧ c.check ds w=true := by
  cases c
  · exact maximal_certificate ds
  · exact StackedCertificate.certificate ds
  · exact polyhedral_certificate ds

def wireCheck (c : Class) (input w : List Bool) : Bool :=
  match (WireSearch.decode input).1 with
  | some (x::xs) => decide (w.length≤c.width (x::xs).length) && c.check (x::xs) w
  | _ => false

theorem wire_certificate (c : Class) (input : List Bool) : Wire.degreeLanguage c.row input ↔
    ∃ w : List Bool,w.length≤c.width input.length ∧ wireCheck c input w=true := by
  simp only [wireCheck,(WireSearch.decode_work input).1]
  cases h : WireSearch.parse input with
  | none =>
    simp only [Bool.false_eq_true,and_false,exists_false,iff_false]
    rintro ⟨ds,eq,_,yes⟩
    have := (WireSearch.parse_exact input ds).mpr ⟨eq,fits c yes⟩
    simp [h] at this
  | some ds =>
    have raw := ((WireSearch.parse_exact input ds).mp h).1
    have order := (WireSearch.count_tags input).2.2
    rw [WireSearch.arity_eq _ raw] at order
    cases ds with
    | nil => simp [Wire.degreeLanguage,raw]
    | cons x xs =>
      simp only [Wire.degreeLanguage,raw,Option.some.injEq,exists_eq_left',Bool.and_eq_true,decide_eq_true_eq]
      constructor
      · intro yes
        obtain ⟨w,sz,ok⟩ := (row_certificate c _).mp yes.2
        refine ⟨w,sz.trans ?_,sz,ok⟩
        cases c <;> dsimp [Class.width] <;> gcongr <;> exact order
      · rintro ⟨w,_,ok⟩
        exact ⟨by simp,(row_certificate c _).mpr ⟨w,ok⟩⟩

end Recognition.TargetLanguages
