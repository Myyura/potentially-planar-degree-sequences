import ElementaryCoverage
import ElementaryCompare
import MainResult

/-! The elementary algorithm filters the finite catalogue by an executable
width test, then uses homomorphism tables rather than a general-purpose
graph-isomorphism algorithm. It returns the red graph on the input labels. -/
namespace Recognition.ElementaryRun
open SparseBoundary QuotientDP ElementaryCoverage

def catalogue (ds : List Nat) :=
  (ShortBoundary.catalogue ds).filter (ElementaryCompare.allowed (budget ds.length) (width ds.length))

theorem catalogue_length (ds : List Nat) : (catalogue ds).length≤(ShortBoundary.catalogue ds).length :=
  List.length_filter_le ..

def find : (ds : List Nat) → Option (Graph ds.length)
  | [] => Certificate.findRealization []
  | x::ds =>
    let n := ds.length+1
    if 6*n < (x::ds).sum then none
    else if n<4 then Certificate.findRealization (x::ds)
    else WitnessTable.realize (ElementaryCompare.compareWith (width n)) (catalogue (x::ds)) (x::ds) (2*n-5)

theorem find_sound (ds : List Nat) (G : Graph ds.length) (hit : find ds=some G) : G.Planar ∧ G.Realizes ds := by
  cases ds with
  | nil => exact (Certificate.findRealization_sound hit).symm
  | cons x ds =>
    simp only [find] at hit
    split at hit <;> rename_i cut
    · contradiction
    · split at hit <;> rename_i small
      · exact (Certificate.findRealization_sound hit).symm
      · exact WitnessTable.realize_sound _ _ _ _ _ (by omega) hit

theorem find_iff (sep : SeparatorInput.WeightedPlanarSeparator) (ds : List Nat) :
    (find ds).isSome ↔ Planaric ds := by
  constructor
  · intro h;obtain ⟨G,hit⟩:=Option.isSome_iff_exists.mp h
    obtain ⟨planar,deg⟩:=find_sound ds G hit
    exact ⟨G,deg,planar⟩
  · intro yes
    cases ds with
    | nil => exact (Certificate.findRealization_iff []).mpr yes
    | cons x ds =>
      have sumBound := MainResult.volume yes
      change (x::ds).sum≤6*(ds.length+1) at sumBound
      simp only [find,ite_eq_right (Nat.not_lt.mpr sumBound)]
      split
      · exact (Certificate.findRealization_iff _).mpr yes
      · rename_i large
        obtain ⟨f,r,valid⟩ := (Augment.face_certificate_iff x ds (by omega)).mp yes
        obtain ⟨_,count,_,C,degrees,_⟩ := TraceCheck.verify_sound _ r valid
        let n := ds.length+1
        obtain ⟨s,path,done⟩ := ElementaryCoverage.path x ds C count degrees sep
          (ElementaryCompare.allowed (budget n) (width n)) (ElementaryCompare.allowed_of_hierarchy (budget n) (width n))
        obtain ⟨G,hit,_,_⟩ := WitnessTable.realize_of_path (ElementaryCompare.compareWith (width n))
          (ElementaryCompare.compareWith_correct _) (catalogue (x::ds)) (x::ds) f s count path done
        have fEq : 2*(ds.length+1)-5=f := by omega
        rw [fEq,hit];rfl

theorem catalogue_branch (ds : List Nat) (x t : State ds.length) (entry : t∈catalogue ds) :
    ∃xs, LayoutSearch.ordered (ElementaryCompare.pattern t) (width ds.length)=some xs ∧
      ElementaryCompare.compareWith (width ds.length) x t=ElementaryCompare.compareOrder x t xs :=
  ElementaryCompare.allowed_branch x t (List.mem_filter.mp entry).2

end Recognition.ElementaryRun

