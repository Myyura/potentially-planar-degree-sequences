import SparseBoundary.GraphCliqueSum
import SparseBoundary.TruncationTags

namespace SparseBoundary.Truncation
open Graph

structure Shape (H : Graph (n+1)) (G : Graph (3+n)) where
  port : Fin 3 → Fin n
  spoke : ∀ s, H.adj 0 (port s).succ=true
  outer : ∀ x y, G.adj (Fin.natAdd 3 x) (Fin.natAdd 3 y)=true → H.adj x.succ y.succ=true
  exit : ∀ s x, G.adj (s.castAdd n) (Fin.natAdd 3 x)=true → x=port s

structure Model (G : Graph m) (R : Fin k → Fin k → Bool) (b : Fin k → List (Fin m)) : Prop where
  con : ∀ i, G.connected (b i)=true
  sep : ∀ i j, i≠j → ∀ x∈b i, x∉b j
  link : ∀ i j, R i j=true → ∃ x∈b i, ∃ y∈b j, G.adj x y=true

theorem model_iff {G : Graph m} {R : Fin k → Fin k → Bool} {b} :
    G.minorTest R b=true ↔ Model G R b := by
  simp only [minorTest,List.all_eq_true,List.mem_finRange,true_implies,Bool.and_eq_true,
    Bool.or_eq_true,beq_iff_eq,Bool.not_eq_true',Bool.eq_false_iff]
  constructor
  · intro h
    refine ⟨fun i => (h i).1,fun i j ne => ?_,fun i j rij => ?_⟩
    · simpa [disjoint,List.all_eq_true] using ((h i).2 j).1.resolve_left ne
    · have hl := ((h i).2 j).2.resolve_left (by simp [rij])
      simpa [links,List.any_eq_true] using hl
  · intro h i
    refine ⟨h.con i, fun j => ⟨?_,?_⟩⟩
    · by_cases eq : i=j
      · exact Or.inl eq
      · exact Or.inr (by simpa [disjoint,List.all_eq_true] using h.sep i j eq)
    · by_cases req : R i j=true
      · exact Or.inr (by simpa [links,List.any_eq_true] using h.link i j req)
      · exact Or.inl req

noncomputable def bagLabel {m k : Nat} (b : Fin k → List (Fin m)) (v : Fin m) : Fin (k+1) :=
  if h : ∃ i, v∈b i then (Classical.choose h).castSucc else Fin.last k

theorem label_iff {G : Graph m} {R} {b : Fin k → List (Fin m)}
    (M : Model G R b) (v : Fin m) (i : Fin k) : (bagLabel b v).val=i.val ↔ v∈b i := by
  unfold bagLabel
  split
  next h =>
    have mem := Classical.choose_spec h
    constructor
    · intro eq; exact (Fin.ext eq : Classical.choose h=i) ▸ mem
    · intro hi
      by_cases e : Classical.choose h=i
      · simp [e]
      · exact False.elim (M.sep _ _ e v mem hi)
  next h => simp only [Fin.val_last]; have less := i.isLt; constructor
            · omega
            · intro hi; exact (h ⟨i,hi⟩).elim

noncomputable def roles {n k : Nat} (b : Fin k → List (Fin (3+n))) : Roles k :=
  fun s => bagLabel b (s.castAdd n)

def anchors {H : Graph (n+1)} {G : Graph (3+n)} (S : Shape H G) (b : Fin k → List (Fin (3+n))) (s : Fin 3) : Bool :=
  decide (∀ i, s.castAdd n∈b i → Fin.natAdd 3 (S.port s)∈b i)

theorem roles_hit {G : Graph (3+n)} {R} {b : Fin k → List (Fin (3+n))}
    (M : Model G R b) (s : Fin 3) (i : Fin k) : hit (roles b) s i ↔ s.castAdd n∈b i :=
  label_iff M _ _

theorem admissible_of_model {H : Graph (n+1)} {G : Graph (3+n)} (S : Shape H G) {R}
    {b : Fin k → List (Fin (3+n))} (M : Model G R b) :
    Admissible R (roles b) (anchors S b) := by
  intro s i owns dirty unique
  have hs := (roles_hit M s i).mp owns
  have absent : Fin.natAdd 3 (S.port s) ∉ b i := by
    intro present
    have all (j : Fin k) (hj : s.castAdd n ∈ b j) : Fin.natAdd 3 (S.port s) ∈ b j := by
      by_cases e : i=j
      · exact e ▸ present
      · exact False.elim (M.sep i j e _ hs hj)
    have present_all : anchors S b s=true := decide_eq_true all
    simp [present_all] at dirty
  have nearby (v : Fin (3+n)) : v∈b i → G.adj (s.castAdd n) v=true → v=s.castAdd n := by
    refine Fin.addCases (fun t hm _ => ?_) (fun u hu edge => ?_) v
    · exact congrArg (Fin.castAdd n) (unique t ((roles_hit M t i).mpr hm))
    · exact False.elim (absent ((S.exit s u edge) ▸ hu))
  have pure (x) (hx : x∈b i) : x=s.castAdd n := by
    have agree : ∀ u∈b i,∀ v∈b i,G.adj u v=true → (u=s.castAdd n ↔ v=s.castAdd n) := by
      intro u hu v hv edge
      constructor
      · rintro rfl; exact nearby v hv edge
      · rintro rfl; exact nearby u hu ((G.adj_comm _ _).trans edge)
    exact ((uniform_bag (M.con i) _ agree _ hs _ hx).mp rfl)
  refine ⟨bagLabel b (Fin.natAdd 3 (S.port s)),?_⟩
  intro j he
  obtain ⟨x,hx,y,hy,hxy⟩ := M.link i j he
  rw [pure x hx] at hxy
  revert hy hxy
  refine Fin.addCases (fun t hy _ => Or.inl ⟨t,(roles_hit M t j).mpr hy⟩)
    (fun u hy hsu => ?_) y
  exact Or.inr ((label_iff M _ _).mpr ((S.exit s u hsu) ▸ hy))

end SparseBoundary.Truncation
