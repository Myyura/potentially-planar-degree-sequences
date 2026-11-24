import SparseBoundary.GraphEnumeration
import SparseBoundary.TruncationData
import SparseBoundary.BranchDegree

/-! A specification of the graph certificate, and an independent (exhaustive)
decision and search procedure for arbitrary input lists.  The fast frontier
algorithm needs the additional structural arguments in the manuscript. -/
namespace Recognition.Certificate
open SparseBoundary SparseBoundary.Graph

/-- The graph itself is given by one bit per unordered pair. -/
theorem certificate_width (n : Nat) : 2 * pairCount n + n = n*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairCount, Nat.succ_mul, Nat.mul_succ, Nat.mul_add] at *
    omega

def checkWith (planar : {n : Nat} → Graph n → Bool) (d : List Nat)
    (bits : BitVec (pairCount d.length)) : Bool :=
  let g : Graph d.length := ⟨bits⟩
  (List.finRange d.length).all (fun i => g.degree i == d[i]) && planar g

theorem graph_certificate {test : {n : Nat} → Graph n → Bool}
    (correct : ∀ {n} (G : Graph n), test G = true ↔ G.Planar) (d : List Nat) :
    (∃ bits, checkWith (@test) d bits = true) ↔ Planaric d := by
  constructor
  · rintro ⟨bits,h⟩
    obtain ⟨degrees,hp⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨⟨bits⟩, fun v => beq_iff_eq.mp (List.all_eq_true.mp degrees v (List.mem_finRange v)),
      (correct _).mp hp⟩
  · rintro ⟨⟨bits⟩,h,hp⟩
    exact ⟨bits,Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr
      (fun v _ => beq_iff_eq.mpr (h v)),(correct _).mpr hp⟩⟩

/-- Keep the last occurrence so that a connected construction order survives. -/
private def clean {α} [DecidableEq α] : List α → List α
  | [] => []
  | x::xs => if x ∈ xs then clean xs else x::clean xs

@[simp] private theorem clean_mem {α} [DecidableEq α] (x : α) (s : List α) :
    x ∈ clean s ↔ x ∈ s := by
  induction s with
  | nil => simp [clean]
  | cons y ys ih => by_cases h : y ∈ ys <;> simp [clean, h, ih] <;> grind

private theorem clean_nodup {α} [DecidableEq α] (s : List α) : (clean s).Nodup := by
  induction s with
  | nil => simp [clean]
  | cons x xs ih => by_cases h : x ∈ xs <;> simp [clean,h,ih]

private theorem clean_connected (G : Graph n) (s : List (Fin n)) (h : G.connected s) :
    G.connected (clean s) := by
  match s with
  | [] => contradiction
  | [x] => simp [clean, connected]
  | x::y::ys =>
    obtain ⟨he,hc⟩ := Bool.and_eq_true_iff.mp h
    have ih := clean_connected G (y::ys) hc
    rw [clean]
    split
    · exact ih
    · obtain ⟨v,hv,e⟩ := List.any_eq_true.mp he
      have mem := (clean_mem v (y::ys)).2 hv
      cases t : clean (y::ys) with
      | nil => simp [t] at mem
      | cons z zs =>
        rw [t] at ih mem
        exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨v,mem,e⟩,ih⟩

/-- All words of length at most b on the n vertex names. -/
private def bags (n : Nat) : Nat → List (List (Fin n))
  | 0 => [[]]
  | b+1 => [] :: (List.finRange n).flatMap (fun x => (bags n b).map (List.cons x))

private theorem mem_bags (s : List (Fin n)) (b : Nat) (h : s.length ≤ b) :
    s ∈ bags n b := by
  induction b generalizing s with
  | zero => have : s = [] := List.length_eq_zero_iff.mp (by omega); simp [this,bags]
  | succ b ih =>
    cases s with
    | nil => simp [bags]
    | cons x xs =>
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      exact ⟨x,List.mem_finRange _,List.mem_map.mpr ⟨xs,ih _ (by simpa using h),rfl⟩⟩

/-- Existential search over k independent choices without building a list of
all k-tuples. -/
private def anyTuple {α} (choices : List α) : (k : Nat) → ((Fin k → α) → Bool) → Bool
  | 0, p => p Fin.elim0
  | k+1, p => choices.any fun x => anyTuple choices k (fun f => p (Fin.cases x f))

private theorem tuple_iff (choices : List α) (k : Nat) (p : (Fin k → α) → Bool) :
    anyTuple choices k p = true ↔ ∃ f, (∀ i, f i ∈ choices) ∧ p f = true := by
  induction k with
  | zero =>
    constructor
    · exact fun h => ⟨_,fun i => i.elim0,h⟩
    · rintro ⟨f,_,h⟩
      have : f = Fin.elim0 := funext (fun i => i.elim0)
      simpa [anyTuple,this] using h
  | succ k ih =>
    simp only [anyTuple,List.any_eq_true,ih]
    constructor
    · rintro ⟨x,hx,f,hf,h⟩
      exact ⟨_,Fin.cases hx hf,h⟩
    · rintro ⟨f,hf,h⟩
      refine ⟨f 0,hf 0,fun i => f i.succ,fun i => hf i.succ,?_⟩
      have e : Fin.cases (f 0) (fun i => f i.succ) = f := funext (Fin.cases rfl (fun _ => rfl))
      rwa [e]

def hasMinor (G : Graph n) (R : Fin k → Fin k → Bool) : Bool :=
  anyTuple ((bags n n).filter G.connected) k (G.minorTest R)

theorem hasMinor_iff (G : Graph n) (R : Fin k → Fin k → Bool) :
    hasMinor G R = true ↔ ∃ f, G.minorTest R f = true := by
  rw [hasMinor,tuple_iff]
  constructor
  · rintro ⟨f,_,h⟩; exact ⟨f,h⟩
  · rintro ⟨f,hf⟩
    have m := Truncation.model_iff.mp hf
    refine ⟨fun i => clean (f i),fun i => List.mem_filter.mpr ⟨?_,clean_connected _ _ (m.con i)⟩,?_⟩
    · apply mem_bags
      have bound := (clean_nodup (f i)).length_le_of_subset
        (show clean (f i) ⊆ List.finRange n from fun _ _ => List.mem_finRange _)
      simpa using bound
    · apply Truncation.model_iff.mpr
      refine ⟨fun i => clean_connected _ _ (m.con i),?_,?_⟩
      · simpa only [clean_mem] using m.sep
      · simpa only [clean_mem] using m.link

def testPlanar (G : Graph n) : Bool :=
  if n ≤ 4 then true else !hasMinor G clique5 && !hasMinor G biclique33

theorem testPlanar_iff (G : Graph n) : testPlanar G = true ↔ G.Planar := by
  unfold testPlanar
  split
  · rename_i h
    have few := List.length_filter_le (fun (v : Fin n) => decide (3≤G.degree v)) (List.finRange n)
    exact iff_of_true rfl (planar_of_few_high G (by simpa using Nat.le_trans few (by simpa using h)))
  · change ((!hasMinor G clique5 && !hasMinor G biclique33) = true) ↔ _
    rw [Bool.and_eq_true_iff, Bool.not_eq_true', Bool.not_eq_true']
    rw [Bool.eq_false_iff, Bool.eq_false_iff]
    exact and_congr (not_congr (hasMinor_iff G clique5)) (not_congr (hasMinor_iff G biclique33))

def findRealization (d : List Nat) : Option (Graph d.length) :=
  (candidates d.length (fun i => d[i])).find? (fun G => checkWith (@testPlanar) d G.bits)

theorem findRealization_sound {d : List Nat} {G : Graph d.length}
    (h : findRealization d = some G) : G.Realizes d ∧ G.Planar := by
  have check := List.find?_some h
  obtain ⟨row,hp⟩ := Bool.and_eq_true_iff.mp check
  exact ⟨fun v => beq_iff_eq.mp (List.all_eq_true.mp row v (List.mem_finRange v)),(testPlanar_iff G).mp hp⟩

theorem findRealization_iff (d : List Nat) : (findRealization d).isSome ↔ Planaric d := by
  rw [findRealization,List.find?_isSome]
  constructor
  · rintro ⟨G,_,h⟩
    exact (graph_certificate (@testPlanar_iff) d).1 ⟨G.bits,h⟩
  · rintro ⟨G,hd,hp⟩
    refine ⟨G,candidates_complete G _ hd,Bool.and_eq_true_iff.mpr ⟨?_,(testPlanar_iff _).2 hp⟩⟩
    exact List.all_eq_true.mpr (fun v _ => beq_iff_eq.mpr (hd v))

end Recognition.Certificate
