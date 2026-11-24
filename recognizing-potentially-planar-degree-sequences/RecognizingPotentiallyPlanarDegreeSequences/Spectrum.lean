import RecognizingPotentiallyPlanarDegreeSequences.SpectrumConstruct
import RecognizingPotentiallyPlanarDegreeSequences.SpectrumGraphic
import BoundaryEG
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

/-! Three marked vertices give the lower bound on the subdivision budgets.
The proof uses the same forbidden-minor definition of planarity as the sparse companion. -/
namespace RecognizingPotentiallyPlanarDegreeSequences.Spectrum

open SparseBoundary Finset
open scoped BigOperators

private theorem not_three_common {n : ℕ} {G : Graph n} (plane : G.Planar)
    (l r : Fin 3 ↪ Fin n) (cross : ∀ i j, G.adj (l i) (r j) = true) : False := by
  have apart (i j) : l i ≠ r j := by
    intro h
    have := cross i j
    rw [h, Graph.adj_self] at this
    contradiction
  let f (i : Fin 6) : Fin n :=
    if h : i.val<3 then l ⟨i.val,h⟩ else r ⟨i.val-3,by omega⟩
  have inj : Function.Injective f := by
    intro i j eq
    unfold f at eq
    split at eq <;> split at eq
    · exact Fin.ext (congrArg (fun z : Fin 3 => z.val) (l.injective eq))
    · exact False.elim (apart _ _ eq)
    · exact False.elim (apart _ _ eq.symm)
    · have h := congrArg Fin.val (r.injective eq)
      apply Fin.ext
      dsimp at h
      omega
  have edges (i j : Fin 6) (h : Graph.biclique33 i j = true) : G.adj (f i) (f j) = true := by
    by_cases hi : i.val < 3 <;> by_cases hj : j.val < 3
    · simp [Graph.biclique33,hi,hj] at h
    · simp [f,hi,hj,cross]
    · simp [f,hi,hj]
      rw [G.adj_comm]
      exact cross _ _
    · simp [Graph.biclique33,hi,hj] at h
  apply plane.2
  refine ⟨fun i => [f i], ?_⟩
  simp only [Graph.minorTest, List.all_eq_true, List.mem_finRange, true_implies,
    Graph.connected, Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', Bool.eq_false_iff]
  intro i j
  constructor
  · by_cases e : i=j
    · exact .inl e
    · exact .inr (by simp [Graph.disjoint, inj.ne e])
  · by_cases e : Graph.biclique33 i j=true
    · exact .inr (by simpa [Graph.links] using edges i j e)
    · exact .inl e

private theorem degree_sum {n : ℕ} (G : Graph n) (u : Fin n) :
    G.degree u = ∑ v, if G.adj u v = true then 1 else 0 := by
  rw [← Finset.card_filter]
  unfold Graph.degree
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _),
    List.toFinset_filter, List.toFinset_finRange]

/-- Any three distinct vertices in a planar simple graph have degree sum at most
twice its order plus two. All but at most two vertices see at most two poles. -/
theorem three_pole_bound {n : ℕ} {G : Graph n} (plane : G.Planar) (poles : Fin 3 ↪ Fin n) :
    G.degree (poles 0) + G.degree (poles 1) + G.degree (poles 2) ≤ 2*n+2 := by
  classical
  let good (v : Fin n) : Prop := ∀ i, G.adj (poles i) v = true
  let common := Finset.univ.filter good
  have few : common.card ≤ 2 := by
    by_contra! large
    have size : Fintype.card (Fin 3) ≤ Fintype.card (↥common) := by simp; omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le size
    let r : Fin 3 ↪ Fin n := e.trans ⟨Subtype.val, Subtype.val_injective⟩
    exact not_three_common plane poles r (fun i j => (Finset.mem_filter.mp (e j).property).2 i)
  have aux (v : Fin n) :
      ((if G.adj (poles 0) v=true then 1 else 0) +
        (if G.adj (poles 1) v=true then 1 else 0) +
        (if G.adj (poles 2) v=true then 1 else 0) : ℕ) ≤ 2+(if good v then 1 else 0) := by
    have iff : good v ↔ G.adj (poles 0) v=true ∧ G.adj (poles 1) v=true ∧ G.adj (poles 2) v=true := by
      exact ⟨fun h => ⟨h 0,h 1,h 2⟩, fun ⟨h0,h1,h2⟩ i => by
        fin_cases i <;> assumption⟩
    simp only [iff]
    by_cases ha : G.adj (poles 0) v=true <;> by_cases hb : G.adj (poles 1) v=true <;> by_cases hc : G.adj (poles 2) v=true <;> simp [ha,hb,hc]
  have bound := Finset.sum_le_sum (N:=ℕ) (s:=Finset.univ) (fun v _ => aux v)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_boole] at bound
  simp only [degree_sum, Finset.sum_boole]
  change _ ≤ 2*n+2
  rw [← Finset.card_filter] at bound
  dsimp [common] at few
  norm_cast at bound ⊢
  have eq : #{i : Fin n | good i} = (Finset.univ.filter good).card := by rfl
  omega

/-- Parameters k and m count subsequent stackings and the degree-two budget. -/
def core (k m : ℕ) : List ℕ :=
  (k+2*m+3) :: (k+2*m+3) :: (2*m+3) ::
    (List.replicate k 4 ++ List.replicate (2*m+1) 3)

def symmetric (p : ℕ) : List ℕ :=
  (p-1) :: (p-1) :: (p-1) :: List.replicate (p-3) 3

private theorem list_bound {a b c : ℕ} {tail : List ℕ}
    (plane : Planaric (a::b::c::tail)) : a+b+c ≤ 2*(tail.length+3)+2 := by
  obtain ⟨G, real, flat⟩ := plane
  let e : Fin 3 ↪ Fin (a::b::c::tail).length :=
    ⟨fun i => ⟨i.val, by simp; omega⟩,fun i j h => Fin.ext (congrArg (fun x : Fin (a::b::c::tail).length => x.val) h)⟩
  have bound := three_pole_bound flat e
  rw [real,real,real] at bound
  change a+b+c ≤ 2*(tail.length+3)+2 at bound
  exact bound

theorem spectrum_lower {k m t : ℕ} (plane : Planaric (core k m ++ List.replicate t 2)) : m ≤ t := by
  have b := list_bound plane
  simp at b
  omega

theorem symmetric_lower {p t : ℕ} (size : 8 ≤ p)
    (plane : Planaric (symmetric p ++ List.replicate t 2)) : p ≤ 2*t+5 := by
  have b := list_bound plane
  simp at b
  omega

private theorem feasible_zero_iff (h : List ℕ) (t : ℕ) :
    Budget.Feasible h 0 t ↔ Planaric (h ++ List.replicate t 2) := by
  simpa only [Budget.Feasible,List.replicate_zero,List.append_nil] using
    (planaric_perm (List.perm_append_comm (l₁:=List.replicate t 2) (l₂:=h)))

theorem spectrum_minimum (k m : ℕ) : Budget.IsMinimum (core k m) 0 m := by
  refine ⟨(feasible_zero_iff ..).mpr ?_,fun t ht => spectrum_lower ((feasible_zero_iff ..).mp ht)⟩
  simpa only [core,List.cons_append,List.append_assoc] using spectrum_expanded k m

/-- Proposition 3.5 at the stipulated order, with ordinary graphicness, positivity,
Euler's maximal sum and the genuine minimum all asserted for the same list. -/
theorem fixed_order_spectrum {p m : ℕ} (hp : 4≤p) (hm : m≤(p-4)/2) :
    let h := core (p-(2*m+4)) m
    h.length=p ∧ (∀ x∈h, 3≤x) ∧ h.sum+12=6*p ∧ Graphic h ∧ Budget.IsMinimum h 0 m := by
  let k := p-(2*m+4)
  have order : p=k+2*m+4 := by dsimp [k];omega
  refine ⟨?_,?_,?_,spectrum_graphic k m,spectrum_minimum k m⟩
  · simp [core];omega
  · intro x hx
    simp only [core,List.mem_cons,List.mem_append,List.mem_replicate] at hx
    rcases hx with h|h|h|⟨_,h⟩|⟨_,h⟩ <;> omega
  · simp [core];omega

/-- For the symmetric lists (p-4)/2 is integer division, equal to the ceiling
of (p-5)/2 in the usual real-valued notation. -/
theorem symmetric_minimum (p : ℕ) (hp : 8≤p) :
    Graphic (symmetric p) ∧ Budget.IsMinimum (symmetric p) 0 ((p-4)/2) := by
  let m := (p-4)/2
  have cases : p=2*m+4 ∨ p=2*m+5 := by dsimp [m];omega
  have graphic := symmetric_graphic (p-3)
  have g : Graphic (symmetric p) := by
    simpa only [symmetric,show p-3+2=p-1 by omega] using graphic
  refine ⟨g,(feasible_zero_iff ..).mpr ?_,?_⟩
  · change Planaric (symmetric p ++ List.replicate m 2)
    rcases cases with e|e
    · have s := spectrum_expanded 0 m
      simp only [symmetric,e,show 2*m+4-1=2*m+3 by omega,show 2*m+4-3=2*m+1 by omega,
        List.cons_append]
      simpa only [Nat.zero_add,List.replicate_zero,List.nil_append] using s
    · have s := odd_symmetric_expanded m (by dsimp [m];omega)
      simpa only [symmetric,e,show 2*m+5-1=2*m+4 by omega,show 2*m+5-3=2*m+2 by omega,
        List.cons_append] using s
  · intro t ht
    have h := symmetric_lower hp ((feasible_zero_iff ..).mp ht)
    omega

end RecognizingPotentiallyPlanarDegreeSequences.Spectrum
