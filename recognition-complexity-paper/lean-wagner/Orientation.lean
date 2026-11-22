import Topology
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A characteristic-two closed triangulation admits coherent face orientations.
The dual tree propagates signs, and its complement is a primal tree. A signed
boundary supported on a tree and having zero divergence is identically zero. -/
namespace Recognition.Orientation
open PlanarDegrees.Topology
open scoped BigOperators

private abbrev unit (z : ℤ) := z=1 ∨ z= -1
private theorem mul_unit {a b : ℤ} (ha : unit a) (hb : unit b) : unit (a*b) := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> decide
private theorem neg_unit {a : ℤ} (h : unit a) : unit (-a) := by rcases h with rfl|rfl <;> decide

private def vertex (a x : Fin n) : ℤ := if a=x then 1 else 0
private def delta (p : Fin n × Fin n) (x : Fin n) : ℤ := vertex p.1 x - vertex p.2 x
private def direction (p : Fin n × Fin n) (a b : Fin n) : ℤ := if p=(a,b) then 1 else -1
private theorem dir_unit (p : Fin n × Fin n) (a b : Fin n) : unit (direction p a b) := by
  unfold direction; split <;> decide
private theorem dir_times {ends : Fin e → Fin n × Fin n} {a b : Fin n} {d : Fin e}
    (h : Across ends d a b) (x : Fin n) :
    direction (ends d) a b * delta (ends d) x = vertex a x - vertex b x := by
  rcases h with h|h
  · simp [direction,delta,h]
  · rw [h]; by_cases he : (b,a)=(a,b)
    · have := (Prod.mk.inj he).1; subst b; simp [delta]
    · simp [direction,delta,he]

def coefficient (G : Gluing v f e) (i : Fin (f+1)) (d : Fin e) : ℤ :=
  let t := G.tri i
  (if t.ab=d then direction (G.primal d) t.a t.b else 0) +
  (if t.bc=d then direction (G.primal d) t.b t.c else 0) +
  (if t.ca=d then direction (G.primal d) t.c t.a else 0)

private theorem coeff_zero (G : Gluing v f e) (i : Fin (f+1)) (d : Fin e)
    (h : ¬incident G.dual d i) : coefficient G i d = 0 := by
  have H := mt (G.faceSide i d).mpr h
  simp only [Triangle.sides,List.mem_cons,List.not_mem_nil,or_false,not_or] at H
  simp [coefficient,Ne.symm H.1,Ne.symm H.2.1,Ne.symm H.2.2]

private theorem coeff_unit (G : Gluing v f e) (i : Fin (f+1)) (d : Fin e)
    (h : incident G.dual d i) : unit (coefficient G i d) := by
  have H := (G.faceSide i d).mp h
  have nd := G.sidesDistinct i
  simp only [Triangle.sides,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd
  simp only [Triangle.sides,List.mem_cons,List.not_mem_nil,or_false] at H
  rcases H with rfl|rfl|rfl <;>
    simp [coefficient,nd.1.1,nd.1.2,nd.2.1,Ne.symm nd.1.1,Ne.symm nd.1.2,Ne.symm nd.2.1,dir_unit]

private theorem face_balance (G : Gluing v f e) (i : Fin (f+1)) (x : Fin (v+1)) :
    ∑ d, coefficient G i d * delta (G.primal d) x = 0 := by
  simp only [coefficient,add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [dir_times (G.abEnds i),dir_times (G.bcEnds i),dir_times (G.caEnds i)]
  ring

private noncomputable def parent {ends : E → Fin (k+1) × Fin (k+1)} {keep : E → Prop}
    (T : Tree ends keep) (i : Fin k) := (T.choice i).2.choose

private theorem parent_spec {ends : E → Fin (k+1) × Fin (k+1)} {keep : E → Prop}
    (T : Tree ends keep) (i : Fin k) : Across ends (T.pick i) i.succ (parent T i) ∧
      T.height (parent T i) < T.height i.succ := (T.choice i).2.choose_spec

private noncomputable def propagate {ends : E → Fin (k+1) × Fin (k+1)} {keep : E → Prop}
    (T : Tree ends keep) (twist : Fin k → ℤ) (z : Fin (k+1)) : ℤ :=
  match z with
  | ⟨0,_⟩ => 1
  | ⟨i+1,h⟩ => twist ⟨i,by omega⟩ * propagate T twist (parent T ⟨i,by omega⟩)
termination_by T.height z
decreasing_by apply (parent_spec T _).2

private theorem prop_unit {ends : E → Fin (k+1) × Fin (k+1)} {keep : E → Prop}
    (T : Tree ends keep) (twist : Fin k → ℤ) (h : ∀ i, unit (twist i)) (z : Fin (k+1)) :
    unit (propagate T twist z) := by
  cases z with
  | mk j hj =>
    cases j with
    | zero => rw [propagate]; exact Or.inl rfl
    | succ i => unfold propagate; exact mul_unit (h _) (prop_unit T twist h _)
termination_by T.height z
decreasing_by subst_vars; apply (parent_spec T _).2

private def flux (G : Gluing v f e) (s : Fin (f+1) → ℤ) (d : Fin e) : ℤ :=
  ∑ i, s i * coefficient G i d

private theorem flux_pair (G : Gluing v f e) (s : Fin (f+1) → ℤ) (d : Fin e) :
    flux G s d = s (G.dual d).1 * coefficient G (G.dual d).1 d +
      s (G.dual d).2 * coefficient G (G.dual d).2 d := by
  classical
  let a := (G.dual d).1
  let b := (G.dual d).2
  have pair : ∀ i, s i * coefficient G i d =
      (if a=i then s a * coefficient G a d else 0) +
      (if b=i then s b * coefficient G b d else 0) := by
    intro i
    have ne : a≠b := G.twoFaces d
    by_cases h : a=i
    · subst i; simp [ne.symm]
    · by_cases h' : b=i
      · subst i; simp [ne]
      · simp [h,h',coeff_zero G i d (show ¬incident G.dual d i from not_or.mpr ⟨h,h'⟩)]
  unfold flux
  rw [Finset.sum_congr rfl (fun i _ => pair i)]
  simp [Finset.sum_add_distrib,a,b]

private theorem forest_flow {ends : Fin e → Fin (k+1) × Fin (k+1)} {keep : Fin e → Prop}
    (P : Tree ends keep) (flow : Fin e → ℤ)
    (support : ∀ d, flow d ≠ 0 → ∃ j, P.pick j = d)
    (balance : ∀ x, ∑ d, flow d * delta (ends d) x = 0) : ∀ d, flow d = 0 := by
  classical
  let bound := ∑ x : Fin (k+1), P.height x
  have hb (x) : P.height x ≤ bound := Finset.single_le_sum (f := P.height) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  have elim (i : Fin k) : flow (P.pick i) = 0 := by
    generalize hh : bound-P.height i.succ = m
    induction m using Nat.strong_induction_on generalizing i with
    | h m IH =>
      have sum := balance i.succ
      rw [Finset.sum_eq_single (P.pick i)] at sum
      · obtain ⟨par,small⟩ := parent_spec P i
        have ne : parent P i ≠ i.succ := by intro eq; rw [eq] at small; omega
        rcases par with e|e <;> simpa [e,delta,vertex,ne] using sum
      · intro d _ dif
        by_cases zero : flow d=0
        · simp [zero]
        obtain ⟨j,rfl⟩ := support d zero
        have ij : j≠i := fun eq => dif (congrArg P.pick eq)
        obtain ⟨par,small⟩ := parent_spec P j
        by_cases cross : parent P j=i.succ
        · rw [cross] at small
          have hb' := hb j.succ
          have h₁ := IH (bound-P.height j.succ) (by omega) j rfl
          exact (zero h₁).elim
        · have ji : j.succ ≠ i.succ := fun z => ij (Fin.succ_inj.mp z)
          rcases par with eq|eq <;> simp [delta,vertex,eq,ji,cross]
      · simp
  intro d
  by_contra bad
  obtain ⟨j,rfl⟩ := support _ bad
  exact bad (elim j)

/-- Give every face a sign. Relative to its stored cyclic boundary the two
oriented contributions at each edge are opposite. -/
theorem coherent (G : Gluing v f e) (terminal : (f+1)+4=2*(v+1)) :
    ∃ s : Fin (f+1) → ℤ, (∀ i, s i=1 ∨ s i= -1) ∧
      ∀ d, s (G.dual d).1 * coefficient G (G.dual d).1 d =
        -(s (G.dual d).2 * coefficient G (G.dual d).2 d) := by
  classical
  have cnt := G.incidence_count
  obtain ⟨D,P,cover⟩ := tree_cotree_cover _ _ G.primalConnected G.dualConnected G.bypass (by omega)
  let twist (i : Fin f) := -(coefficient G i.succ (D.pick i)) * coefficient G (parent D i) (D.pick i)
  have unitCoeffs (i : Fin f) : unit (coefficient G i.succ (D.pick i)) ∧ unit (coefficient G (parent D i) (D.pick i)) := by
    have ends := (parent_spec D i).1
    constructor <;> apply coeff_unit <;> rcases ends with eq|eq <;> simp [incident,eq]
  have tu (i : Fin f) : unit (twist i) := mul_unit (neg_unit (unitCoeffs i).1) (unitCoeffs i).2
  let s := propagate D twist
  have du (i : Fin f) : flux G s (D.pick i) = 0 := by
    have step : s i.succ = twist i * s (parent D i) := by
      rcases i with ⟨k,hi⟩
      change propagate D twist ⟨k+1,_⟩ = _
      rw [propagate]
    rw [flux_pair]
    have ends := (parent_spec D i).1
    have hu := (unitCoeffs i).1
    rcases ends with eq|eq <;> simp only [eq,step,twist] <;>
      rcases hu with h|h <;> rw [h] <;> ring
  have sup (d) (nz : flux G s d ≠ 0) : ∃ i, P.pick i=d :=
    (cover d).resolve_right (fun ⟨j,eq⟩ => nz (eq ▸ du j))
  have div (x) : ∑ d, flux G s d * delta (G.primal d) x=0 := by
    simp only [flux,Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,face_balance,mul_zero,Finset.sum_const_zero]
  refine ⟨s,prop_unit D twist tu,fun d => ?_⟩
  have h := forest_flow P (flux G s) sup div d
  rw [flux_pair] at h
  omega

end Recognition.Orientation

namespace Recognition.Orientation
open PlanarDegrees.Topology

def corner (G : Gluing v f e) (i : Fin (f+1)) (k : Fin 3) :=
  if k=0 then (G.tri i).a else if k=1 then (G.tri i).b else (G.tri i).c

def side (G : Gluing v f e) (i : Fin (f+1)) (k : Fin 3) :=
  if k=0 then (G.tri i).ab else if k=1 then (G.tri i).bc else (G.tri i).ca

theorem side_ends (G : Gluing v f e) (i : Fin (f+1)) (k : Fin 3) :
    Across G.primal (side G i k) (corner G i k) (corner G i (k+1)) := by
  have cases3 : ∀ j : Fin 3, j=0 ∨ j=1 ∨ j=2 := by decide
  rcases cases3 k with rfl|rfl|rfl
  · simpa [corner,side] using G.abEnds i
  · simpa [corner,side,show (1+1 : Fin 3)=2 by decide] using G.bcEnds i
  · simpa [corner,side,show (2+1 : Fin 3)=0 by decide] using G.caEnds i

theorem side_coeff (G : Gluing v f e) (i : Fin (f+1)) (k : Fin 3) :
    coefficient G i (side G i k) =
    if G.primal (side G i k) = (corner G i k,corner G i (k+1)) then 1 else -1 := by
  have nd := G.sidesDistinct i
  simp only [Triangle.sides,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd
  have cases3 : ∀ j : Fin 3, j=0 ∨ j=1 ∨ j=2 := by decide
  rcases cases3 k with rfl|rfl|rfl <;>
    simp [coefficient,side,corner,show (1+1 : Fin 3)=2 by decide,show (2+1 : Fin 3)=0 by decide,
      nd.1.1,nd.1.2,nd.2.1,Ne.symm nd.1.1,Ne.symm nd.1.2,Ne.symm nd.2.1,direction]

theorem side_injective (G : Gluing v f e) (i : Fin (f+1)) : Function.Injective (side G i) := by
  have nd := G.sidesDistinct i
  simp only [Triangle.sides,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd
  have cases3 : ∀ j : Fin 3, j=0 ∨ j=1 ∨ j=2 := by decide
  intro k l eq
  rcases cases3 k with rfl|rfl|rfl <;> rcases cases3 l with rfl|rfl|rfl <;>
    simp_all [side]

theorem incident_side (G : Gluing v f e) (i : Fin (f+1)) (d : Fin e) :
    incident G.dual d i ↔ ∃ k, side G i k=d := by
  rw [G.faceSide,Triangle.sides]
  have cases3 : ∀ j : Fin 3, j=0 ∨ j=1 ∨ j=2 := by decide
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro (rfl|rfl|rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  · rintro ⟨k,rfl⟩; rcases cases3 k with rfl|rfl|rfl <;> simp [side]

end Recognition.Orientation
