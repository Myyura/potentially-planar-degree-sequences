import SparseBoundary.LeafReduction
import SparseBoundary.FanOuter
import SparseBoundary.GraphEnumeration
import SparseBoundary.GraphWeighted
import SparseBoundary.GraphPerm

namespace SparseBoundary.RimGrowth
open Graph

/-- The last label is the apex. The rim labels are in cyclic order. -/
def Ordered (G : Graph (n+3)) : Prop :=
  ∀ a b c d : Fin (n+3), a<b → b<c → c<d → d.val<n+2 →
    G.adj a c=true → G.adj b d=true → False

theorem ordered_planar {G : Graph (n+3)} (ho : Ordered G) : G.Planar := by
  apply Fan.outer_order_planar (v:=Fin.last (n+2))
  refine ⟨Fin.val,fun _ _ => Fin.ext,?_⟩
  intro a b x y ha hb hx hy ax ay bx by' hab hxy
  have lt {v : Fin (n+3)} (ne : v≠Fin.last (n+2)) : v.val<n+2 := by
    have hn : v.val≠n+2 := fun eq => ne (Fin.ext eq)
    omega
  have av:=lt ha; have bv:=lt hb; have xv:=lt hx; have yv:=lt hy
  have neq {i j : Fin (n+3)} (h : i≠j) : i.val ≠ j.val := fun eq => h (Fin.ext eq)
  have e1:=neq ax; have e2:=neq ay; have e3:=neq bx; have e4:=neq by'
  have sym1 := (G.adj_comm b a).trans hab
  have sym2 := (G.adj_comm y x).trans hxy
  have no (a x b y : Fin (n+3)) (h1 : G.adj a b=true) (h2 : G.adj x y=true) (hy : y.val<n+2) :
      ¬ (a.val<x.val ∧ x.val<b.val ∧ b.val<y.val) := fun ⟨p,q,r⟩ => ho a x b y p q r hy h1 h2
  have h1:=no a x b y hab hxy yv; have h2:=no a y b x hab sym2 xv
  have h3:=no b x a y sym1 hxy yv; have h4:=no b y a x sym1 sym2 xv
  have h5:=no x a y b hxy hab bv; have h6:=no x b y a hxy sym1 av
  have h7:=no y a x b sym2 hab bv; have h8:=no y b x a sym2 sym1 av
  simp only [decide_eq_decide]
  omega

def lastRim (n : Nat) : Fin (n+3) := (Fin.last (n+1)).castSucc

private def row (n : Nat) (v : Fin (n+3)) : Bool :=
  v==0 || v==lastRim n || v==Fin.last (n+2)

private def extend (G : Graph (n+3)) : Graph (n+1+3) :=
  adjoinRow (row n) (G.editEdge 0 (lastRim n) false)

private theorem zero_ne (n : Nat) : (0 : Fin (n+3)) ≠ lastRim n := by
  intro e; have := congrArg Fin.val e; simp [lastRim] at this

private theorem back (G : Graph (n+3)) (x : Fin (n+3)) :
    (extend G).adj 0 x.succ=row n x := by simp [extend,incident]

private theorem keep (G : Graph (n+3)) (i j : Fin (n+3)) :
    (extend G).adj i.succ j.succ = (G.editEdge 0 (lastRim n) false).adj i j := by
  simp [extend,incident]

private theorem original {G : Graph (n+3)} {i j : Fin (n+3)}
    (e : (extend G).adj i.succ j.succ=true) : G.adj i j=true := by
  rw [keep] at e
  unfold editEdge at e
  have symm (u v : Fin (n+3)) : ((if (u=0 ∧ v=lastRim n) ∨ (u=lastRim n ∧ v=0) then false else G.adj u v)) =
      (if (v=0 ∧ u=lastRim n) ∨ (v=lastRim n ∧ u=0) then false else G.adj v u) := by rw [G.adj_comm u v]; grind
  have irr (u : Fin (n+3)) : (if (u=0 ∧ u=lastRim n) ∨ (u=lastRim n ∧ u=0) then false else G.adj u u)=false := by simp
  change (ofRelation (fun u v => if (u=0 ∧ v=lastRim n) ∨ (u=lastRim n ∧ v=0) then false else G.adj u v)).adj i j=true at e
  rw [adj_ofRelation _ symm irr] at e
  split at e <;> simp_all

private theorem ordered_extend {G : Graph (n+3)} (ho : Ordered G) : Ordered (extend G) := by
  intro a b c d ab bc cd cap ac bd
  have nz : ∀ (i : Fin (n+4)),0<i.val → ∃ j : Fin (n+3), i=j.succ := fun i hi =>
    Fin.cases (fun h => False.elim (Nat.lt_irrefl 0 h)) (fun j _ => ⟨j,rfl⟩) i hi
  obtain ⟨b,rfl⟩ := nz b (by change a.val < b.val at ab; omega)
  obtain ⟨c,rfl⟩ := nz c (by change b.succ.val < c.val at bc; omega)
  obtain ⟨d,rfl⟩ := nz d (by change c.succ.val < d.val at cd; omega)
  cases a using Fin.cases with
  | zero =>
    rw [back] at ac
    simp only [row,Bool.or_eq_true,beq_iff_eq] at ac
    rcases ac with (h|h)|h <;> subst c <;>
      simp [lastRim,Fin.lt_def] at bc cd cap <;> omega
  | succ a =>
    exact ho a b c d (Fin.succ_lt_succ_iff.mp ab) (Fin.succ_lt_succ_iff.mp bc) (Fin.succ_lt_succ_iff.mp cd) (by simpa using cap)
      (original ac) (original bd)

private theorem new_deg (G : Graph (n+3)) : (extend G).degree 0=3 := by
  rw [extend,degree_adjoin_zero]
  have pn : ([0,lastRim n,Fin.last (n+2)] : List (Fin (n+3))).Nodup := by
    simp [lastRim,Fin.ext_iff]
  have perm := (List.perm_ext_iff_of_nodup ((List.nodup_finRange (n+3)).filter (row n)) pn).mpr (by
    intro v; simp [row,List.mem_finRange,or_assoc])
  exact perm.length_eq.trans rfl

private theorem old_deg (G : Graph (n+3)) (edge : G.adj 0 (lastRim n)=true) (v : Fin (n+3)) :
    (extend G).degree v.succ = G.degree v + (if v=Fin.last (n+2) then 1 else 0) := by
  rw [extend,degree_adjoin_succ]
  have he:=degree_edit (zero_ne n) G false v
  rw [edge] at he
  have a : Fin.last (n+2) ≠ (0 : Fin (n+3)) := by simp [Fin.ext_iff]
  have b : Fin.last (n+2) ≠ lastRim n := by simp [Fin.ext_iff,lastRim]
  by_cases e1 : v=0 <;> by_cases e2 : v=lastRim n <;> by_cases e3 : v=Fin.last (n+2) <;>
    simp_all [row] <;> omega

private theorem next_edge (G : Graph (n+3)) : (extend G).adj 0 (lastRim (n+1))=true := by
  change (extend G).adj 0 (lastRim n).succ=true
  simp [back,row]

def rimDegrees (G : Graph (n+3)) := List.ofFn (fun v : Fin (n+2) => G.degree v.castSucc)
def apexDegree (G : Graph (n+3)) := G.degree (Fin.last (n+2))

private theorem list_extend (G : Graph (n+3)) (edge : G.adj 0 (lastRim n)=true) :
    rimDegrees (extend G)=3::rimDegrees G ∧ apexDegree (extend G)=apexDegree G+1 := by
  constructor
  · unfold rimDegrees
    rw [List.ofFn_succ]
    congr 1
    · exact new_deg G
    · congr 1; funext j
      change (extend G).degree j.castSucc.succ=G.degree j.castSucc
      have ne : j.castSucc≠Fin.last (n+2) := fun eq => by have ev := congrArg Fin.val eq; simp at ev; omega
      simp [old_deg _ edge,ne]
  · exact (old_deg G edge (Fin.last (n+2))).trans (by simp [apexDegree])

/-- Subdividing the outer edge from first to last rim vertex while adding
    its midpoint to the apex neighborhood permits any number of additional
    threes, each increasing the apex by one. -/
theorem realize_growing (G : Graph (n+3)) (ho : Ordered G) (edge : G.adj 0 (lastRim n)=true)
    (k : Nat) : Planaric ((apexDegree G+k)::(List.replicate k 3 ++ rimDegrees G)) := by
  induction k generalizing n with
  | zero =>
    have hp := Graph.planaric_profile (ordered_planar ho)
    have split : List.ofFn G.degree = rimDegrees G ++ [apexDegree G] := List.ofFn_succ_last ..
    rw [split] at hp
    simpa only [Nat.add_zero,List.replicate_zero,List.nil_append,List.cons_append] using
      (planaric_perm (List.perm_append_comm (l₁:=rimDegrees G) (l₂:=[apexDegree G]))).mp hp
  | succ k ih =>
    have h := ih (extend G) (ordered_extend ho) (next_edge G)
    rw [(list_extend G edge).1,(list_extend G edge).2] at h
    simpa [List.replicate_succ',Nat.add_assoc,Nat.add_comm 1 k] using h

end SparseBoundary.RimGrowth
