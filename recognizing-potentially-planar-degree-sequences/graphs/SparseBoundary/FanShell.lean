import SparseBoundary.FanOuter
import SparseBoundary.FanSpokes
import SparseBoundary.GraphCone
import SparseBoundary.GraphSeries

namespace SparseBoundary.Fan

open Graph

/-- A circular ordering with a distinguished outermost edge. -/
structure Perimeter (G : Graph n) where
  rank : Fin n → Fin n
  inj : ∀u v, rank u=rank v → u=v
  lo : Fin n
  hi : Fin n
  first : (rank lo).val=0
  last : (rank hi).val+1=n
  edge : G.adj lo hi=true
  chords : ∀u v x y, u≠x → u≠y → v≠x → v≠y → G.adj u v=true → G.adj x y=true →
    noncross (rank u).val (rank v).val (rank x).val (rank y).val

private def newRank {n} (r : Fin n → Fin n) : Fin (n+1) → Fin (n+1) :=
  Fin.cases 0 (fun v => (r v).succ)

private theorem rank_inj (r : Fin n → Fin n) (inj : ∀u v, r u=r v → u=v) :
    ∀ u v, newRank r u=newRank r v → u=v := by
  refine Fin.cases ?_ (fun a => ?_)
  · refine Fin.cases (by simp) (fun b => ?_); simp [newRank,Ne.symm (Fin.succ_ne_zero _)]
  · refine Fin.cases ?_ (fun b => ?_)
    · simp [newRank,Fin.succ_ne_zero]
    · simp only [newRank,Fin.cases_succ,Fin.succ_inj]; exact inj a b

/-- Subdivision of the distinguished boundary edge extends the circular
ordering. The next boundary edge joins the new vertex to the old last
vertex. -/
def Perimeter.grow {G : Graph n} (P : Perimeter G) : Perimeter (G.subdivide P.lo P.hi) := by
  let H := G.subdivide P.lo P.hi
  let R := newRank P.rank
  have inj := rank_inj P.rank P.inj
  have old {a b : Fin n} (e : H.adj a.succ b.succ=true) : G.adj a b=true := by
    simp only [H,subdivide,adjoin_adj,incident,Fin.cases_succ,erase_adj,eraseRel,Bool.and_eq_true] at e
    exact e.1
  have near {v : Fin (n+1)} (e : H.adj 0 v=true) : (R v).val=1 ∨ (R v).val=n := by
    refine Fin.cases ?_ (fun w => ?_) v e
    · simp
    · intro e
      have he : w=P.lo ∨ w=P.hi := by simpa [H,subdivide,incident,pairRow] using e
      rcases he with rfl|rfl
      · exact .inl (by simp [R,newRank,P.first])
      · exact .inr (by simpa [R,newRank] using P.last)
  have ranks {u v : Fin (n+1)} (e : u≠v) : (R u).val ≠ (R v).val :=
    fun eq => e (inj _ _ (Fin.ext eq))
  have border {u v x y : Fin (n+1)} (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y)
      (z : u=0 ∨ v=0) (e : H.adj u v=true) :
      noncross (R u).val (R v).val (R x).val (R y).val := by
    have hux := ranks ux; have huy := ranks uy; have hvx := ranks vx; have hvy := ranks vy
    have b1 := (R x).isLt; have b2 := (R y).isLt
    apply (noncross_iff ..).mpr
    rcases z with rfl|rfl
    · have h := near e
      have zero : (R 0).val=0 := rfl
      omega
    · have h := near ((H.adj_comm ..).trans e)
      have zero : (R 0).val=0 := rfl
      omega
  refine ⟨R,inj,0,P.hi.succ,rfl,?_,?_,?_⟩
  · change (P.rank P.hi).val+1+1=n+1; have := P.last; omega
  · simp [subdivide,incident,pairRow]
  · intro u v x y ux uy vx vy uv xy
    by_cases h1 : u=0 ∨ v=0
    · exact border ux uy vx vy h1 uv
    by_cases h2 : x=0 ∨ y=0
    · apply (noncross_swap (ranks ux) (ranks uy) (ranks vx) (ranks vy)).mpr
      exact border (Ne.symm ux) (Ne.symm vx) (Ne.symm uy) (Ne.symm vy) h2 xy
    obtain ⟨u,rfl⟩ := Fin.eq_succ_of_ne_zero (fun e => h1 (.inl e))
    obtain ⟨v,rfl⟩ := Fin.eq_succ_of_ne_zero (fun e => h1 (.inr e))
    obtain ⟨x,rfl⟩ := Fin.eq_succ_of_ne_zero (fun e => h2 (.inl e))
    obtain ⟨y,rfl⟩ := Fin.eq_succ_of_ne_zero (fun e => h2 (.inr e))
    have no := P.chords u v x y (fun e => ux (congrArg Fin.succ e)) (fun e => uy (congrArg Fin.succ e))
      (fun e => vx (congrArg Fin.succ e)) (fun e => vy (congrArg Fin.succ e)) (old uv) (old xy)
    simpa only [R,newRank,Fin.cases_succ,Fin.val_succ,noncross_iff,Nat.add_lt_add_iff_right] using no


private theorem cone_spoke (G : Graph n) (i : Fin n) : G.cone.adj 0 i.succ=true := by
  simp; rfl

private theorem cone_old (G : Graph n) (i j : Fin n) : G.cone.adj i.succ j.succ=G.adj i j := by
  simp; rfl

private theorem cone_degree_zero (G : Graph n) : G.cone.degree 0=n := by
  simp only [degree,List.finRange_succ,List.filter_cons,adj_self,List.filter_map]
  rw [show G.cone.adj 0 ∘ Fin.succ=(fun _ => true) from funext (cone_spoke G)]
  simp [List.filter_eq_self.mpr]

theorem Perimeter.cone_planar {G : Graph n} (P : Perimeter G) : G.cone.Planar := by
  apply outer_order_planar (v:=0)
  refine ⟨fun i => (newRank P.rank i).val,fun i j eq => rank_inj _ P.inj i j (Fin.ext eq),?_⟩
  intro u v x y uz vz xz yz ux uy vx vy uv xy
  obtain ⟨u,rfl⟩ := Fin.eq_succ_of_ne_zero uz
  obtain ⟨v,rfl⟩ := Fin.eq_succ_of_ne_zero vz
  obtain ⟨x,rfl⟩ := Fin.eq_succ_of_ne_zero xz
  obtain ⟨y,rfl⟩ := Fin.eq_succ_of_ne_zero yz
  rw [cone_old] at uv xy
  have nc := P.chords u v x y (fun e => ux (congrArg Fin.succ e)) (fun e => uy (congrArg Fin.succ e))
      (fun e => vx (congrArg Fin.succ e)) (fun e => vy (congrArg Fin.succ e)) uv xy
  change noncross (P.rank u).succ.val (P.rank v).succ.val (P.rank x).succ.val (P.rank y).succ.val
  simpa only [noncross_iff,Fin.val_succ,Nat.add_lt_add_iff_right] using nc

/-- A core shell exposes a boundary edge for further subdivisions. Its
degrees after coning are bounded by the target entries and have a known
total excess over three per rim vertex. -/
def ShellFor (d : List Nat) (c : Nat) : Prop :=
  ∃ G : Graph d.length, Nonempty (Perimeter G) ∧
    (∀i : Fin d.length, G.degree i+1≤d[i]) ∧
    ((List.finRange d.length).map (fun i => G.degree i+1)).sum=3*d.length+c

theorem shell_cons {d : List Nat} {c a : Nat} (h : ShellFor d c) (ha : 3≤a) :
    ShellFor (a::d) c := by
  obtain ⟨G,⟨P⟩,fit,total⟩ := h
  refine ⟨G.subdivide P.lo P.hi,⟨P.grow⟩,?_,?_⟩
  · refine Fin.cases ?_ (fun i => ?_)
    · change (G.subdivide P.lo P.hi).degree 0+1≤a
      rw [subdivide_new_degree P.edge]; exact ha
    · change (G.subdivide P.lo P.hi).degree i.succ+1≤d[i]
      rw [subdivide_old_degree P.edge]; exact fit i
  · simp only [List.length_cons,List.finRange_succ,List.map_cons,List.map_map,List.sum_cons,
      subdivide_new_degree P.edge]
    rw [show (fun i => (G.subdivide P.lo P.hi).degree i+1) ∘ Fin.succ=
      (fun i => G.degree i+1) from funext (fun i => by simp [subdivide_old_degree P.edge])]
    omega

theorem shell_append {d : List Nat} {c : Nat} (h : ShellFor d c) (xs : List Nat) (hm : ∀v∈xs,3≤v) :
    ShellFor (xs++d) c := by
  induction xs with
  | nil => exact h
  | cons x xs ih => exact shell_cons (ih (fun v m => hm v (by simp [m]))) (hm x (by simp))

/-- Exact universal degree and two-budget from a certified shell. -/
theorem universal_of_shell {d : List Nat} {c t : Nat} (h : ShellFor d c)
    (vol : d.sum=3*d.length+c+t) :
    Planaric (List.replicate t 2 ++ (d.length+t)::d) := by
  obtain ⟨G,⟨P⟩,fit,total⟩ := h
  have e (i : Fin d.length) : G.cone.degree i.succ=G.degree i+1 := degree_in_cone G i
  obtain ⟨m,hm,plan⟩ := expand_spokes d G.cone P.cone_planar (cone_spoke G)
    (fun i => (e i).symm ▸ fit i)
  simp only [e,total] at hm
  have mt : m=t := by omega
  rw [mt,cone_degree_zero] at plan
  exact (planaric_perm List.perm_middle).mpr plan

end SparseBoundary.Fan
