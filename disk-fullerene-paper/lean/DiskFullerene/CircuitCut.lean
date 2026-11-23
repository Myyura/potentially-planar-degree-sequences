import DiskFullerene.ThreeCut
import DiskFullerene.InteriorTriangles

namespace DiskFullerene.Separation

def NoLeaf {E F : Type} (ends : E → F × F) (S : E → Prop) : Prop :=
  ∀ d, S d → ∀ x, incident ends d x → ∃ k, S k ∧ incident ends k x ∧ k ≠ d

/-- An edge circuit is a nonempty inclusion-minimal subgraph without a leaf. -/
structure Circuit {E F : Type} (ends : E → F × F) (S : E → Prop) : Prop where
  exists_edge : ∃ d, S d
  closed : NoLeaf ends S
  minimal : ∀ T : E → Prop, (∀ e, T e → S e) → (∃ e, T e) →
    NoLeaf ends T → ∀ e, S e → T e

private theorem along {V E : Type} {pr : E → V × V} {ok : E → Prop} {P : V → Prop}
    (uniform : ∀ e, ok e → (P (pr e).1 ↔ P (pr e).2)) {x y}
    (walk : Walk (Adj pr ok) x y) : P x ↔ P y := by
  induction walk with
  | refl => rfl
  | step _ ed ih =>
    obtain ⟨e,keep,ac⟩ := ed
    have t := uniform e keep
    rcases ac with eq|eq <;> rw [eq] at t
    · exact ih.trans t
    · exact ih.trans t.symm

private theorem flipNoLeaf {E V F : Type} {pr : E → V × V} {du : E → F × F}
    (bypass : FaceBypass pr du) (P : V → Prop) :
    NoLeaf du (fun d => ¬(P (pr d).1 ↔ P (pr d).2)) := by
  intro d diff x hit
  apply Classical.byContradiction
  intro no
  apply diff
  apply along (ok := fun e => e ≠ d ∧ incident du e x) (fun e he => ?_) (bypass x d hit)
  exact Classical.byContradiction fun flip => no ⟨e,flip,he.2,he.1⟩

/-- A simple circuit of dual edges cuts a sphere into exactly two primal
components. Every edge of the circuit has one endpoint in each component. -/
theorem circuit_bipartition {v f e : Nat} {pr : Fin e → Fin v × Fin v} {du : Fin e → Fin f × Fin f}
    (nv : 0<v) (nf : 0<f) (chi : v+f=e+2) (pc : ∀ i j, Walk (Adj pr (fun _ => True)) i j)
    (dc : ∀ i j, Walk (Adj du (fun _ => True)) i j) (vb : FaceBypass du pr) (fb : FaceBypass pr du)
    {S : Fin e → Prop} (C : Circuit du S) : Nonempty (Bipartition pr S) := by
  classical
  let R := Adj pr (fun d => ¬S d)
  have rev : ∀ {a b}, Walk R a b → Walk R b a :=
    fun p => p.symm (fun _ _ ⟨e,h,ed⟩ => ⟨e,h,ed.symm⟩)
  have disconnected := separates_on_sphere nv nf chi dc vb C.exists_edge C.closed
  obtain ⟨a,b,apart⟩ : ∃ a b, ¬Walk R a b := by
    apply Classical.byContradiction; intro nope
    exact disconnected (fun a b => Classical.byContradiction fun ab => nope ⟨a,b,ab⟩)
  have wall (x y) (gap : ¬Walk R x y) :
      ∀ ed, S ed ↔ ¬(Walk R x (pr ed).1 ↔ Walk R x (pr ed).2) := by
    let T := fun ed => ¬(Walk R x (pr ed).1 ↔ Walk R x (pr ed).2)
    have subset (ed) (hT : T ed) : S ed := by
      apply Classical.byContradiction; intro ok
      have step : R (pr ed).1 (pr ed).2 := ⟨ed,ok,Or.inl rfl⟩
      exact hT ⟨(·.step step),fun p => p.trans (rev (.step .refl step))⟩
    have nonempty : ∃ ed, T ed := by
      apply Classical.byContradiction; intro none
      have same := along (P := Walk R x) (fun ed _ => Classical.byContradiction fun flip => none ⟨ed,flip⟩) (pc x y)
      exact gap (same.mp .refl)
    exact fun ed => ⟨C.minimal T subset nonempty (flipNoLeaf fb (Walk R x)) ed,subset ed⟩
  have A := wall a b apart
  have B := wall b a (fun p => apart (rev p))
  obtain ⟨ed,marked⟩ := C.exists_edge
  have cover (x) : Walk R a x ∨ Walk R b x := by
    by_cases ax : Walk R a x
    · exact Or.inl ax
    by_cases bx : Walk R b x
    · exact Or.inr bx
    have X := (wall x a (fun p => ax (rev p)) ed).1 marked
    have phaseA := (A ed).1 marked
    have phaseB := (B ed).1 marked
    have disjoint (i) (ai : Walk R a i) : ¬Walk R b i := fun bi => apart (ai.trans (rev bi))
    have noA (i) (xi : Walk R x i) : ¬Walk R a i := fun ai => ax (ai.trans (rev xi))
    have noB (i) (xi : Walk R x i) : ¬Walk R b i := fun bi => bx (bi.trans (rev xi))
    grind
  refine ⟨⟨Walk R a,⟨a,.refl⟩,⟨b,apart⟩,?_,A⟩⟩
  intro p q
  constructor
  · intro eq
    rcases cover p with hit|bp
    · exact (rev hit).trans (eq.mp hit)
    · rcases cover q with hit|bq
      · exact (rev (eq.mpr hit)).trans hit
      · exact (rev bp).trans bq
  · intro walk; exact ⟨(·.trans walk),(·.trans (rev walk))⟩

end DiskFullerene.Separation

namespace DiskFullerene.Separation

def cyclicNext {n : Nat} (i : Fin (n+1)) : Fin (n+1) :=
  ⟨if i.val+1 < n+1 then i.val+1 else 0,by split <;> omega⟩
def cyclicPrev {n : Nat} (i : Fin (n+1)) : Fin (n+1) :=
  ⟨if i.val=0 then n else i.val-1,by split <;> omega⟩

private theorem next_previous {n} (i : Fin (n+1)) : cyclicNext (cyclicPrev i)=i := by
  apply Fin.ext; dsimp [cyclicNext,cyclicPrev]; split <;> split <;> omega
private theorem previous_next {n} (i : Fin (n+1)) : cyclicPrev (cyclicNext i)=i := by
  apply Fin.ext; dsimp [cyclicNext,cyclicPrev]; split <;> split <;> omega
private theorem next_diff {n} (sz : 1≤n) (i : Fin (n+1)) : cyclicNext i≠i := by
  intro eq; have h := congrArg Fin.val eq; dsimp [cyclicNext] at h; split at h <;> omega

/-- A list of at least three distinct cyclic vertices joined by distinct
edges satisfies the graph-theoretic circuit property. -/
theorem indexed_circuit {V E : Type} {n : Nat} (sz : 2≤n) {ends : E → V × V}
    {v : Fin (n+1) → V} {e : Fin (n+1) → E} (vi : Function.Injective v)
    (ei : Function.Injective e) (joins : ∀ i, Across ends (e i) (v i) (v (cyclicNext i))) :
    Circuit ends (fun ed => ∃ i, ed=e i) := by
  have atIndex (i) (x) : incident ends (e i) x ↔ x=v i ∨ x=v (cyclicNext i) := by
    rcases joins i with h|h <;> simp [incident,h,or_comm,eq_comm]
  have two (i j) (inc : incident ends (e j) (v (cyclicNext i))) : j=i ∨ j=cyclicNext i := by
    rcases (atIndex _ _).1 inc with eq|eq
    · exact Or.inr (vi eq).symm
    · exact Or.inl (by simpa [previous_next] using (congrArg cyclicPrev (vi eq)).symm)
  refine ⟨⟨e 0,0,rfl⟩,?_,?_⟩
  · rintro _ ⟨i,rfl⟩ x hit
    rcases (atIndex _ _).1 hit with rfl|rfl
    · refine ⟨e (cyclicPrev i),⟨_,rfl⟩,(atIndex _ _).2 (Or.inr (congrArg v (next_previous i).symm)),?_⟩
      intro eq; have nj := next_diff (by omega) (cyclicPrev i)
      exact nj ((next_previous i).trans (ei eq).symm)
    · exact ⟨e (cyclicNext i),⟨_,rfl⟩,(atIndex _ _).2 (Or.inl rfl),fun eq => next_diff (by omega) i (ei eq)⟩
  · intro T incl nonempty closed
    have onward (i) (h : T (e i)) : T (e (cyclicNext i)) := by
      obtain ⟨k,marked,inc,ne⟩ := closed _ h _ ((atIndex _ _).2 (Or.inr rfl))
      obtain ⟨j,rfl⟩ := incl _ marked
      rcases two i j inc with rfl|rfl
      · exact False.elim (ne rfl)
      · exact marked
    have path {a b : Nat} (ab : a≤b) (hi : b<n+1) (start : T (e ⟨a,by omega⟩)) : T (e ⟨b,hi⟩) := by
      induction b with
      | zero => have eq : a=0 := by omega
                subst a; exact start
      | succ k ih =>
        by_cases equal : a=k+1
        · subst a; exact start
        · have p := onward ⟨k,by omega⟩ (ih (by omega) (by omega) start)
          simpa [cyclicNext,hi] using p
    obtain ⟨edge,he⟩ := nonempty
    obtain ⟨i,rfl⟩ := incl edge he
    have last := path (a := i.val) (b := n) (by omega) (by omega) he
    have start : T (e 0) := by simpa [cyclicNext] using (onward ⟨n,by omega⟩ last)
    rintro _ ⟨j,rfl⟩
    exact path (a := 0) (b := j.val) (by omega) j.isLt start

end DiskFullerene.Separation

namespace DiskFullerene.Dual
open Separation

structure CycleSide {M : MapData} (G : IsDiskFullerene M h) {n : Nat}
    (v : Fin (n+1) → Face M) where
  edge : Fin (n+1) → Edge M
  spans : ∀ i, Across (dual G) (edge i) (v i) (v (cyclicNext i))
  part : Bipartition (primal G) (fun d => ∃ i, d=edge i)

/-- Every simple dual cycle of any length bounds two actual primal
components. No embedding, triangulated-disk or separation certificate is an input. -/
theorem cycleSides {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h) {n : Nat}
    (sz : 2≤n) (v : Fin (n+1) → Face M) (vi : Function.Injective v)
    (joins : ∀ i, v (cyclicNext i) ∈ dualRow G (v i)) : Nonempty (CycleSide G v) := by
  classical
  have edge (i) : ∃ e, Across (dual G) e (v i) (v (cyclicNext i)) := by
    obtain ⟨d,di,dj⟩ := (mem_row_iff G _ _).mp (joins i)
    obtain ⟨e,eq⟩ := repr_dart G (incident_dart G di)
    exact ⟨e,crossTable G eq (Or.inl ⟨di,dj⟩)⟩
  let e := fun i => (edge i).choose
  have spans (i) : Across (dual G) (e i) (v i) (v (cyclicNext i)) := (edge i).choose_spec
  have ei : Function.Injective e := by
    intro i j eq
    have A := spans i; have B := spans j; rw [eq] at A
    have cases' : (v i=v j) ∨ (v i=v (cyclicNext j) ∧ v (cyclicNext i)=v j) := by
      rcases A with a|a <;> rcases B with b|b <;> rw [a] at b <;> simp only [Prod.mk.injEq] at b <;> grind
    rcases cases' with direct | ⟨r,s⟩
    · exact vi direct
    · have r' := congrArg Fin.val (vi r); have s' := congrArg Fin.val (vi s)
      dsimp [cyclicNext] at r' s'; split at r' <;> split at s' <;> omega
  have pc (x y) : Walk (Adj (primal G) (fun _ => True)) x y := by
    have p := primalResilient G (e 0) (e 0) x y
    induction p with
    | refl => exact .refl
    | step _ adj ih => obtain ⟨k,_,hit⟩ := adj; exact ih.step ⟨k,trivial,hit⟩
  obtain ⟨P⟩ := circuit_bipartition (by have := G.connectivity.1; omega)
    (show 0<M.faces.length by simp [MapData.faces]) (table_euler G) pc
    (fun x y => liftDual G (fun _ _ _ _ => trivial) (dual_connected G hh x y))
    (vertexBypassTable G) (faceBypassTable G hh) (indexed_circuit sz vi ei spans)
  exact ⟨⟨e,spans,P⟩⟩

end DiskFullerene.Dual
