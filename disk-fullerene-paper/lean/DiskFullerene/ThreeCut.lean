import DiskFullerene.DualDisk

namespace DiskFullerene
open Separation

def ThreeEdges (a b c : E) (t : E) : Prop := t=a ∨ t=b ∨ t=c

/-- The two connected components and precisely their three crossing edges. -/
structure Bipartition {V E : Type} (ends : E → V × V) (cut : E → Prop) where
  left : V → Prop
  inhabitedLeft : ∃ x, left x
  inhabitedRight : ∃ x, ¬ left x
  components : ∀ x y, (left x ↔ left y) ↔ Walk (Adj ends (fun d => ¬cut d)) x y
  crosses : ∀ d, cut d ↔ ¬(left (ends d).1 ↔ left (ends d).2)

private theorem walkFlip {V E} {ends : E → V × V} {keep : E → Prop} {i j}
    (p : Walk (Adj ends keep) i j) : Walk (Adj ends keep) j i :=
  p.symm (fun _ _ ⟨e,h,a⟩ => ⟨e,h,a.symm⟩)

private theorem onEdge {V E} {ends : E → V × V} {keep : E → Prop} {d : E}
    {x y} (cross : Across ends d x y) (path : Walk (Adj ends keep) (ends d).1 (ends d).2) :
    Walk (Adj ends keep) x y := by
  rcases cross with h|h <;> rw [h] at path
  · exact path
  · exact walkFlip path

private theorem twoComponents {E V : Type} (ends : E → V × V) (a b c : E)
    (two : ∀ i j x y, Walk (Adj ends (fun d => ¬(d=i ∨ d=j))) x y)
    (apart : ¬ ∀ x y, Walk (Adj ends (fun d => ¬ ThreeEdges a b c d)) x y) :
    Nonempty (Bipartition ends (ThreeEdges a b c)) := by
  classical
  let cut := ThreeEdges a b c
  let R := Adj ends (fun d => ¬cut d)
  let A := (ends a).1
  let B := (ends a).2
  let L := fun v => Walk R A v
  have cover (v) : Walk R A v ∨ Walk R B v := by
    have p := two b c A v
    induction p with
    | refl => exact Or.inl .refl
    | @step u v _ e ih =>
      obtain ⟨t,notBC,ea⟩ := e
      by_cases ta : t=a
      · subst t
        rcases ea with hh|hh
        · exact Or.inr (by change Walk R (ends a).2 v; rw [hh]; exact .refl)
        · exact Or.inl (by change Walk R (ends a).1 v; rw [hh]; exact .refl)
      · have step : R u v := ⟨t,by change ¬(t=a ∨ t=b ∨ t=c); grind,ea⟩
        exact ih.imp (·.step step) (·.step step)
  have splitAB : ¬Walk R A B := by
    intro bridge
    apply apart
    intro x y
    have reach (z) : Walk R A z := (cover z).elim id (bridge.trans ·)
    exact (walkFlip (reach x)).trans (reach y)
  have comp (x y) : (L x ↔ L y) ↔ Walk R x y := by
    constructor
    · intro hxy
      rcases cover x with hx|hx
      · exact (walkFlip hx).trans (hxy.mp hx)
      · rcases cover y with hy|hy
        · exact (walkFlip (hxy.mpr hy)).trans hy
        · exact (walkFlip hx).trans hy
    · intro p; exact ⟨(·.trans p),(·.trans (walkFlip p))⟩
  refine ⟨⟨L,⟨A,.refl⟩,⟨B,splitAB⟩,comp,?_⟩⟩
  intro d
  constructor
  · intro marked eq
    have bridge := (comp _ _).mp eq
    have claim (i j) (only : ∀ t, ¬(t=i ∨ t=j) → cut t → t=d) : False := by
      apply apart
      intro x y
      have p := two i j x y
      induction p with
      | refl => exact .refl
      | @step u v _ hop ih =>
        obtain ⟨t,ok,atEdge⟩ := hop
        by_cases ct : cut t
        · have e := only t ok ct
          subst t
          exact ih.trans (onEdge atEdge bridge)
        · exact ih.step ⟨t,ct,atEdge⟩
    rcases marked with h|h|h
    · exact claim b c (by intro t hh k; dsimp [cut,ThreeEdges] at k; grind)
    · exact claim a c (by intro t hh k; dsimp [cut,ThreeEdges] at k; grind)
    · exact claim a b (by intro t hh k; dsimp [cut,ThreeEdges] at k; grind)
  · intro crossing
    by_cases h : cut d
    · exact h
    · exact False.elim (crossing ((comp _ _).mpr (.step .refl ⟨d,h,Or.inl rfl⟩)))

namespace Dual

private theorem edgeFor {M} (G : IsDiskFullerene M h) {i j : Face M} (adj : j ∈ dualRow G i) :
    ∃ e, Across (dual G) e i j := by
  obtain ⟨d,di,dj⟩ := (mem_row_iff G i j).mp adj
  obtain ⟨e,eq⟩ := repr_dart G (incident_dart G di)
  exact ⟨e,crossTable G eq (Or.inl ⟨di,dj⟩)⟩

/-- A genuine triangle in the dual cuts the original primal graph into two
connected components. In particular this applies to the triangle consisting
of the apex and the endpoints of any boundary chord. -/
theorem triangle_separates {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    {x y z : Face M} (xy : y ∈ dualRow G x) (yz : z ∈ dualRow G y) (zx : x ∈ dualRow G z) :
    ∃ a b c : Edge M, Across (dual G) a x y ∧ Across (dual G) b y z ∧ Across (dual G) c z x ∧
      Nonempty (Bipartition (primal G) (ThreeEdges a b c)) := by
  obtain ⟨a,ha⟩ := edgeFor G xy
  obtain ⟨b,hb⟩ := edgeFor G yz
  obtain ⟨c,hc⟩ := edgeFor G zx
  have nxy : x ≠ y := fun eq => row_no_loop G hh x (eq ▸ xy)
  have nyz : y ≠ z := fun eq => row_no_loop G hh y (eq ▸ yz)
  have nzx : z ≠ x := fun eq => row_no_loop G hh z (eq ▸ zx)
  have apart : ¬ ∀ i j, Walk (Adj (primal G) (fun e => ¬ThreeEdges a b c e)) i j := by
    apply separates_on_sphere (by have := G.connectivity.1; omega)
      (show 0<M.faces.length by simp [MapData.faces]) (table_euler G)
      (fun i j => liftDual G (fun _ _ _ _ => trivial) (dual_connected G hh i j))
      (vertexBypassTable G) (S := ThreeEdges a b c) ⟨a,Or.inl rfl⟩
    have atA (v) : Separation.incident (dual G) a v ↔ x=v ∨ y=v := by
      rcases ha with H|H <;> simp [Separation.incident,H,or_comm]
    have atB (v) : Separation.incident (dual G) b v ↔ y=v ∨ z=v := by
      rcases hb with H|H <;> simp [Separation.incident,H,or_comm]
    have atC (v) : Separation.incident (dual G) c v ↔ z=v ∨ x=v := by
      rcases hc with H|H <;> simp [Separation.incident,H,or_comm]
    have ab : a≠b := by intro eq; have := (atB x).mp (eq ▸ (atA x).mpr (by simp)); grind
    have bc : b≠c := by intro eq; have := (atC y).mp (eq ▸ (atB y).mpr (by simp)); grind
    have ca : c≠a := by intro eq; have := (atA z).mp (eq ▸ (atC z).mpr (by simp)); grind
    intro d hd v hv
    rcases hd with rfl|rfl|rfl
    · rcases (atA v).mp hv with rfl|rfl
      · exact ⟨c,Or.inr (Or.inr rfl),(atC _).mpr (by simp),ca⟩
      · exact ⟨b,Or.inr (Or.inl rfl),(atB _).mpr (by simp),Ne.symm ab⟩
    · rcases (atB v).mp hv with rfl|rfl
      · exact ⟨a,Or.inl rfl,(atA _).mpr (by simp),ab⟩
      · exact ⟨c,Or.inr (Or.inr rfl),(atC _).mpr (by simp),Ne.symm bc⟩
    · rcases (atC v).mp hv with rfl|rfl
      · exact ⟨b,Or.inr (Or.inl rfl),(atB _).mpr (by simp),bc⟩
      · exact ⟨a,Or.inl rfl,(atA _).mpr (by simp),Ne.symm ca⟩
  exact ⟨a,b,c,ha,hb,hc,twoComponents _ a b c (primalResilient G) apart⟩

end Dual
end DiskFullerene
