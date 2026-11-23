import DiskFullerene.ActualLoads

namespace DiskFullerene.Dual
open Strip EndEuler EndLabels

def TriangleSide.swapMarks {M} {G : IsDiskFullerene M h} {w x y} (S : TriangleSide G w x y) :
    TriangleSide G w y x := by
  have eq : ThreeEdges S.yw S.xy S.wx = ThreeEdges S.wx S.xy S.yw := by
    funext e; apply propext; simp [ThreeEdges,or_comm,or_left_comm]
  refine ⟨S.yw,S.xy,S.wx,S.last.symm,S.middle.symm,S.first.symm,⟨S.part.left,S.part.inhabitedLeft,S.part.inhabitedRight,?_,?_⟩⟩
  · rw [eq]; exact S.part.components
  · rw [eq]; exact S.part.crosses

theorem swapped_count {M} {G : IsDiskFullerene M h} {w x y} (S : TriangleSide G w x y)
    (B : Bool) (f : Face M) : vertexCountAt S.swapMarks B f=vertexCountAt S B f := rfl

private theorem complementary (xs : List α) (p : α → Bool) :
    xs.countP p+xs.countP (fun i => !p i)=xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : p x <;> simp [h] at * <;> omega

theorem seam_load_sum {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y}
    (S : TriangleSide G w x y) (b : Bool) {f : Face M} (mark : f=x ∨ f=y) :
    (dualRow G f).length=2+loadAt S b f+loadAt S (!b) f := by
  classical
  have pos := seam_count_pos hh S b mark
  have neg := seam_count_pos hh S (!b) mark
  have eq : (fun v => !primalLabelSide S b v)=primalLabelSide S (!b) := by
    funext v; cases b <;> by_cases h : S.color v <;> simp [primalLabelSide,h]
  have count := complementary M.faces[f.val] (primalLabelSide S b)
  rw [eq] at count
  change vertexCountAt S b f+vertexCountAt S (!b) f=M.faces[f.val].length at count
  unfold loadAt
  rw [row_length]; omega

structure SeamState {M} (G : IsDiskFullerene M h) where
  x : Face M
  y : Face M
  cut : TriangleSide G (apex M) x y
  side : Bool

def SeamState.flip {M} {G : IsDiskFullerene M h} (S : SeamState G) : SeamState G :=
  ⟨S.y,S.x,S.cut.swapMarks,S.side⟩

noncomputable def SeamState.loads {M} {G : IsDiskFullerene M h} (S : SeamState G) : Loads :=
  ⟨loadAt S.cut S.side S.x,loadAt S.cut S.side S.y⟩

def SeamState.pick {M} {G : IsDiskFullerene M h} (P : SeamState G) : Side → SeamState G
  | .left => P
  | .right => P.flip

/-- Local facial data of a triangle on the ordered path of seams. It records
the primal vertex of the middle triangle and of the apex triangle facing
it. No numerical degree or load equation occurs in this input. -/
structure SeamStep {M} {G : IsDiskFullerene M h} (P Q : SeamState G) (s : Side) : Prop where
  retained : (P.pick s).x = Q.x
  different : (P.pick s).y ≠ Q.y
  faces : ∃ t o : Fin M.ord,
    (∀ i, i∈triangle t ↔ i=Q.x ∨ i=(P.pick s).y ∨ i=Q.y) ∧
    (∀ i, i∈triangle o ↔ i=apex M ∨ i=(P.pick s).y ∨ i=Q.y) ∧
    vertexSide (P.pick s).cut P.side t=false ∧ vertexSide Q.cut Q.side t=true

private theorem raw_step {M} {G : IsDiskFullerene M h} (hh : 3≤h) {P Q : SeamState G}
    (A : SeamStep P Q s) : Q.loads=after P.loads s ∧ allowed (3+dropped P.loads s) := by
  obtain ⟨ret,ne,⟨t,o,tri,cap,old,new⟩⟩ := A
  rcases Q with ⟨x,z,T,d⟩
  change (P.pick s).x=x at ret
  subst x
  have upd := actual_load_step hh (P.pick s).cut T P.side d ne tri cap old new
  have diff : (P.pick s).y≠apex M := by
    have ee := (P.pick s).cut.last
    have ne := left_ne_right G hh (P.pick s).cut.yw
    rcases ee with e|e <;> rw [e] at ne <;> simp_all [ne_comm]
  have deg := inner_degree G diff
  have same : (P.pick s).side=P.side := by cases s <;> rfl
  have ⟨u,v,w⟩ := upd
  change loadAt T d (P.pick s).x=loadAt (P.pick s).cut P.side (P.pick s).x+1 at u
  change loadAt T d z=1 at v
  change (dualRow G (P.pick s).y).length=3+loadAt (P.pick s).cut P.side (P.pick s).y at w
  rw [w] at deg
  cases s <;> simp only [SeamState.loads,SeamState.pick,SeamState.flip,after,kept,dropped,Loads.mk.injEq,allowed] at * <;>
    simp only [loadAt,swapped_count] at * <;> exact ⟨⟨u,v⟩,deg⟩

inductive ActualTrace {M} {G : IsDiskFullerene M h} : SeamState G → List Side → SeamState G → Prop where
  | done (S) : ActualTrace S [] S
  | next {P Q R s ss} : SeamStep P Q s → ActualTrace Q ss R → ActualTrace P (s::ss) R

/-- A finite sequence of actual adjacent seam pairs with the opposite
cap loads determines an accepted strip word. Its length is arbitrary. -/
theorem trace_complete {M} {G : IsDiskFullerene M h} (hh : 3≤h) {P Q : SeamState G}
    {moves g} (path : ActualTrace P moves Q)
    (finish : (⟨loadAt Q.cut (!Q.side) Q.x,loadAt Q.cut (!Q.side) Q.y⟩ : Loads)=endLoads g) :
    Complete P.loads moves g := by
  induction path with
  | done P =>
    have left := seam_load_sum hh P.cut P.side (f:=P.x) (Or.inl rfl)
    have right := seam_load_sum hh P.cut P.side (f:=P.y) (Or.inr rfl)
    have nx := left_ne_right G hh P.cut.wx
    have ny := left_ne_right G hh P.cut.yw
    have aw : P.x≠apex M := by rcases P.cut.first with q|q <;> rw [q] at nx <;> simp_all [ne_comm]
    have bw : P.y≠apex M := by rcases P.cut.last with q|q <;> rw [q] at ny <;> simp_all [ne_comm]
    have dl := inner_degree G aw; have dr := inner_degree G bw
    change allowed (2+P.loads.left+(endLoads g).left) ∧ allowed (2+P.loads.right+(endLoads g).right)
    rw [←finish]
    exact ⟨left ▸ dl,right ▸ dr⟩
  | next step _ ih =>
    have ⟨eq,drop⟩ := raw_step hh step
    exact ⟨drop,eq ▸ ih finish⟩

end DiskFullerene.Dual
