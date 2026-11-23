import DiskFullerene.LoadTransition
import DiskFullerene.Strip

namespace DiskFullerene.Dual
open EndLabels EndEuler Separation

noncomputable def vertexCountAt {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (b : Bool) (f : Face M) :=
  M.faces[f.val].countP (primalLabelSide S b)

noncomputable def loadAt {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (b : Bool) (f : Face M) := vertexCountAt S b f - 1

private theorem label_fin {M} {G : IsDiskFullerene M h} {w x y} (S : TriangleSide G w x y)
    (b : Bool) (v : Fin M.ord) : primalLabelSide S b v.val = vertexSide S b v := by
  classical
  have eq : S.color v.val ↔ S.part.left v := ⟨fun ⟨_,k⟩ => k,fun k => ⟨_,k⟩⟩
  simp [primalLabelSide,vertexSide,eq]

private theorem valid_label {M} (G : IsDiskFullerene M h) {f : Face M} {a} (hit : a∈M.faces[f.val]) : a<M.ord := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hit
  have atP := side_at M.faces[f.val] i hi
  have dart := dart_info G (incident_dart G (sideDart_mem M f ⟨i,hi⟩))
  change sideDart M f ⟨i,hi⟩ = _ at atP
  rw [atP] at dart
  exact dart.1

private theorem sameOnFace {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (b : Bool) {f : Face M} (nf : f≠w ∧ f≠x ∧ f≠y)
    {u v} (U : u∈M.faces[f.val]) (V : v∈M.faces[f.val]) :
    primalLabelSide S b u=primalLabelSide S b v := by
  classical
  simp [primalLabelSide,S.face_constant nf U V]

private theorem list_step {α} [DecidableEq α] (xs : List α) (p q : α→Bool) (t o : α) (ne : t≠o)
    (ta : p t=false) (oa : p o=false)
    (step : ∀ v∈xs, q v=if v=t ∨ v=o then !p v else p v) :
    xs.countP q = xs.countP p + xs.count t + xs.count o := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have st := step x (by simp)
    have tail := ih (fun v m => step v (by simp [m]))
    by_cases xt : x=t <;> by_cases xo : x=o <;> cases hp : p x <;>
      simp_all <;> omega

theorem seam_count_pos {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y}
    (S : TriangleSide G w x y) (b : Bool) {f : Face M} (marked : f=x ∨ f=y) :
    0<vertexCountAt S b f := by
  classical
  let e := S.xy
  have pp := (S.part.crosses e).mp (Or.inr (Or.inl rfl))
  let v := (primal G e).1; let z := (primal G e).2
  have opposite : vertexSide S b v≠vertexSide S b z := by
    by_cases a : S.part.left v <;> by_cases c : S.part.left z <;>
      cases b <;> simp_all [vertexSide,v,z,e]
  have two (p) (ep : endpoint G e p) : f∈triangle p := by
    obtain ⟨a,c⟩ := (endpoint_iff G hh e p).mp ep
    have vals : Across (dual G) e x y := S.middle
    rcases vals with eq|eq <;> rw [eq] at a c <;> rcases marked with rfl|rfl <;> assumption
  apply List.countP_pos_iff.mpr
  cases pv : vertexSide S b v with
  | true => exact ⟨v.val,(mem_triangle _ _).mp (two v (Or.inl rfl)),(label_fin S b v).trans pv⟩
  | false =>
    have pz : vertexSide S b z=true := by cases h : vertexSide S b z <;> grind
    exact ⟨z.val,(mem_triangle _ _).mp (two z (Or.inr rfl)),(label_fin S b z).trans pz⟩

/-- Recurrence for the loads measured on the original face words. The
dropped vertex y has its final degree; x stays, and z enters with load one. -/
theorem actual_load_step {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y z : Face M}
    (S : TriangleSide G w x y) (T : TriangleSide G w x z) (b d : Bool) (yz : y≠z)
    {t o : Fin M.ord} (tr : ∀ f, f∈triangle t ↔ f=x ∨ f=y ∨ f=z)
    (ap : ∀ f, f∈triangle o ↔ f=w ∨ f=y ∨ f=z)
    (fromSide : vertexSide S b t=false) (toSide : vertexSide T d t=true) :
    loadAt T d x=loadAt S b x+1 ∧ loadAt T d z=1 ∧ (dualRow G y).length=3+loadAt S b y := by
  classical
  have ne {i j : Face M} {e : Edge M} (A : Across (dual G) e i j) : i≠j := by
    have h := left_ne_right G hh e
    rcases A with eq|eq <;> rw [eq] at h <;> simp_all [ne_comm]
  have wx := ne S.first
  have xy := ne S.middle
  have yw := ne S.last
  have xz := ne T.middle
  have zw := ne T.last
  have diff : t.val≠o.val := by
    intro eq
    have same := Fin.ext eq
    have m := (tr x).mpr (by simp)
    have n := (ap x).mp (same ▸ m)
    grind
  let p := primalLabelSide S b; let q := primalLabelSide T d
  have tp : p t.val=false := (label_fin S b t).trans fromSide
  have tq : q t.val=true := (label_fin T d t).trans toSide
  have inT (f) : t.val∈M.faces[f.val] ↔ f=x ∨ f=y ∨ f=z := (mem_triangle t f).symm.trans (tr f)
  have inO (f) : o.val∈M.faces[f.val] ↔ f=w ∨ f=y ∨ f=z := (mem_triangle o f).symm.trans (ap f)
  have zoff {v} (hit : v∈M.faces[z.val]) : p v=false := (sameOnFace S b ⟨zw,xz.symm,yz.symm⟩ hit ((inT _).mpr (by simp))).trans tp
  have yon {v} (hit : v∈M.faces[y.val]) : q v=true := (sameOnFace T d ⟨yw,xy.symm,yz⟩ hit ((inT _).mpr (by simp))).trans tq
  have op := zoff ((inO _).mpr (by simp))
  have step (f : Face M) : vertexCountAt T d f = vertexCountAt S b f +
      (if t.val∈M.faces[f.val] then 1 else 0) + (if o.val∈M.faces[f.val] then 1 else 0) := by
    have nd := List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem f.isLt)
    have uniq : M.faces[f.val].Nodup := of_decide_eq_true (Bool.and_eq_true_iff.mp nd).1
    rw [← uniq.count, ← uniq.count]
    apply list_step _ p q _ _ diff tp op
    intro v hit
    let vtx : Fin M.ord := ⟨v,valid_label G hit⟩
    have update := advance_sides hh S T b d yz tr ap fromSide toSide vtx
    have eqt : vtx=t ↔ v=t.val := Fin.ext_iff
    have eqo : vtx=o ↔ v=o.val := Fin.ext_iff
    simpa only [q,p,← label_fin,eqt,eqo] using update
  have xstep := step x; have ystep := step y; have zstep := step z
  simp only [inT,inO] at xstep ystep zstep
  have pz : vertexCountAt S b z=0 := by
    apply List.countP_eq_zero.mpr
    intro v hv; simp [← zoff hv,p]
  have qy : vertexCountAt T d y=M.faces[y.val].length := List.countP_eq_length.mpr (fun v hit => yon hit)
  have px := seam_count_pos hh S b (f:=x) (Or.inl rfl)
  have py := seam_count_pos hh S b (f:=y) (Or.inr rfl)
  unfold loadAt
  rw [row_length]
  have xw := Ne.symm wx
  simp_all <;> omega

end DiskFullerene.Dual
