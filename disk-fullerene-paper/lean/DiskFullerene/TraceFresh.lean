import DiskFullerene.StripFresh
import DiskFullerene.StripTrace

namespace DiskFullerene.StripFresh
open Dual EndLabels EndEuler Separation Strip

variable {M : MapData} {G : IsDiskFullerene M h}

def Trace.moves {x y a b} : Trace G x y a b → List Side
  | .done _ _ => []
  | .keepFirst _ tail => .left::tail.moves
  | .keepSecond _ tail => .right::tail.moves

def Trace.records {x y a b} : Trace G x y a b → Prop
  | .done _ _ => True
  | .keepFirst (x:=x) (y:=y) (z:=z) e t => (∀ f, f∈triangle e.label ↔ f=x ∨ f=y ∨ f=z) ∧ t.records
  | .keepSecond (x:=x) (y:=y) (z:=z) e t => (∀ f, f∈triangle e.label ↔ f=y ∨ f=x ∨ f=z) ∧ t.records

theorem Trace.moves_count {x y a b} (t : Trace G x y a b) : t.moves.length=t.triangles.length := by
  induction t <;> simp_all [moves,triangles]

private theorem edge_not_loop (hh : 3≤h) {e : Edge M} {x y : Face M} (E : Across (dual G) e x y) : x≠y := by
  have ne := left_ne_right G hh e
  rcases E with eq|eq <;> rw [eq] at ne <;> first | exact ne | exact ne.symm

theorem apex_link_of_facial_pair (hh : 3≤h) {x y : Face M} {t : Fin M.ord}
    (xo : x≠apex M) (yo : y≠apex M) (xy : x≠y)
    (ap : apex M∈triangle t) (xp : x∈triangle t) (yp : y∈triangle t) :
    OnCycle (dualRow G (apex M)) x y := by
  obtain ⟨a,b,C,_,_,_,marks⟩ := corners_at G hh ((mem_triangle _ _).1 ap)
  have X := (marks x).1 ((mem_triangle _ _).1 xp)
  have Y := (marks y).1 ((mem_triangle _ _).1 yp)
  rcases X with eq|rfl|rfl <;> rcases Y with eq'|e|e <;>
    first | contradiction | exact .inl (e ▸ C.step) | exact .inr (e ▸ C.step) | grind [OnCycle]

noncomputable def sideOf (P : SeamState G) := vertexSide P.cut P.side

private theorem picked {P : SeamState G} (s : Side) (v : Fin M.ord) :
    vertexSide (P.pick s).cut P.side v=sideOf P v := by cases s <;> rfl

private theorem step_info (hh : 3≤h) {P Q : SeamState G} {s} (A : SeamStep P Q s) :
    ∃ edge : RimEdge G (P.pick s).y Q.y,
      (∀ f, f∈triangle edge.label ↔ f=Q.x ∨ f=(P.pick s).y ∨ f=Q.y) ∧
      sideOf P edge.label=false ∧ sideOf Q edge.label=true ∧
      ∀ v, apex M∉triangle v → sideOf P v=true → sideOf Q v=true := by
  obtain ⟨ret,ne,t,o,tr,ap,old,new⟩ := A
  rcases Q with ⟨x,z,T,d⟩
  change (P.pick s).x=x at ret; subst x
  let U := P.pick s
  have tx := (tr U.x).2 (Or.inl rfl); have ty := (tr U.y).2 (Or.inr (.inl rfl))
  have tz := (tr z).2 (Or.inr (.inr rfl))
  have ow := (ap _).2 (Or.inl rfl); have oy := (ap U.y).2 (Or.inr (.inl rfl)); have oz := (ap z).2 (Or.inr (.inr rfl))
  have yw : U.y≠apex M := edge_not_loop hh U.cut.last
  have xw : apex M≠U.x := edge_not_loop hh U.cut.first
  have zw : z≠apex M := edge_not_loop hh T.last
  have out : apex M∉triangle t := fun m => ((tr _).1 m).elim xw (fun disj=>disj.elim (Ne.symm yw) (Ne.symm zw))
  let edge : RimEdge G U.y z := ⟨t,apex_link_of_facial_pair hh yw zw ne ow oy oz,out,ty,tz⟩
  refine ⟨edge,tr,(picked s t) ▸ old,new,?_⟩
  intro v off was
  have eff := advance_sides hh U.cut T P.side d ne tr ap old new v
  have notO : v≠o := fun eq => off (eq ▸ ow)
  have notT : v≠t := fun eq => by have no := (picked s t) ▸ old; subst v; exact Bool.noConfusion (no.symm.trans was)
  change vertexSide T d v=true
  rw [eff]; simp only [notT,notO,or_self,ite_false]; simpa [U,picked] using was

/-- The face changes defining the load trace force its middle triangles
to be distinct. Once crossed, a nonapical middle triangle stays on the
traversed side of every following seam. -/
theorem extract_trace (hh : 3≤h) {P Q : SeamState G} {moves}
    (path : ActualTrace P moves Q) :
    ∃ geom : Trace G P.x P.y Q.x Q.y, geom.moves=moves ∧ geom.records ∧ geom.triangles.Nodup ∧
      (∀ v∈geom.triangles, apex M∉triangle v ∧ sideOf P v=false ∧ sideOf Q v=true) ∧
      (∀ v, apex M∉triangle v → sideOf P v=true → sideOf Q v=true) := by
  induction path with
  | done P => exact ⟨.done _ _,rfl,trivial,.nil,by simp [Trace.triangles],fun _ _ p=>p⟩
  | @next P T Q s ss step _ ih =>
    obtain ⟨tail,moves,verified,nd,colors,mono⟩ := ih
    obtain ⟨edge,tr,old,new,grow⟩ := step_info hh step
    obtain ⟨ret,_,_⟩ := step
    have dis : edge.label∉tail.triangles := fun m=>Bool.noConfusion ((colors _ m).2.1.symm.trans new)
    have info : ∀ v∈edge.label::tail.triangles, apex M∉triangle v ∧ sideOf P v=false ∧ sideOf Q v=true := by
      intro v m;rcases List.mem_cons.mp m with rfl|m
      · exact ⟨edge.nonapex,old,mono _ edge.nonapex new⟩
      · obtain ⟨off,cold,cnew⟩ := colors _ m
        refine ⟨off,?_,cnew⟩
        cases val : sideOf P v with
        | false => rfl
        | true => exact False.elim (Bool.noConfusion (cold.symm.trans (grow _ off val)))
    have mg := fun v vr vp => mono v vr (grow v vr vp)
    rcases P with ⟨x,y,S,b⟩;rcases T with ⟨k,z,U,d⟩
    cases s with
    | left =>
      change x=k at ret;subst k
      exact ⟨.keepFirst edge tail,(by change Side.left::tail.moves=Side.left::ss; rw [moves]),⟨tr,verified⟩,List.nodup_cons.mpr ⟨dis,nd⟩,info,mg⟩
    | right =>
      change y=k at ret;subst k
      exact ⟨.keepSecond edge tail,(by change Side.right::tail.moves=Side.right::ss; rw [moves]),⟨tr,verified⟩,List.nodup_cons.mpr ⟨dis,nd⟩,info,mg⟩

end DiskFullerene.StripFresh
