import DiskFullerene.MiddlePath
import DiskFullerene.StripTrace

namespace DiskFullerene.MiddlePath
open Dual EndLabels EndEuler Separation Strip

/-- An oriented seam on the proper-chord path, with its preceding triangle
in the selected half of the primal cut. -/
structure Record {M} {G : IsDiskFullerene M h} (P : SeamState G) (u v : Fin M.ord) : Prop where
  crosses : Across (primal G) P.cut.xy u v
  proper : Proper G P.cut.xy
  selected : vertexSide P.cut P.side u=true

private theorem record_off {M} {G : IsDiskFullerene M h} {P : SeamState G} {u v : Fin M.ord}
    (L : Record P u v) : vertexSide P.cut P.side v=false := by
  classical
  have split := (P.cut.part.crosses P.cut.xy).mp (Or.inr (Or.inl rfl))
  have differ : ¬(P.cut.part.left u ↔ P.cut.part.left v) := by
    rcases L.crosses with eq|eq <;> rw [eq] at split; exact split; exact fun e=>split e.symm
  have s := L.selected
  cases eq : P.side <;> by_cases U : P.cut.part.left u <;> by_cases V : P.cut.part.left v <;> simp_all [vertexSide]

private theorem across_ne {M} (G : IsDiskFullerene M h) (hh : 3≤h) {e a b} (H : Across (dual G) e a b) : a≠b := by
  have ne := left_ne_right G hh e
  rcases H with eq|eq <;> rw [eq] at ne; exact ne; exact ne.symm

private theorem across_ends {V E : Type} {D : E→V×V} {k : E} {x y a b : V}
    (A : Across D k x y) (B : Across D k a b) : (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by
  rcases A with eq|eq <;> rcases B with z|z <;> have pair := Prod.mk.inj (z.symm.trans eq) <;> grind

private theorem across_row {M} (G : IsDiskFullerene M h) {e a b} (H : Across (dual G) e a b) : b∈dualRow G a := by
  have base : (dual G e).2∈dualRow G (dual G e).1 := (mem_row_iff _ _ _).mpr
    ⟨endpoints e,left_incident G (endpoints_mem e),left_incident G (dart_reverse G (endpoints_mem e))⟩
  rcases H with eq|eq <;> rw [eq] at base; exact base; exact (dual_adj_symmetric G ..).mp base

private theorem off_cycle {M} {G : IsDiskFullerene M h} {e x y} (proper : Proper G e) (D : Across (dual G) e x y) :
    ¬OnCycle (dualRow G (apex M)) x y := by
  obtain ⟨a,b,A,_,_,off⟩ := proper
  rcases across_ends A D with ⟨rfl,rfl⟩|⟨rfl,rfl⟩; exact off; exact fun m=>off m.symm

private theorem remaining {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u : Fin M.ord} {x y z : Face M}
    (X : x∈triangle u) (Y : y∈triangle u) (Z : z∈triangle u) (xy : x≠y) (xz : x≠z) (yz : y≠z) :
    ∀ i, i∈triangle u ↔ i=x ∨ i=y ∨ i=z := by
  obtain ⟨a,b,c,eq⟩ : ∃ a b c, triangle u=[a,b,c] := ⟨_,_,_,List.eq_getElem_of_length_eq_three _ (triangle_three G hh u)⟩
  intro i; simp [eq] at X Y Z ⊢; grind

private theorem apex_triangle {M} (G : IsDiskFullerene M h) {a b : Face M} (outer : OnCycle (dualRow G (apex M)) a b) :
    ∃ o : Fin M.ord, ∀ i, i∈triangle o ↔ i=apex M ∨ i=a ∨ i=b := by
  have one {x y : Face M} (e : (x,y)∈sides (dualRow G (apex M))) :
      ∃ o : Fin M.ord, ∀ i, i∈triangle o ↔ i=apex M ∨ i=x ∨ i=y := by
    obtain ⟨k,o,K,O,hit,all⟩ := cornerEdge G e
    obtain ⟨v,uv⟩ : ∃ v, Across (primal G) k o v := by
      rcases O with rfl|rfl; exact ⟨_,Or.inl rfl⟩; exact ⟨_,Or.inr rfl⟩
    have c := edge_corners G uv K
    exact ⟨o,fun i=>⟨fun m=>all i ((mem_triangle _ _).mp m),fun p=>by rcases p with rfl|rfl|rfl; exact (mem_triangle _ _).mpr hit; exact c.1; exact c.2.1⟩⟩
  rcases outer with a|b
  · exact one a
  · obtain ⟨o,yes⟩ := one b
    exact ⟨o,fun i=>(yes i).trans (or_congr_right or_comm)⟩

private theorem picked {M} {G : IsDiskFullerene M h} (P : SeamState G) (s : Side) (v : Fin M.ord) :
    vertexSide (P.pick s).cut P.side v=vertexSide P.cut P.side v := by cases s <;> rfl

private theorem prepare {M} (G : IsDiskFullerene M h) (hh : 3≤h) (cut : HasChord G) (six : M.hexagons=6)
    {P : SeamState G} {v t w : Fin M.ord} (prev : Record P v t) (pure : Pure G t)
    {e : Edge M} (pw : Across (primal G) e t w) (prop : Proper G e) {s : Side} {z : Face M}
    (newEdge : Across (dual G) e (P.pick s).x z) (fresh : (P.pick s).y≠z) :
    ∃ Q : SeamState G, SeamStep P Q s ∧ Record Q t w := by
  classical
  let R := P.pick s
  have oldDual : Across (dual G) P.cut.xy R.x R.y := by cases s; exact P.cut.middle; exact P.cut.middle.symm
  have both := edge_corners G prev.crosses oldDual
  have X := both.2.2.1; have Y := both.2.2.2
  have Z := (edge_corners G pw newEdge).2.1
  have xy := across_ne G hh oldDual; have xz := across_ne G hh newEdge
  have rim := middle_has_boundary_edge G hh cut six t X Y Z xy xz fresh (pure _ X) (pure _ Y) (pure _ Z)
  have oldOff := off_cycle prev.proper oldDual; have newOff := off_cycle prop newEdge
  have face : OnCycle (dualRow G (apex M)) R.y z :=
    (rim.resolve_left oldOff).resolve_right (fun eq=>newOff eq.symm)
  obtain ⟨o,cap⟩ := apex_triangle G face
  obtain ⟨T⟩ := hasSides G hh (pure _ X) (across_row G newEdge) ((dual_adj_symmetric G ..).mp (pure _ Z))
  have eq := uniqueAcross G hh T.middle newEdge
  let Q : SeamState G := ⟨R.x,z,T,decide (T.part.left t)⟩
  have new : vertexSide Q.cut Q.side t=true := by simp [Q,vertexSide]
  have old : vertexSide R.cut P.side t=false := by rw [show vertexSide R.cut P.side t=vertexSide P.cut P.side t from picked P s t]; exact record_off prev
  exact ⟨Q,⟨rfl,fresh,t,o,remaining G hh X Y Z xy xz fresh,cap,old,new⟩,
    ⟨by change Across (primal G) T.xy t w; rwa [eq],by change Proper G T.xy; rwa [eq],new⟩⟩

private theorem step {M} (G : IsDiskFullerene M h) (hh : 3≤h) (cut : HasChord G) (six : M.hexagons=6)
    {P : SeamState G} {v t w : Fin M.ord} (prev : Record P v t) (pure : Pure G t)
    (forward : Crossing G t w) (distinct : v≠w) : ∃ s Q, SeamStep P Q s ∧ Record Q t w := by
  obtain ⟨e,pw,prop⟩ := forward
  obtain ⟨a,b,ed,_,_,_⟩ := (show Proper G e from prop)
  have neq : P.cut.xy≠e := by
    rintro eq; have A := prev.crosses; rw [eq] at A
    have endpoints := across_ends A pw
    grind
  have old := edge_corners G prev.crosses P.cut.middle; have new := edge_corners G pw ed
  have xIn := old.2.2.1; have yIn := old.2.2.2; have aIn := new.1; have bIn := new.2.1
  have xy := across_ne G hh P.cut.middle; have ab := across_ne G hh ed
  have first : ¬(a=P.x ∧ b=P.y) := by rintro ⟨rfl,rfl⟩; exact neq (uniqueAcross G hh P.cut.middle ed)
  have second : ¬(a=P.y ∧ b=P.x) := by rintro ⟨rfl,rfl⟩; exact neq (uniqueAcross G hh P.cut.middle ed.symm)
  have options : (a=P.x ∧ P.y≠b) ∨ (b=P.x ∧ P.y≠a) ∨ (a=P.y ∧ P.x≠b) ∨ (b=P.y ∧ P.x≠a) := by
    obtain ⟨x,y,z,eq⟩ : ∃ x y z, triangle t=[x,y,z] := ⟨_,_,_,List.eq_getElem_of_length_eq_three _ (triangle_three G hh t)⟩
    simp [eq] at xIn yIn aIn bIn; grind
  rcases options with ⟨ax,f⟩|⟨bx,f⟩|⟨ay,f⟩|⟨by',f⟩
  · exact ⟨.left,prepare G hh cut six prev pure pw prop (s:=.left) (show Across (dual G) e P.x b from ax ▸ ed) f⟩
  · exact ⟨.left,prepare G hh cut six prev pure pw prop (s:=.left) (show Across (dual G) e P.x a from bx ▸ ed.symm) f⟩
  · exact ⟨.right,prepare G hh cut six prev pure pw prop (s:=.right) (show Across (dual G) e P.y b from ay ▸ ed) f⟩
  · exact ⟨.right,prepare G hh cut six prev pure pw prop (s:=.right) (show Across (dual G) e P.y a from by' ▸ ed.symm) f⟩

private theorem follow {M} (G : IsDiskFullerene M h) (hh : 3≤h) (cut : HasChord G) (six : M.hexagons=6)
    (middle : List (Fin M.ord)) (u r : Fin M.ord) (P : SeamState G)
    (rec : Record P u (middle.headD r)) (nd : (u::middle++[r]).Nodup)
    (line : SpineWalk.Follows (Crossing G) (u::middle++[r])) (pure : ∀t∈middle, Pure G t) :
    ∃ Q moves, ActualTrace P moves Q ∧ moves.length=middle.length ∧ ∃ v, Record Q v r := by
  induction middle generalizing u P with
  | nil => exact ⟨P,[],.done _,rfl,u,rec⟩
  | cons t ts ih =>
    let v := ts.headD r
    have next : Crossing G t v := line t v (by cases ts <;> simp [v,SpineWalk.steps])
    have ne : u≠v := by
      have nv := (List.nodup_cons.mp nd).1
      cases ts <;> simp_all [v]
    obtain ⟨s,Q,T,recQ⟩ := step G hh cut six rec (pure t (by simp)) next ne
    have keep : SpineWalk.Follows (Crossing G) (t::ts++[r]) := fun a b edge=>line a b (List.mem_cons_of_mem _ edge)
    obtain ⟨Z,rest,walk,len,w,R⟩ := ih t Q recQ (List.nodup_cons.mp nd).2 keep (fun y h=>pure y (List.mem_cons_of_mem _ h))
    exact ⟨Z,s::rest,.next T walk,by simp [len],w,R⟩

private theorem mark_agreement {M} {G : IsDiskFullerene M h} {P Q : SeamState G}
    (same : P.cut.xy=Q.cut.xy) : (P.x=Q.x ∧ P.y=Q.y) ∨ (P.x=Q.y ∧ P.y=Q.x) :=
  across_ends Q.cut.middle (same ▸ P.cut.middle)

private theorem edge_agreement {M} {G : IsDiskFullerene M h} (hh : 3≤h) {P Q : SeamState G}
    (same : P.cut.xy=Q.cut.xy) : ThreeEdges P.cut.wx P.cut.xy P.cut.yw=ThreeEdges Q.cut.wx Q.cut.xy Q.cut.yw := by
  have changeX {e : Edge M} {a b x : Face M} (eq : a=b) (old : Across (dual G) e a x) : Across (dual G) e b x := eq ▸ old
  have changeY {e : Edge M} {a b x : Face M} (eq : a=b) (old : Across (dual G) e x a) : Across (dual G) e x b := eq ▸ old
  rcases mark_agreement same with ⟨xx,yy⟩|⟨xy,yx⟩
  · have x := uniqueAcross G hh (changeY xx P.cut.first) Q.cut.first
    have y := uniqueAcross G hh (changeX yy P.cut.last) Q.cut.last
    rw [same,x,y]
  · have x := uniqueAcross G hh (changeY xy P.cut.first) Q.cut.last.symm
    have y := uniqueAcross G hh (changeX yx P.cut.last) Q.cut.first.symm
    funext t; apply propext; simp [ThreeEdges,same,x,y,or_comm,or_left_comm]

private theorem same_at {M} {G : IsDiskFullerene M h} (P : SeamState G) (v w : Fin M.ord) :
    (vertexSide P.cut P.side v=vertexSide P.cut P.side w) ↔ (P.cut.part.left v ↔ P.cut.part.left w) := by
  classical
  by_cases a : P.cut.part.left v <;> by_cases b : P.cut.part.left w <;> cases P.side <;> simp_all [vertexSide]

/-- Two cuts on the same actual chord have the same two components.
Selecting opposite sides at one reference triangle fixes the sign globally. -/
theorem complementary_masks {M} {G : IsDiskFullerene M h} (hh : 3≤h) {P Q : SeamState G}
    (same : P.cut.xy=Q.cut.xy) {v : Fin M.ord}
    (opposite : vertexSide P.cut P.side v ≠ vertexSide Q.cut Q.side v) (w : Fin M.ord) :
    vertexSide P.cut (!P.side) w = vertexSide Q.cut Q.side w := by
  classical
  have masks : (vertexSide P.cut P.side v=vertexSide P.cut P.side w) ↔ (vertexSide Q.cut Q.side v=vertexSide Q.cut Q.side w) := by
    rw [same_at,same_at,P.cut.part.components,Q.cut.part.components,edge_agreement hh same]
  have neg : vertexSide P.cut (!P.side) w = !vertexSide P.cut P.side w := by
    cases P.side <;> by_cases yes : P.cut.part.left w <;> simp_all [vertexSide]
  rw [neg]
  cases h₁ : vertexSide P.cut P.side v <;> cases h₂ : vertexSide Q.cut Q.side v <;>
    cases h₃ : vertexSide P.cut P.side w <;> cases h₄ : vertexSide Q.cut Q.side w <;> simp_all

/-- For either orientation of the initial cap seam, the actual ordered
triangles give a legal geometric trace. The final untraversed side is
exactly the prescribed second cap, with its two seam endpoints identified. -/
theorem actual_trace {M} (G : IsDiskFullerene M h) (hh : 3≤h) (cut : HasChord G) (six : M.hexagons=6)
    (O : Ordered G) (P : SeamState G) (beginEdge : P.cut.xy=O.leftEnd.seam.xy)
    (beginSide : vertexSide P.cut P.side O.left=true) :
    ∃ Q moves, ActualTrace P moves Q ∧ moves.length=O.path.middle.length ∧
      Q.cut.xy=O.rightEnd.seam.xy ∧
      ((Q.x=atSide G (apex M) O.rightEnd.i ∧ Q.y=atSide G (apex M) O.rightEnd.j) ∨
       (Q.x=atSide G (apex M) O.rightEnd.j ∧ Q.y=atSide G (apex M) O.rightEnd.i)) ∧
      ∀ w, vertexSide Q.cut (!Q.side) w=vertexSide O.rightEnd.seam O.rightEnd.side w := by
  let mid := O.path.middle
  have source : Crossing G O.left (mid.headD O.right) := by
    apply O.path.chain
    change (_,mid.headD O.right)∈SpineWalk.steps (O.left::mid++[O.right]); cases mid <;> simp [SpineWalk.steps]
  obtain ⟨e,uv,pr⟩ := source
  have matchEdge := (only_seam_at hh O.leftEnd O.leftRoot.2 uv pr).trans beginEdge.symm
  have start : Record P O.left (mid.headD O.right) := ⟨matchEdge ▸ uv,matchEdge ▸ pr,beginSide⟩
  obtain ⟨Q,moves,trace,len,v,finalRec⟩ := follow G hh cut six mid O.left O.right P start O.path.simple O.path.chain (fun t h=>(O.pure_iff t).mp h)
  have matchFinal := only_seam_at hh O.rightEnd O.rightRoot.2 finalRec.crosses.symm finalRec.proper
  let T : SeamState G := ⟨_,_,O.rightEnd.seam,O.rightEnd.side⟩
  have eq : Q.cut.xy=T.cut.xy := matchFinal
  have diff : vertexSide Q.cut Q.side O.right≠vertexSide T.cut T.side O.right := by
    rw [record_off finalRec]; intro bad; exact Bool.false_ne_true (bad.trans O.rightRoot.2)
  exact ⟨Q,moves,trace,len,matchFinal,mark_agreement (P:=Q) (Q:=T) eq,complementary_masks hh eq diff⟩

end DiskFullerene.MiddlePath
