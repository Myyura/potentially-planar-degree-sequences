import DiskFullerene.TerminalBoundary
import DiskFullerene.InteriorTriangles

namespace DiskFullerene.Dual
open Separation EndEuler

/-- The primal vertex and third edge at a corner in an actual dual row. -/
theorem cornerEdge {M} (G : IsDiskFullerene M h) {i x y : Face M}
    (step : (x,y) ∈ sides (dualRow G i)) :
    ∃ (e : Edge M) (t : Fin M.ord), Across (dual G) e x y ∧
      (t=(primal G e).1 ∨ t=(primal G e).2) ∧ t.val∈M.faces[i.val] ∧
      ∀ k : Face M, t.val∈M.faces[k.val] → k=i ∨ k=x ∨ k=y := by
  let ds := sides M.faces[i.val]
  obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp step
  rw [sides_size] at hn
  rw [side_at _ _ hn] at eq
  have hp : n < ds.length := by simpa [dualRow, ds] using hn
  let m := next ds.length n
  have hq : m < ds.length := next_bound hp
  have pair : (ds[n],ds[m]) ∈ sides ds := List.mem_iff_getElem.mpr
    ⟨n,by simpa [sides_size] using hp,side_at ds n hp⟩
  have ok := List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem i.isLt)
  have good := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 _ pair
  obtain ⟨u,v,ea⟩ : ∃ u v, ds[n] = (u,v) := ⟨_,_,rfl⟩
  obtain ⟨v',w,eb⟩ : ∃ v' w, ds[m] = (v',w) := ⟨_,_,rfl⟩
  have tt : M.turn (u,v) = (v',w) := by simpa [ea,eb] using good
  have eqv : v = v' := congrArg Prod.fst tt
  subst v'
  have ha : incident M i (u,v) := ea ▸ List.getElem_mem hp
  have hb : incident M i (v,w) := eb ▸ List.getElem_mem hq
  simp only [dualRow, List.length_map, List.getElem_map] at eq
  change (owner G ds[n].swap, owner G ds[m].swap) = _ at eq
  simp [ea, eb] at eq
  rcases eq with ⟨rfl,rfl⟩
  obtain ⟨z,_,t2,t3⟩ := cubic_corner G ha tt
  have ina := reverse_owner G ha
  have inb := reverse_owner G hb
  have outb : incident M (owner G (w,v)) (v,z) := t2 ▸ incident_turn G inb
  obtain ⟨l,il,_⟩ := dart_has_face G (dart_reverse G (incident_dart G outb))
  have lu : incident M l (v,u) := t3 ▸ incident_turn G il
  have same : l = owner G (v,u) := face_indices_unique G lu ina
  have za : incident M (owner G (v,u)) (z,v) := same ▸ il
  obtain ⟨edge,orient⟩ := repr_dart G (incident_dart G za)
  have cross := crossTable G orient (Or.inl ⟨za,outb⟩)
  let t : Fin M.ord := ⟨v,(dart_info G (incident_dart G hb)).1⟩
  refine ⟨edge,t,cross,?_,(sideEnds hb).1,fun k hv => three_at_corner G ha tt hv⟩
  rcases orient with eq|eq
  · exact Or.inr (Fin.ext (congrArg Prod.snd eq).symm)
  · exact Or.inl (Fin.ext (congrArg Prod.fst eq).symm)

private theorem coreInfo {M} {G : IsDiskFullerene M h} {x y}
    (S : TriangleSide G (apex M) x y) {B f} (h : sectorCore S B f=true) :
    f ∈ diskInterior G ∧ faceSide S B f=true := by
  classical
  have ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true a,b⟩

theorem core_corner_selected {M} {G : IsDiskFullerene M h} {x y}
    (S : TriangleSide G (apex M) x y) {B f} (active : sectorCore S B f=true)
    (t : Fin M.ord) (touch : t.val∈M.faces[f.val]) : vertexSide S B t=true := by
  classical
  have hs := (coreInfo S active).2
  obtain ⟨neq,fs⟩ := Bool.and_eq_true_iff.mp hs
  have good : f≠apex M ∧ f≠x ∧ f≠y := of_decide_eq_true neq
  have c := S.color_at good touch
  have cf : S.color t.val ↔ S.part.left t :=
    ⟨fun ⟨_,k⟩ => k,fun k => ⟨t.isLt,k⟩⟩
  change (decide (S.faceColor f) == B)=true at fs
  simpa [vertexSide,← cf,← c] using fs

theorem core_frontier {M} {G : IsDiskFullerene M h} {x y}
    (S : TriangleSide G (apex M) x y) {B u v} (inside : sectorCore S B u=true)
    (outside : sectorCore S B v=false) (adj : v∈dualRow G u) : IsBoundary G v := by
  classical
  have inf := (coreInfo S inside).1
  have hr := (mem_diskInterior G u).mp inf
  have nv : v≠apex M := fun eq => hr.2 ((dual_adj_symmetric G _ _).mp (eq ▸ adj))
  apply Classical.byContradiction; intro no
  have vi := (mem_diskInterior G v).mpr ⟨nv,no⟩
  have source (e : Edge M) (a b : Face M) (E : Across (dual G) e a b) : b∈dualRow G a := by
    have base : (dual G e).2∈dualRow G (dual G e).1 :=
      (mem_row_iff _ _ _).mpr ⟨endpoints e,left_incident G (endpoints_mem e),left_incident G (dart_reverse G (endpoints_mem e))⟩
    rcases E with q|q <;> rw [q] at base
    · exact base
    · exact (dual_adj_symmetric G _ _).mp base
  have n (i) (hi : i∈diskInterior G) : i≠apex M ∧ i≠x ∧ i≠y := by
    have ⟨other,notB⟩ := (mem_diskInterior G i).mp hi
    exact ⟨other,fun eq => notB (eq ▸ source _ _ _ S.first),fun eq => notB (eq ▸ source _ _ _ S.last.symm)⟩
  have eq := S.edge_stays (n _ inf) (n _ vi) adj
  simp [sectorCore,faceSide,inf,vi,n _ inf,n _ vi,eq] at inside outside
  grind


/-- A run of three outside neighbors meets the unique selected primal
endpoint of the seam. Every other face there is one of its two marks. -/
theorem terminal_run {M} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) (P : TerminalHalf G (vertexSide S B))
    {u a b c : Face M} (hu : sectorCore S B u=true) (ac : a≠c)
    (na : sectorCore S B a=false) (nb : sectorCore S B b=false) (nc : sectorCore S B c=false)
    (one : (a,b)∈sides (dualRow G u)) (two : (b,c)∈sides (dualRow G u)) :
    (b=x ∨ b=y) ∧ ∃ v : Fin M.ord,
      (v=(primal G S.xy).1 ∨ v=(primal G S.xy).2) ∧ vertexSide S B v=true ∧
      v.val∈M.faces[u.val] ∧ ∀ z : Face M, v.val∈M.faces[z.val] → z=u ∨ z=x ∨ z=y := by
  have inRow {a b : Face M} (h : (a,b)∈sides (dualRow G u)) :
      a∈dualRow G u ∧ b∈dualRow G u := by
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
    rw [sides_size] at hi
    rw [side_at _ _ hi] at eq
    rcases Prod.mk.inj eq with ⟨rfl,rfl⟩
    exact ⟨List.getElem_mem hi,List.getElem_mem (next_bound hi)⟩
  have aC := core_frontier S hu na (inRow one).1
  have bC := core_frontier S hu nb (inRow one).2
  have cC := core_frontier S hu nc (inRow two).2
  have result {r t : Face M} (rC : IsBoundary G r) (tC : IsBoundary G t)
      (corner : (r,t)∈sides (dualRow G u)) :
      OnCycle (dualRow G (apex M)) r t ∨
      ((r=x ∧ t=y) ∨ (r=y ∧ t=x)) ∧ ∃ v : Fin M.ord,
        (v=(primal G S.xy).1 ∨ v=(primal G S.xy).2) ∧ vertexSide S B v=true ∧
        v.val∈M.faces[u.val] ∧ ∀ z : Face M, v.val∈M.faces[z.val] → z=u ∨ z=x ∨ z=y := by
    obtain ⟨e,v,E,ends,some,faces⟩ := cornerEdge G corner
    have vB := core_corner_selected S hu v some
    have selected : vertexSide S B (primal G e).1=true ∨ vertexSide S B (primal G e).2=true := by
      rcases ends with eq|eq
      · exact Or.inl (eq ▸ vB)
      · exact Or.inr (eq ▸ vB)
    rcases TerminalHalf.seam_or_cycle hh S B P rC tC E selected with cycle|seam
    · exact Or.inl cycle
    right; subst e
    have marks : (r=x ∧ t=y) ∨ (r=y ∧ t=x) := by
      rcases E with d|d <;> rcases S.middle with f|f <;> rw [d] at f <;> simp only [Prod.mk.injEq] at f <;> grind
    refine ⟨marks,v,ends,vB,some,?_⟩
    intro z hz; have := faces z hz; grind
  rcases result aC bC one with outer|⟨marks,v⟩
  · rcases result bC cC two with outer'|⟨marks,v⟩
    · exfalso
      have opp {i r s : Face M} (e : OnCycle (dualRow G i) r s) : OnCycle (dualRow G r) i s := by
        rcases e with f|f
        · exact Or.inr (turn_triangle G f).1
        · exact Or.inl (turn_triangle G f).2
      have distinct := (mem_diskInterior G u).1 (coreInfo S hu).1
      have deg := inner_degree G (show b≠apex M from fun eq => row_no_loop G hh _ (eq ▸ bC))
      have short := quadrilateral (row_nodup G (noRepeatOnSphere G hh) b) (by omega)
        (Ne.symm distinct.1) ac (opp outer.symm) (opp (Or.inr one : OnCycle (dualRow G u) b a)).symm
        (opp (Or.inl two : OnCycle (dualRow G u) b c)) (opp outer').symm ((dual_adj_symmetric G _ _).mp bC)
      omega
    · exact ⟨by grind,v⟩
  · exact ⟨by grind,v⟩

def BoundaryRun {M} (G : IsDiskFullerene M h) (A : Face M → Bool) (u : Face M) :=
  ∃ a b c, a≠c ∧ A a=false ∧ A b=false ∧ A c=false ∧
    (a,b)∈sides (dualRow G u) ∧ (b,c)∈sides (dualRow G u)

/-- All the long runs in a terminal sector are at one inner vertex. -/
theorem terminal_single_run {M} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) (P : TerminalHalf G (vertexSide S B)) :
    ∃ z : Face M, ∀ u, sectorCore S B u=true → BoundaryRun G (sectorCore S B) u → u=z := by
  classical
  by_cases existsRun : ∃ z, sectorCore S B z=true ∧ BoundaryRun G (sectorCore S B) z
  · obtain ⟨z,hz,R⟩ := existsRun
    have witness {q} (hq : sectorCore S B q=true) (run : BoundaryRun G (sectorCore S B) q) :
        ∃ v : Fin M.ord, (v=(primal G S.xy).1 ∨ v=(primal G S.xy).2) ∧ vertexSide S B v=true ∧
          v.val∈M.faces[q.val] ∧ ∀ z : Face M, v.val∈M.faces[z.val] → z=q ∨ z=x ∨ z=y := by
      obtain ⟨a,b,c,ac,ha,hb,hc,A,C⟩ := run
      exact (terminal_run hh S B P hq ac ha hb hc A C).2
    obtain ⟨v,ev,vp,_,all⟩ := witness hz R
    refine ⟨z,fun u hu run => ?_⟩
    obtain ⟨w,ew,wp,wu,_⟩ := witness hu run
    have cut := (S.part.crosses S.xy).mp (Or.inr (Or.inl rfl))
    have uniq : w=v := by
      have left {i : Fin M.ord} (p : vertexSide S B i=true) : S.part.left i ↔ B=true := by
        cases B <;> simp_all [vertexSide]
      have same := (left wp).trans (left vp).symm
      rcases ew with eq|eq <;> rcases ev with eq'|eq' <;> rw [eq,eq'] at same ⊢ <;> grind
    have poss := all u (uniq ▸ wu)
    have h := (coreInfo S hu).2
    have neq := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    change u≠apex M ∧ u≠x ∧ u≠y at neq
    grind
  · exact ⟨apex M,fun u hu run => False.elim (existsRun ⟨u,hu,run⟩)⟩

theorem terminal_nonisolated {M} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) (P : TerminalHalf G (vertexSide S B))
    {u} (hu : sectorCore S B u=true) : ∃ v∈dualRow G u, sectorCore S B v=true := by
  classical
  apply Classical.byContradiction; intro no
  have off (v) (adj : v∈dualRow G u) : sectorCore S B v=false := by
    cases eq : sectorCore S B v
    · rfl
    · exact False.elim (no ⟨v,adj,eq⟩)
  have deg := inner_degree G ((mem_diskInterior G u).mp (coreInfo S hu).1).1
  have nd := row_nodup G (noRepeatOnSphere G hh) u
  have subset : dualRow G u ⊆ [x,y] := by
    intro b hb
    obtain ⟨a,ha,c,hc,ac,one,two,_⟩ := cycle_at nd (by omega) hb
    have marks := (terminal_run hh S B P hu ac (off a ha) (off b hb) (off c hc) one two).1
    simpa using marks
  have size := nd.length_le_of_subset subset
  simp only [List.length_cons,List.length_nil] at size
  omega

end DiskFullerene.Dual
