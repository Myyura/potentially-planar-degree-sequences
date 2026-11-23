import DiskFullerene.SixLabels
import DiskFullerene.SixRuns

namespace DiskFullerene.SixLabels
open Dual EndEuler Separation SixTable EndSix
open EndLabels (items selected label decode_label label_decode)

private theorem sizeItems {n} (A : Fin n → Bool) : (items A).length = num A :=
  (List.countP_eq_length_filter ..).symm

noncomputable def lookup {M} (A : Face M → Bool) (i : Nat) := ((items A)[i]?).getD (apex M)

private theorem lookup_ok {M} {A : Face M → Bool} (six : num A=6) {i : Nat} (hi : i∈labels) :
    (items A)[i]?=some (lookup A i) := by
  have h : i < (items A).length := by rw [sizeItems,six]; exact (in_labels i).mp hi
  simp [lookup,List.getElem?_eq_getElem h]

private theorem lookup_injective {M} {A : Face M → Bool} (six : num A=6) {i j : Nat}
    (hi : i∈labels) (hj : j∈labels) (eq : lookup A i=lookup A j) : i=j :=
  (label_decode (lookup_ok six hi)).2.symm.trans ((congrArg (label A) eq).trans (label_decode (lookup_ok six hj)).2)

private theorem lookup_edge {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (six : num A=6) {i j : Nat} (hi : i∈labels) (hj : j∈labels) :
    adjacent (graph G A) i j=true ↔ lookup A j∈dualRow G (lookup A i) := by
  rw [edge_iff G hh A ((in_labels _).mp hi) ((in_labels _).mp hj),lookup_ok six hi,lookup_ok six hj]; simp

private theorem subsets_sublist {α} {xs ys : List α} (mem : ys∈EndGeometry.subsets xs) : ys.Sublist xs := by
  induction xs generalizing ys with
  | nil => simp [EndGeometry.subsets] at mem; subst ys; exact .slnil
  | cons a xs ih =>
    simp only [EndGeometry.subsets,List.mem_append,List.mem_map] at mem
    rcases mem with h|⟨zs,h,rfl⟩
    · exact (ih h).cons a
    · exact (ih h).cons_cons a

private theorem max_mem {α} (p : α→Nat) {xs : List α} (ne : xs≠[]) : ∃ v∈xs, ∀ u∈xs, p u≤p v := by
  induction xs with
  | nil => exact (ne rfl).elim
  | cons a as ih =>
    by_cases empty : as=[]
    · subst as; exact ⟨a,by simp,by simp⟩
    obtain ⟨v,hv,big⟩ := ih empty
    by_cases h : p a≤p v
    · exact ⟨v,by simp [hv],fun u hu => (List.mem_cons.mp hu).elim (fun eq => eq ▸ h) (big u)⟩
    · exact ⟨a,by simp,fun u hu => (List.mem_cons.mp hu).elim (fun eq => eq ▸ Nat.le_refl _) (fun m => by have := big u m; omega)⟩

private theorem noClosed {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool} (six : num A=6)
    (exposed : ∀ c∈items A, ∃ z∈dualRow G c, z∉items A)
    (conn : ∀ x∉items A, ∀ y∉items A, OutsideWalk G (items A) x y)
    (i : Nat) (hi : i∈labels) : closedLink (graph G A) i=false := by
  apply List.any_eq_false.mpr; intro s hs
  intro yes
  obtain ⟨nonempty,all⟩ := Bool.and_eq_true_iff.mp yes
  have ne : s≠[] := by intro e; simp [e] at nonempty
  have sub := subsets_sublist hs
  let L := graph G A
  have nei (x) (hx : x∈s) : x∈labels ∧ adjacent L i x=true := List.mem_filter.mp (sub.subset hx)
  have within (x) (hx : x∈labels) : lookup A x∈items A := selected.mpr (label_decode (lookup_ok six hx)).1
  obtain ⟨rank,unique,step⟩ := openOrder G hh (items A) exposed conn (lookup A i) (within i hi)
  have main (x) (hx : x∈s) : lookup A x ∈ dualRow G (lookup A i) := (lookup_edge G hh six hi (nei x hx).1).mp (nei x hx).2
  obtain ⟨v,hv,maximal⟩ := max_mem (fun x => rank (lookup A x)) ne
  have size : 2≤(s.filter (adjacent L v)).length := by simpa using List.all_eq_true.mp all v hv
  have small {u} (hu : u∈s.filter (adjacent L v)) : rank (lookup A u)+1=rank (lookup A v) := by
    obtain ⟨us,edge⟩ := List.mem_filter.mp hu
    have z := step _ (main v hv) (within _ (nei _ hv).1) _ (main u us) (within _ (nei _ us).1)
      ((lookup_edge G hh six (nei _ hv).1 (nei _ us).1).mp edge)
    have m := maximal u us
    omega
  have dn : (s.filter (adjacent L v)).Nodup := (List.Nodup.sublist sub ((show labels.Nodup by decide).filter _)).filter _
  cases eq : s.filter (adjacent L v) with
  | nil => simp [eq] at size
  | cons a tail =>
    cases tail with
    | nil => simp [eq] at size
    | cons b as =>
      have ha : a∈s.filter (adjacent L v) := by simp [eq]
      have hb : b∈s.filter (adjacent L v) := by simp [eq]
      have as' := (List.mem_filter.mp ha).1; have bs' := (List.mem_filter.mp hb).1
      have ab := unique _ (main a as') _ (main b bs') (by have := small ha; have := small hb; omega)
      have same := lookup_injective six (nei _ as').1 (nei _ bs').1 ab
      subst b; simp [eq] at dn

/-- A terminal half is one source of a connected complementary vertex set.
The connectivity data here agree with the Euler API for arbitrary masks. -/
theorem outside_walks {M} (G : IsDiskFullerene M h) {A : Face M → Bool}
    (conn : ∀ z, A z=false → Walk (Adj (dual G) (fun t=>sideEdge (dual G) (fun i=> !A i) t=true)) (apex M) z) :
    ∀ x∉items A, ∀ y∉items A, OutsideWalk G (items A) x y := by
  have path (z) (hz : z∉items A) : OutsideWalk G (items A) (apex M) z := by
    have out : A z=false := by cases eq : A z <;> simp_all
    have W := conn z out
    induction W with
    | refl => exact .refl
    | @step b c trail edge ih =>
      obtain ⟨e,ok,cut⟩ := edge
      have base : (dual G e).2∈dualRow G (dual G e).1 := (mem_row_iff _ _ _).mpr
        ⟨endpoints e,left_incident G (endpoints_mem e),left_incident G (dart_reverse G (endpoints_mem e))⟩
      rcases cut with eq|eq <;> rw [eq] at base <;> simp [sideEdge,eq] at ok
      · exact (ih (by simp [ok.1]) ok.1).step ⟨by simp [ok.1],by simp [ok.2],base⟩
      · exact (ih (by simp [ok.2]) ok.2).step ⟨by simp [ok.2],by simp [ok.1],(dual_adj_symmetric G ..).mp base⟩
  intro x nx y ny
  exact ((path x nx).symm (fun a b e => ⟨e.2.1,e.1,(dual_adj_symmetric G ..).mp e.2.2⟩)).trans (path y ny)

private theorem lookup_label {M} {A : Face M→Bool} {f : Face M} (hf : A f=true) :
    lookup A (label A f)=f := by simp [lookup,decode_label hf]

private theorem label_small {n} {A : Fin n→Bool} (six : num A=6) {f : Fin n} (hf : A f=true) :
    label A f∈labels := by
  apply (in_labels _).mpr
  have b := List.idxOf_lt_length_iff.mpr (selected.mpr hf)
  simpa [label,sizeItems,six] using b

private theorem ear_run {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool} (six : num A=6)
    (off : A (apex M)=false) (exposed : ∀ c∈items A, ∃ z∈dualRow G c, z∉items A)
    (conn : ∀ x∉items A, ∀ y∉items A, OutsideWalk G (items A) x y)
    (i : Nat) (hi : i∈labels) (ear : SixTable.ear (graph G A) i=true) : BoundaryRun G A (lookup A i) := by
  let L := graph G A
  have inside (w) (hw : w∈labels) : lookup A w∈items A := selected.mpr (label_decode (lookup_ok six hw)).1
  have info (w) (hw : w∈innerNeighbors L i) :
      w∈labels ∧ lookup A w ∈ dualRow G (lookup A i) := by
    have ⟨h,m⟩ := List.mem_filter.mp hw
    exact ⟨h,(lookup_edge G hh six hi h).mp m⟩
  have inrow {f : Face M} (mem : f∈dualRow G (lookup A i)) (fa : f∈items A) : label A f∈innerNeighbors L i := by
    have small := label_small six (selected.mp fa)
    exact List.mem_filter.mpr ⟨small,(lookup_edge G hh six hi small).mpr (by rwa [lookup_label (selected.mp fa)])⟩
  have exclude : apex M∉items A := by simp [off]
  change SixTable.ear L i=true at ear
  unfold SixTable.ear at ear
  split at ear
  next a row =>
    have ai := info a (by simp [row])
    apply run_of_ear G hh A (items A) (fun _=>selected) exclude exposed conn (inside i hi) (inside a ai.1) (inside a ai.1) ai.2 ai.2 (Or.inl rfl)
    intro z mz iz; have q := inrow mz iz; simp [row] at q
    exact Or.inl (q ▸ (lookup_label (selected.mp iz)).symm)
  next a b row =>
    have ai := info a (by simp [row]); have bi := info b (by simp [row])
    apply run_of_ear G hh A (items A) (fun _=>selected) exclude exposed conn (inside i hi) (inside a ai.1) (inside b bi.1) ai.2 bi.2 (Or.inr ((lookup_edge G hh six ai.1 bi.1).mp ear))
    intro z mz iz; have q := inrow mz iz; simp [row] at q
    rcases q with e|e
    · exact Or.inl (e ▸ (lookup_label (selected.mp iz)).symm)
    · exact Or.inr (e ▸ (lookup_label (selected.mp iz)).symm)
  next => contradiction

/-- The table parameter is discharged once for all maps in `SixCenter`. -/
theorem center_from_table {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (table : test (graph G A)=true) (six : num A=6) (off : A (apex M)=false)
    (nonisolated : ∀ f, A f=true → ∃ z∈dualRow G f, A z=true)
    (conn : ∀ z, A z=false → Walk (Adj (dual G) (fun t=>sideEdge (dual G) (fun i=> !A i) t=true)) (apex M) z)
    (singleton : ∃ z, ∀ f, A f=true → BoundaryRun G A f → f=z) :
    ∃ c, A c=true ∧ ∀ z∈dualRow G c, A z=true := by
  apply Classical.byContradiction; intro neg
  have exposed (c) (inside : c∈items A) : ∃ z∈dualRow G c, z∉items A := by
    apply Classical.byContradiction; intro bad
    exact neg ⟨c,selected.mp inside,fun z hz=>selected.mp (Classical.byContradiction (fun nz=>bad ⟨z,hz,nz⟩))⟩
  let L := graph G A
  have paths := outside_walks G conn
  have noLink : labels.any (closedLink L)=false := List.any_eq_false.mpr
    (fun i hi eq=>by rw [noClosed G hh six exposed paths i hi] at eq; contradiction)
  have noIsolated : labels.any (fun v=>(innerNeighbors L v).isEmpty)=false := by
    apply List.any_eq_false.mpr; intro i hi empty
    obtain ⟨f,hf,af⟩ := nonisolated _ (label_decode (lookup_ok six hi)).1
    have small := label_small six af
    have hit : label A f∈innerNeighbors L i := List.mem_filter.mpr ⟨small,(lookup_edge G hh six hi small).mpr (by rwa [lookup_label af])⟩
    have nil := List.isEmpty_iff.mp empty; simp [nil] at hit
  have chosen := (label_decode (lookup_ok six (show 0∈labels by decide))).1
  have Eu := induced_euler_bound G hh A off (nonsolid G hh A chosen) conn
  have E := edge_count G hh A
  have F := face_count G hh A (by omega)
  have notCount : ¬6+(triples.filter (clique L)).length < (pairs.filter (clique L)).length+1 := by
    change ¬6+(triples.filter (clique (graph G A))).length < (pairs.filter (clique (graph G A))).length+1; omega
  change test L=true at table
  simp only [test,noLink,noIsolated,notCount,decide_false,Bool.or_false,decide_eq_true_eq] at table
  obtain ⟨z,alone⟩ := singleton
  have uniquely {i} (m : i∈labels.filter (SixTable.ear L)) : lookup A i=z := by
    have h := List.mem_filter.mp m
    exact alone _ (label_decode (lookup_ok six h.1)).1 (ear_run G hh six off exposed paths i h.1 h.2)
  have sub : labels.filter (SixTable.ear L) ⊆ [label A z] := by
    intro i m
    have h := (List.mem_filter.mp m).1
    have equality := congrArg (label A) (uniquely m)
    have index := (label_decode (lookup_ok six h)).2
    simp [←equality,index]
  have nd : (labels.filter (SixTable.ear L)).Nodup := (show labels.Nodup by decide).filter _
  have upper := nd.length_le_of_subset sub
  simp at upper; omega

end DiskFullerene.SixLabels
