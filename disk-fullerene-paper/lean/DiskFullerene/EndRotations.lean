import DiskFullerene.EndLabels
import DiskFullerene.TerminalRuns

namespace DiskFullerene.EndLabels
open EndGeometry Lower Dual EndEuler Separation

theorem cycle_split {α} (p q : List α) : (sides (p++q)).Perm (sides (q++p)) := by
  cases p with
  | nil => simp
  | cons a as =>
    cases q with
    | nil => simp
    | cons b bs =>
      have split (a b : α) (as bs : List α) : sides ((a::as)++b::bs) =
          ((a::as).zip (as++[b])) ++ ((b::bs).zip (bs++[a])) := by
        change ((a::as)++b::bs).zip ((as++b::bs)++[a]) = _
        have eq : (as++b::bs)++[a] = (as++[b])++(bs++[a]) := by simp [List.append_assoc]
        rw [eq,List.zip_append (by simp)]
      rw [split,split]; exact List.perm_append_comm

private theorem sides_map {α β} (r : List α) (f : α→β) : sides (r.map f)=(sides r).map (Prod.map f f) := by
  cases r with
  | nil => rfl
  | cons a l => simp [sides,←List.zip_map]

private theorem side_ends {α} {r : List α} {a b : α} (e : (a,b)∈sides r) : a∈r ∧ b∈r := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp e; rw [sides_size] at hi; rw [side_at _ _ hi] at eq
  exact ⟨(Prod.mk.inj eq).1 ▸ List.getElem_mem _,(Prod.mk.inj eq).2 ▸ List.getElem_mem _⟩

private theorem side_consecutive {r : List Nat} (nd : r.Nodup) {a b} (e : (a,b)∈sides r ∨ (b,a)∈sides r) :
    consecutive r.length (r.idxOf a) (r.idxOf b) := by
  have fw {a b} (m : (a,b)∈sides r) : r.idxOf a+1=r.idxOf b ∨ r.idxOf a+1=r.length ∧ r.idxOf b=0 := by
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp m; rw [sides_size] at hi; rw [side_at _ _ hi] at eq
    cases eq
    simp only [List.Nodup.idxOf_getElem nd]; unfold next; split <;> omega
  unfold consecutive; rcases e with e|e <;> have h := fw e <;> omega

def tag {n} (A : Fin n→Bool) (q : Fin n) := if A q then label A q else 5+q.val

theorem smallTag {n} {A : Fin n→Bool} (sz : num A≤5) (q : Fin n) : tag A q<5 ↔ A q=true := by
  cases eq : A q <;> simp [tag,eq]; exact small_label sz eq

private theorem tagInj {n} {A : Fin n→Bool} (sz : num A≤5) (p q) (eq : tag A p=tag A q) : p=q := by
  have iff := (smallTag sz p).symm.trans (eq ▸ smallTag sz q)
  cases ap : A p <;> cases aq : A q <;> simp_all [tag]
  · exact Fin.ext eq
  · have f := decode_label ap; have g := decode_label aq; rw [eq] at f; exact Option.some.inj (f.symm.trans g)

private theorem outside_neighbor {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (sz : num A≤5) {q : Face M} (inQ : A q=true) (np : q≠apex M) : ∃ o∈dualRow G q, A o=false := by
  apply Classical.byContradiction; intro no
  have nd : (q::dualRow G q).Nodup := List.nodup_cons.mpr ⟨row_no_loop G hh q,row_nodup G (noRepeatOnSphere G hh) q⟩
  have sub : q::dualRow G q ⊆ items A := by
    intro r m; rcases List.mem_cons.mp m with rfl|m
    · exact selected.mpr inQ
    · cases e : A r with
      | false => exact False.elim (no ⟨r,m,e⟩)
      | true => exact selected.mpr e
  have ub := nd.length_le_of_subset sub
  have sz' : (items A).length=num A := (List.countP_eq_length_filter ..).symm
  have deg := inner_degree G np; simp only [List.length_cons] at ub; omega

structure Opened {M} (G : IsDiskFullerene M h) (A : Face M→Bool) (q : Face M) where
  o : Face M
  out : A o=false
  pre : List (Face M)
  post : List (Face M)
  whole : dualRow G q=pre++o::post

noncomputable def openAt {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (sz : num A≤5) {q : Face M} (iq : A q=true) (np : q≠apex M) : Opened G A q := by
  let ext := outside_neighbor G hh sz iq np
  let cut := List.append_of_mem ext.choose_spec.1
  exact ⟨ext.choose,ext.choose_spec.2,cut.choose,cut.choose_spec.choose,cut.choose_spec.choose_spec⟩

namespace Opened
variable {M : MapData} {G : IsDiskFullerene M h} {A : Face M→Bool} {q : Face M}

def faceRow (O : Opened G A q) := O.o :: (O.post ++ O.pre)
def numbers (O : Opened G A q) := (O.faceRow).map (tag A)

theorem order (O : Opened G A q) : O.faceRow.Perm (dualRow G q) := by rw [O.whole]; exact List.perm_append_comm (l₁:=O.o::O.post) (l₂:=O.pre)

theorem arcs (O : Opened G A q) {a b} : (a,b)∈sides O.faceRow ↔ (a,b)∈sides (dualRow G q) := by
  rw [O.whole]; exact List.Perm.mem_iff (cycle_split (O.o::O.post) O.pre)

theorem simple (O : Opened G A q) (hh : 3≤h) (sz : num A≤5) : O.numbers.Nodup :=
  List.pairwise_map.mpr (((O.order.nodup_iff.mpr (row_nodup G (noRepeatOnSphere G hh) q))).imp (fun hne h => hne (tagInj sz _ _ h)))

theorem index_edge (O : Opened G A q) {a b} (e : (a,b)∈sides (dualRow G q)) :
    (tag A a,tag A b)∈sides O.numbers := by
  rw [numbers,sides_map]; exact List.mem_map.mpr ⟨(a,b),O.arcs.mpr e,rfl⟩
end Opened

private theorem data_corner {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool} {t}
    (ht : t∈facial G A) {i j k} (it : i∈t) (jt : j∈t) (kt : k∈t) (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    ∃ q f g, (items A)[i]?=some q ∧ tag A f=j ∧ tag A g=k ∧
      ((f,g)∈sides (dualRow G q) ∨ (g,f)∈sides (dualRow G q)) := by
  obtain ⟨u,_,rfl⟩ := facial_witness ht
  obtain ⟨_,q,dq,uq⟩ := word_mem.mp it
  obtain ⟨_,f,df,uf⟩ := word_mem.mp jt
  obtain ⟨_,g,dg,ug⟩ := word_mem.mp kt
  obtain ⟨a,b,C,_,_,_,fs⟩ := corners_at G hh ((mem_triangle _ _).mp uq)
  have uniq {i j : Nat} {p r} (di : (items A)[i]? = some p) (dj : (items A)[j]? = some r) (ne : i≠j) : p≠r := by
    intro eq; subst r; exact ne ((label_decode di).2.symm.trans (label_decode dj).2)
  have qf := uniq dq df ij; have qg := uniq dq dg ik; have fg := uniq df dg jk
  have fsf := (fs f).mp ((mem_triangle _ _).mp uf); have fsg := (fs g).mp ((mem_triangle _ _).mp ug)
  refine ⟨q,f,g,dq, by simp [tag,(label_decode df).1,(label_decode df).2],by simp [tag,(label_decode dg).1,(label_decode dg).2],?_⟩
  have side := C.step; grind

private def openPair {M} {G : IsDiskFullerene M h} {A : Face M→Bool} {q : Face M} (O : Opened G A q) :=
  (tag A O.o,(O.post++O.pre).map (tag A))

noncomputable def entries {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (sz : num A≤5) (pole : A (apex M)=false) (i : Nat) : Nat × List Nat :=
  if e : ∃ q, (items A)[i]?=some q then
    openPair (openAt G hh sz (label_decode e.choose_spec).1 (fun eq => by have := (label_decode e.choose_spec).1; grind))
  else (5,[])

private theorem entries_eq {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (sz : num A≤5) (pole : A (apex M)=false) {i q} (de : (items A)[i]?=some q) :
    entries G hh sz pole i=openPair (openAt G hh sz (label_decode de).1 (fun eq => by have := (label_decode de).1; grind)) := by
  have ex : ∃ q, (items A)[i]?=some q := ⟨q,de⟩
  unfold entries; rw [dite_eq_left_of_eq_true (eq_true ex)]; have eq := Option.some.inj (ex.choose_spec.symm.trans de); cases eq; rfl

noncomputable def faceRows {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (sz : num A≤5) (pole : A (apex M)=false) : CornerRows (facial G A) where
  start x := (entries G hh sz pole x).1
  tail x := (entries G hh sz pole x).2
  startOutside x := by
    by_cases ex : ∃ q, (items A)[x]?=some q
    · obtain ⟨q,dq⟩ := ex; rw [entries_eq G hh sz pole dq]
      simp [openPair,tag,Opened.out]
    · simp [entries,ex]
  corners := by
    intro t ht i it j jt ne
    have ts := (List.mem_filter.mp (List.mem_filter.mp ht).1).1
    obtain ⟨u,_,he⟩ := facial_witness ht
    have small {l} (m : l∈t) : l∈labels := (in_labels _).mpr (word_mem.mp (he ▸ m)).1
    have tab := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp third_table t ts) i (small it)) j (small jt)
    simp [it,jt,ne,Bool.and_assoc] at tab
    obtain ⟨q,f,g,dq,fj,gk,side⟩ := data_corner G hh ht it jt tab.1 ne (Ne.symm tab.2.2.1) (Ne.symm tab.2.2.2.1)
    have stage := entries_eq G hh sz pole dq
    let O := openAt G hh sz (label_decode dq).1 (show q≠apex M by have := (label_decode dq).1; grind)
    rw [stage]; change j∈O.numbers ∧ third t i j∈O.numbers ∧ consecutive O.numbers.length (O.numbers.idxOf j) (O.numbers.idxOf (third t i j))
    have pair : (j,third t i j)∈sides O.numbers ∨ (third t i j,j)∈sides O.numbers := by
      rcases side with side|side
      · exact .inl (by simpa only [fj,gk] using O.index_edge side)
      · exact .inr (by simpa only [fj,gk] using O.index_edge side)
    refine ⟨?_,?_,side_consecutive (O.simple hh sz) pair⟩
    · rcases pair with s|s; exact (side_ends s).1; exact (side_ends s).2
    · rcases pair with s|s; exact (side_ends s).2; exact (side_ends s).1

private theorem positive_edges {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool} (sz : num A≤5)
    (nonempty : ∃ q,A q=true) (nonisolated : ∀ q, A q=true → ∃ f ∈ dualRow G q, A f=true) : 0<eCount (graph G A) := by
  obtain ⟨q,iq⟩ := nonempty; obtain ⟨f,nb,if'⟩ := nonisolated q iq
  have qf := small_label sz iq; have fl := small_label sz if'
  let i := label A q; let j := label A f
  have ne : i≠j := by
    intro eq
    have a := decode_label iq; have b := decode_label if'
    change label A q=label A f at eq; rw [eq] at a
    have e := Option.some.inj (a.symm.trans b); exact row_no_loop G hh _ (e ▸ nb)
  have ij := (edge_iff G hh A qf fl).mpr ⟨q,f,decode_label iq,decode_label if',nb⟩
  have ji := (edge_iff G hh A fl qf).mpr ⟨f,q,decode_label if',decode_label iq,(dual_adj_symmetric G _ _).mp nb⟩
  have all : ∀ a b : Fin 5, a.val<b.val → [a.val,b.val]∈pairs := by decide
  have here (a b : Fin 5) (lt : a.val<b.val) (ab : adjacent (graph G A) a.val b.val=true) (ba : adjacent (graph G A) b.val a.val=true) : 0<eCount (graph G A) := by
    have m : [a.val,b.val]∈pairs.filter (clique (graph G A)) := List.mem_filter.mpr ⟨all a b lt,by simp [clique,ab,ba]⟩
    simpa [eCount,List.countP_eq_length_filter] using List.length_pos_of_mem m
  change i<5 at qf; change j<5 at fl
  by_cases l : i<j
  · exact here ⟨i,qf⟩ ⟨j,fl⟩ l ij ji
  · have lt : j<i := by omega
    exact here ⟨j,fl⟩ ⟨i,qf⟩ lt ji ij

private theorem ear_run {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (sz : num A≤5) (pole : A (apex M)=false) {i : Nat} (il : i∈labels) (ie : trueEar (graph G A) (facial G A) i=true) :
    ∃ q, (items A)[i]?=some q ∧ BoundaryRun G A q := by
  let F := facial G A
  let K := graph G A
  have full : innerNeighbors K i≠[] := by intro nil; change trueEar K F i=true at ie; simp [trueEar,nil] at ie
  obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil (l:=innerNeighbors K i) full
  have wv := List.mem_filter.mp hw
  obtain ⟨q,_,dq,_,_⟩ := (edge_iff G hh A ((in_labels _).mp il) ((in_labels _).mp wv.1)).mp wv.2
  have np : q≠apex M := by have := (label_decode dq).1; grind
  let O := openAt G hh sz (label_decode dq).1 np
  let R := faceRows G hh sz pole
  have numeq : rowAt R i=O.numbers := by change (entries G hh sz pole i).1 :: (entries G hh sz pole i).2=_; rw [entries_eq G hh sz pole dq]; rfl
  have incl : F ⊆ triples := fun _ h=> (List.mem_filter.mp (List.mem_filter.mp h).1).1
  have active (l : Nat) (lt : l<5) : l∈O.numbers ↔ l∈innerNeighbors K i := by
    constructor
    · intro mem
      obtain ⟨f,fm,fe⟩ := List.mem_map.mp mem
      have chosen := (smallTag sz f).mp (by omega)
      have fl : label A f=l := by simpa [tag,chosen] using fe
      exact List.mem_filter.mpr ⟨(in_labels _).mpr lt,(edge_iff G hh A ((in_labels _).mp il) lt).mpr ⟨q,f,dq,fl ▸ decode_label chosen,O.order.mem_iff.mp fm⟩⟩
    · intro mem
      obtain ⟨r,f,dr,df,nb⟩ := (edge_iff G hh A ((in_labels _).mp il) lt).mp (List.mem_filter.mp mem).2
      have eq := Option.some.inj (dr.symm.trans dq); subst r
      exact List.mem_map.mpr ⟨f,O.order.mem_iff.mpr nb,by simp [tag,(label_decode df).1,(label_decode df).2]⟩
  have pos := facial_ear_positions R incl i il ie (by simpa only [numeq] using active) (by rw [numeq]; exact O.simple hh sz)
  change ∃ a b, a < (rowAt R i).length ∧ b < (rowAt R i).length ∧ _ at pos
  rw [numeq] at pos
  obtain ⟨a,b,ha,hb,adj,inside⟩ := pos
  have deg : O.numbers.length=5 ∨ O.numbers.length=6 := by simpa [Opened.numbers,O.order.length_eq] using inner_degree G np
  obtain ⟨k,hk,three⟩ := ear_boundary_run O.numbers a b deg ha hb adj inside
  let r := O.faceRow
  have rd : r.length=5 ∨ r.length=6 := by simpa [Opened.numbers,r] using deg
  have ip (l : Nat) : (k+l)%r.length < r.length := Nat.mod_lt _ (by omega)
  let get (l : Nat) := r[(k+l)%r.length]'(ip l)
  have outside (j : Fin 3) : A (get j.val)=false := by
    have ob := three j; change 5 ≤ (r.map (tag A))[(k+j.val)%(r.map (tag A)).length]'(by simpa using ip j.val) at ob
    simp only [List.length_map,List.getElem_map] at ob
    change 5≤tag A (get j.val) at ob
    cases eq : A (get j.val) with
    | false => rfl
    | true => have := (smallTag sz (get j.val)).mpr eq; omega
  have side (j : Nat) : (get j,get (j+1))∈sides (dualRow G q) := by
    apply O.arcs.mp
    have e := side_at r ((k+j)%r.length) (ip j)
    have nextIndex : next r.length ((k+j)%r.length)=(k+(j+1))%r.length := by
      unfold next; rcases rd with e|e <;> simp only [e] <;> split <;> omega
    exact List.mem_iff_getElem.mpr ⟨_,by simpa [sides_size] using ip j,by simpa only [get,nextIndex] using e⟩
  have different : get 0≠get 2 := by
    intro eq; have nd := O.order.nodup_iff.mpr (row_nodup G (noRepeatOnSphere G hh) q)
    have same := index_eq nd (ip 0) (ip 2) eq
    rcases rd with e|e <;> simp only [e] at same <;> omega
  exact ⟨q,dq,get 0,get 1,get 2,different,outside 0,outside 1,outside 2,side 0,side 1⟩

/-- A local six-vertex bound for any nonempty mask with nonisolated
vertices, the one-sided Euler inequality, and a single possible center
of a three-neighbor exterior run. -/
theorem six_of_mask {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M→Bool)
    (pole : A (apex M)=false) (nonempty : ∃ u,A u=true)
    (nonisolated : ∀ f, A f=true → ∃ g∈dualRow G f, A g=true)
    (single : ∃ z, ∀ f, A f=true → BoundaryRun G A f → f=z)
    (euler : num (sideEdge (dual G) A)+1 ≤ num A+num (solid G A true)) : 6≤num A := by
  by_cases sz : num A≤5
  · have card : eCount (graph G A)+1 ≤ vCount (graph G A)+(facial G A).length := by
      have e := edge_count G hh A; have v := active_count G hh A sz nonisolated; have t := face_count G hh A sz; omega
    have incl : facial G A ⊆ triples := fun _ m=> (List.mem_filter.mp (List.mem_filter.mp m).1).1
    have nd : (facial G A).Nodup := ((show triples.Nodup by decide).filter _).filter _
    have openRows := faceRows G hh sz pole
    have clearance := open_of_linear incl nd (linearFromRows incl openRows)
    have bound := two_facial_ears (graph G A) (isFace G A) (positive_edges G hh sz nonempty nonisolated) card clearance
    obtain ⟨z,only⟩ := single
    let ears := labels.filter (trueEar (graph G A) (facial G A))
    have unique : ears ⊆ [label A z] := by
      intro i hi; obtain ⟨il,ie⟩ := List.mem_filter.mp hi
      obtain ⟨q,dq,run⟩ := ear_run G hh sz pole il ie
      obtain ⟨iq,eq⟩ := label_decode dq
      have qz := only q iq run; simp [←qz,eq]
    have high := (show ears.Nodup from (show labels.Nodup by decide).filter _).length_le_of_subset unique
    change 2≤ears.length at bound; simp only [List.length_cons,List.length_nil] at high; omega
  · change 6≤num A; omega

/-- A terminal actual chord component with nonempty strict interior has
at least six interior dual vertices. -/
theorem terminal_six {M} (G : IsDiskFullerene M h) (hh : 3≤h) {x y} (S : TriangleSide G (apex M) x y)
    (B : Bool) (P : TerminalHalf G (vertexSide S B)) (nonempty : ∃ u,sectorCore S B u=true) : 6≤num (sectorCore S B) :=
  six_of_mask G hh _ (by simp [sectorCore,mem_diskInterior]) nonempty (fun _ h=>terminal_nonisolated hh S B P h)
    (terminal_single_run hh S B P) (sector_core_bound hh S B nonempty)

end DiskFullerene.EndLabels
