import DiskFullerene.EndCoreEuler
import DiskFullerene.InteriorTriangles

namespace DiskFullerene.EndLabels
open Dual EndEuler Separation

/-- A corner of a dual face at an actual cubic primal vertex. The dart
provides a witness that distinguishes the two ends of each primal edge. -/
def Corner {M : MapData} (G : IsDiskFullerene M h) (u : Fin M.ord) (i a b : Face M) : Prop :=
  ∃ p q, Dual.incident M i (p,u.val) ∧ M.turn (p,u.val)=(u.val,q) ∧
    a=owner G (u.val,p) ∧ b=owner G (q,u.val)

theorem Corner.step {M} {G : IsDiskFullerene M h} {u : Fin M.ord} {i a b}
    (C : Corner G u i a b) : (a,b) ∈ sides (dualRow G i) := by
  obtain ⟨p,q,ip,tr,rfl,rfl⟩ := C
  simpa [tr] using across_turn G ip

private theorem firstDart {M : MapData} {i : Face M} {v} (m : v ∈ M.faces[i.val]) :
    ∃ w, Dual.incident M i (v,w) := by
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp m
  exact ⟨_, List.mem_iff_getElem.mpr ⟨k, by simpa [sides_size] using hk, side_at _ k hk⟩⟩

private theorem incoming {M : MapData} {i : Face M} {v} (m : v ∈ M.faces[i.val]) :
    ∃ w, Dual.incident M i (w,v) := by
  let s := M.faces[i.val]
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp m
  let j := if k=0 then s.length-1 else k-1
  have hk' : k<s.length := hk
  have hj : j<s.length := by simp only [j]; split <;> omega
  have wrap : next s.length j=k := by unfold next j; split <;> split <;> omega
  have edge : (s[j],s[next s.length j]'(next_bound hj)) ∈ sides s :=
    List.mem_iff_getElem.mpr ⟨j,by simpa [sides_size] using hj,side_at _ _ hj⟩
  have out : s[k] = v := eq
  refine ⟨s[j],?_⟩
  change (s[j],v) ∈ sides s
  simpa only [wrap,out] using edge

theorem corners_at {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u : Fin M.ord} {i : Face M}
    (m : u.val∈M.faces[i.val]) : ∃ a b, Corner G u i a b ∧ a≠b ∧ a≠i ∧ b≠i ∧
      ∀ f, u.val∈M.faces[f.val] ↔ f=i ∨ f=a ∨ f=b := by
  obtain ⟨p,ip⟩ := incoming m
  let q := (M.turn (p,u.val)).2
  have tr : M.turn (p,u.val)=(u.val,q) := rfl
  have iq : Dual.incident M i (u.val,q) := tr ▸ incident_turn G ip
  let a := owner G (u.val,p)
  let b := owner G (q,u.val)
  have A : Dual.incident M a (u.val,p) := reverse_owner G ip
  have B : Dual.incident M b (q,u.val) := reverse_owner G iq
  have C : Corner G u i a b := ⟨p,q,ip,tr,rfl,rfl⟩
  have adj := cyclic_link G i C.step
  have ab : a≠b := by intro eq; exact row_no_loop G hh _ (eq ▸ adj)
  refine ⟨a,b,C,ab,Ne.symm (opposite_faces_distinct G hh ip A),Ne.symm (opposite_faces_distinct G hh iq B),?_⟩
  intro f
  exact ⟨three_at_corner G ip tr,fun z => by rcases z with rfl|rfl|rfl; exact m; exact (sideEnds A).1; exact (sideEnds B).2⟩

private theorem incident_vertex {M} (G : IsDiskFullerene M h) (u : Fin M.ord) : ∃ i : Face M, u.val∈M.faces[i.val] := by
  have sz := G.cubic _ (List.getElem_mem (l:=M.rows) u.isLt)
  let v := (M.rows[u.val]'u.isLt)[0]'(by omega)
  have adj : M.adj u.val v := by simp only [MapData.adj,List.getElem?_eq_getElem u.isLt,Option.getD_some]; exact List.getElem_mem _
  exact ⟨_,(sideEnds (owner_incident G (dart_iff.mpr adj))).1⟩

noncomputable def triangle {M : MapData} (u : Fin M.ord) :=
  (List.finRange M.faces.length).filter fun i=>decide (u.val∈M.faces[i.val])

@[simp] theorem mem_triangle {M : MapData} (u : Fin M.ord) (f : Face M) : f ∈ triangle u ↔ u.val∈M.faces[f.val] := by simp [triangle]

theorem triangle_three {M} (G : IsDiskFullerene M h) (hh : 3≤h) (u : Fin M.ord) : (triangle u).length=3 := by
  obtain ⟨i,hit⟩ := incident_vertex G u
  obtain ⟨a,b,_,ab,ai,bi,faces⟩ := corners_at G hh hit
  have p : (triangle u).Perm [i,a,b] := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (by simp [Ne.symm ai,Ne.symm bi,ab])).mpr
    intro f; simp [faces]
  simpa using p.length_eq

/-- Distinct primal vertices give distinct sets of three incident faces.
Two matching oriented corners use the same entering dart. Oppositely
oriented matching corners would traverse a 2-cycle in a simple link. -/
theorem same_triangle {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u v : Fin M.ord}
    (agree : ∀ f, f ∈ triangle u ↔ f ∈ triangle v) : u=v := by
  obtain ⟨i,iu⟩ := incident_vertex G u
  have iv := (mem_triangle v i).mp ((agree i).mp ((mem_triangle u i).mpr iu))
  obtain ⟨a,b,P,ab,ai,bi,U⟩ := corners_at G hh iu
  obtain ⟨c,d,Q,cd,ci,di,V⟩ := corners_at G hh iv
  have common (j : Face M) : (j=i ∨ j=a ∨ j=b) ↔ (j=i ∨ j=c ∨ j=d) := by
    simpa only [mem_triangle,U,V] using agree j
  have perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a) := by
    have h₁ := (common c).mpr (by simp); have h₂ := (common d).mpr (by simp); grind
  rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · obtain ⟨p,_,pv,_,va,_⟩ := P
    obtain ⟨r,_,rv,_,ra,_⟩ := Q
    have eq := noRepeatOnSphere G hh i c _ _ pv (va ▸ reverse_owner G pv) rv (ra ▸ reverse_owner G rv)
    exact Fin.ext (congrArg Prod.snd eq)
  · have sz : 3≤(dualRow G i).length := by
      by_cases eq : i=apex M
      · subst i; simpa [(boundary_cycle G hh).2.1] using hh
      · have := inner_degree G eq; omega
    exact False.elim (face_has_no_reverse (row_nodup G (noRepeatOnSphere G hh) i) sz P.step Q.step)

theorem solid_iff {M} (G : IsDiskFullerene M h) (A : Face M→Bool) (u : Fin M.ord) :
    solid G A true u=true ↔ ∀ f ∈ triangle u, A f=true := by
  constructor
  · intro yes f hf
    obtain ⟨v,iv⟩ := firstDart ((mem_triangle u f).mp hf)
    have adj := dart_iff.mp (incident_dart G iv)
    have m : v ∈ (M.rows[u.val]'u.isLt) := by simpa [MapData.adj,List.getElem?_eq_getElem u.isLt] using adj
    have z := List.all_eq_true.mp yes v m
    simpa [owner_eq G iv] using (Bool.and_eq_true_iff.mp z).1
  · intro yes; apply List.all_eq_true.mpr
    intro v hv
    have adj : M.adj u.val v := by simpa [MapData.adj,List.getElem?_eq_getElem u.isLt] using hv
    have a := sideEnds (owner_incident G (dart_iff.mpr adj))
    have b := sideEnds (owner_incident G (dart_reverse G (dart_iff.mpr adj)))
    simp [yes _ ((mem_triangle u _).mpr a.1),yes _ ((mem_triangle u _).mpr b.2)]

end DiskFullerene.EndLabels
