import DiskFullerene.EndSix
import DiskFullerene.EndRotations
import DiskFullerene.CapRing

namespace DiskFullerene.EndFans
open Dual EndEuler Separation EndLabels EndSix

abbrev I := Fin 5
abbrev after (i : I) := CapRing.next i
def before (i : I) : I := ⟨(i.val+4)%5,by omega⟩

private theorem ring_id : ∀ i : I, after (before i)=i ∧ before (after i)=i ∧ before i≠after i ∧ after i≠i ∧ before i≠i := by decide

structure Wheel {M : MapData} (G : IsDiskFullerene M h) (A : Face M→Bool) where
  center : Face M
  rim : I → Face M
  rim_injective : ∀ i j, rim i=rim j → i=j
  apart : ∀ i, rim i≠center
  central : ∀ q, q∈dualRow G center ↔ ∃ i, q=rim i
  chosen : ∀ q, A q=true ↔ q=center ∨ ∃ i, q=rim i
  wheel : ∀ i, ∀ q, A q=true → (q∈dualRow G (rim i) ↔ q=center ∨ q=rim (before i) ∨ q=rim (after i))
  oriented : ∀ i, (rim i,rim (after i))∈sides (dualRow G center)

/-- Index the actual wheel in the order induced by the center's rotation. -/
theorem wheel_of_center {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M→Bool) (sz : num A=6)
    (pole : A (apex M)=false) (c : Face M) (inc : A c=true) (closed : ∀ q∈dualRow G c, A q=true)
    (conn : ∀ a∉items A, ∀ b∉items A, OutsideWalk G (items A) a b) : Nonempty (Wheel G A) := by
  obtain ⟨dg,allK,pairs⟩ := EndSix.wheel G hh (items A) (by simpa [items,num,List.countP_eq_length_filter] using sz)
    (by simp [pole]) c (selected.mpr inc) (fun _ m=>selected.mpr (closed _ m)) conn
  have len : M.faces[c.val].length=5 := (row_length G c).symm.trans dg
  let slot (i : I) : Fin M.faces[c.val].length := ⟨i.val,by rw [len]; exact i.isLt⟩
  let r (i : I) := atSide G c (slot i)
  have raw (i : I) : r i=(dualRow G c)[i.val]'(by rw [dg]; exact i.isLt) := atSide_eq _ _ _
  have rr (i : I) : r i ∈ dualRow G c := by rw [raw]; exact List.getElem_mem _
  have rI (i j : I) (e : r i=r j) : i=j := Fin.ext (congrArg (fun x : Fin M.faces[c.val].length=>x.val) (atSide_inj G hh c e))
  have part (q) : A q=true ↔ q=c ∨ ∃ i, q=r i := by
    rw [←selected,allK]; constructor
    · rintro (eq|e); exact .inl eq
      obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp e
      exact .inr ⟨⟨k,by omega⟩,eq.symm.trans (raw ⟨k,by omega⟩).symm⟩
    · rintro (eq|⟨i,rfl⟩); exact .inl eq; exact .inr (rr i)
  have tab : ∀ i j : I, i<j → ((j.val=i.val+1 ∨ (i.val=0 ∧ j.val=4)) ↔ j=before i ∨ j=after i) := by decide
  have pair (i j : I) (lt : i<j) : r j∈dualRow G (r i) ↔ j=before i ∨ j=after i :=
    (pairs (slot i) (slot j) lt).trans (tab i j lt)
  have sym : ∀ i j : I, (i=before j ∨ i=after j) ↔ (j=before i ∨ j=after i) := by decide
  have all (i j : I) : r j∈dualRow G (r i) ↔ j=before i ∨ j=after i := by
    by_cases eq : i=j
    · subst j; simp [row_no_loop G hh,Ne.symm (ring_id i).2.2.2.1,Ne.symm (ring_id i).2.2.2.2]
    · by_cases lt : i<j
      · exact pair i j lt
      · exact (dual_adj_symmetric G ..).trans ((pair j i (by have : i.val≠j.val := fun e=>eq (Fin.ext e); change ¬ i.val<j.val at lt; change j.val<i.val; omega)).trans (sym i j))
  have central (q) : q∈dualRow G c ↔ ∃ i, q=r i := by
    constructor
    · intro nb; obtain ⟨j,n,eq⟩ := List.mem_iff_getElem.mp nb; exact ⟨⟨j,by omega⟩,eq.symm.trans (raw ⟨j,by omega⟩).symm⟩
    · rintro ⟨i,rfl⟩; exact rr i
  refine ⟨⟨c,r,rI,fun i eq=>row_no_loop G hh _ (eq ▸ rr i),central,part,?_,?_⟩⟩
  · intro i q iq; rcases (part q).mp iq with rfl|⟨j,rfl⟩
    · simp [(dual_adj_symmetric G _ _).mp (rr i)]
    · have h := all i j
      have nc : r j≠c := fun eq=>row_no_loop G hh _ (eq ▸ rr j)
      constructor
      · intro m; rcases h.mp m with e|e <;> simp [e]
      · rintro (eq|eq|eq); exact False.elim (nc eq); exact h.mpr (.inl (rI _ _ eq)); exact h.mpr (.inr (rI _ _ eq))
  · intro i
    have hi : i.val<(dualRow G c).length := by rw [dg]; exact i.isLt
    have nxt : next (dualRow G c).length i.val=(after i).val := by rw [dg]; exact (by decide : ∀ j : I, next 5 j.val=(after j).val) i
    exact List.mem_iff_getElem.mpr ⟨i.val,by simpa [sides_size] using hi,by rw [side_at _ _ hi,raw,raw]; simp [nxt]⟩

private theorem out_degree {M} {G : IsDiskFullerene M h} {A : Face M→Bool} (W : Wheel G A) (pole : A (apex M)=false) (i : I) :
    (dualRow G (W.rim i)).length=5 ∨ (dualRow G (W.rim i)).length=6 :=
  inner_degree G (fun eq => by have := (W.chosen _).mpr (Or.inr ⟨i,rfl⟩); rw [eq,pole] at this; contradiction)

private theorem shaped {α} {r : List α} (nd : r.Nodup) (size : r.length=5 ∨ r.length=6) {n c p : α}
    (nc : (n,c)∈sides r) (cp : (c,p)∈sides r) : ∃ ext : List α,
    (ext.length=2 ∨ ext.length=3) ∧ (n::c::p::ext).Perm r ∧ (sides (n::c::p::ext)).Perm (sides r) := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp nc; rw [sides_size] at hi; rw [side_at _ _ hi] at eq
  have nm : n∈r := (Prod.mk.inj eq).1 ▸ List.getElem_mem _
  obtain ⟨a,b,rr⟩ := List.append_of_mem nm
  have row : (n::(b++a)).Perm r := by rw [rr]; exact List.perm_append_comm (l₁:=n::b) (l₂:=a)
  have edge : (sides (n::(b++a))).Perm (sides r) := by rw [rr]; exact cycle_split (n::b) a
  let s := b++a
  have len := row.length_eq; change s.length+1=r.length at len
  have rare := row.nodup_iff.mpr nd
  have h1 := edge.mem_iff.mpr nc; have h2 := edge.mem_iff.mpr cp
  change (n,c)∈sides (n::s) at h1; change (c,p)∈sides (n::s) at h2
  have source {x y z : α} {r : List α} (nod : r.Nodup) (a : (x,y)∈sides r) (b : (x,z)∈sides r) : y=z := by
    obtain ⟨i,hi,pk⟩ := List.mem_iff_getElem.mp a; obtain ⟨j,hj,pl⟩ := List.mem_iff_getElem.mp b
    rw [sides_size] at hi hj; rw [side_at _ _ hi] at pk; rw [side_at _ _ hj] at pl
    have eq := index_eq nod hi hj ((Prod.mk.inj pk).1.trans (Prod.mk.inj pl).1.symm); subst j
    exact (Prod.mk.inj pk).2.symm.trans (Prod.mk.inj pl).2
  change (n::s).Nodup at rare
  obtain ⟨u,v,t,qq⟩ : ∃ u v t, s=u::v::t := by
    have length : 2≤s.length := by omega
    generalize e : s=l at length ⊢
    cases l with
    | nil => simp at length
    | cons a t => cases t with | nil => simp at length | cons b t => exact ⟨_,_,_,rfl⟩
  rw [qq] at h1 h2 rare
  have first : c=u := source rare h1 (by simp [sides])
  subst u
  have second : p=v := source rare h2 (by simp [sides])
  subst v
  exact ⟨t,by rw [qq] at len; simp only [List.length_cons] at len; omega,by change (n::c::p::t).Perm r; rw [←qq]; exact row,by rw [←qq]; exact edge⟩

structure Fan {M} {G : IsDiskFullerene M h} {A : Face M→Bool} (W : Wheel G A) (i : I) where
  arc : List (Face M)
  size : arc.length=2 ∨ arc.length=3
  outside : ∀ v∈arc, A v=false
  distinct : (W.rim (after i)::W.center::W.rim (before i)::arc).Nodup
  neighbors : (W.rim (after i)::W.center::W.rim (before i)::arc).Perm (dualRow G (W.rim i))
  corners : (sides (W.rim (after i)::W.center::W.rim (before i)::arc)).Perm (sides (dualRow G (W.rim i)))

/-- The outside neighbors of each actual wheel rim vertex are one run of
two or three. Both end corners of the run retain their orientation. -/
theorem rim_fan {M} {G : IsDiskFullerene M h} {A : Face M→Bool} (hh : 3≤h) (pole : A (apex M)=false)
    (W : Wheel G A) (i : I) : Nonempty (Fan W i) := by
  have h1 := (turn_triangle G (W.oriented i)).1
  have h2 := (turn_triangle G (W.oriented (before i))).2
  rw [(ring_id i).1] at h2
  obtain ⟨arc,sz,perm,corners⟩ := shaped (row_nodup G (noRepeatOnSphere G hh) _) (out_degree W pole i) h1 h2
  have nd := perm.nodup_iff.mpr (row_nodup G (noRepeatOnSphere G hh) _)
  refine ⟨⟨arc,sz,?_,nd,perm,corners⟩⟩
  intro v mv
  by_cases chosen : A v=true
  · have av : v ∈ dualRow G (W.rim i) := perm.mem_iff.mp (by simp [mv])
    have opts := (W.wheel i v chosen).mp av
    simp only [List.nodup_cons] at nd; grind
  · simp_all

end DiskFullerene.EndFans
