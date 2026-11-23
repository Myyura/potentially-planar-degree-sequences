import DiskFullerene.ArmWheels

namespace DiskFullerene.Dual
open Separation

/-- The three neighbors of a wheel rim vertex lying in the wheel occur
consecutively in its full link, flanking the center. -/
theorem ArmWheel.rim_three {M} {G : IsDiskFullerene M h} {D : Branch G} (W : ArmWheel G D)
    (hh : 3≤h) {u} (rim : u∈dualRow G W.center) :
    ∃ a b : Face M, (a,W.center)∈sides (dualRow G u) ∧ (W.center,b)∈sides (dualRow G u) ∧
      a∈dualRow G W.center ∧ b∈dualRow G W.center ∧ a≠b ∧
      (∀ x∈dualRow G u, arm G D.root D.seed x=true → x=a ∨ x=W.center ∨ x=b) := by
  let C := dualRow G W.center
  let m := M.faces[W.center.val].length
  have len : C.length=m := row_length G W.center
  have five : m=5 := len.symm.trans W.degree
  let N (i : Fin m) := atSide G W.center i
  let suc (i : Fin m) : Fin m := ⟨next m i.val,next_bound i.isLt⟩
  let pre (i : Fin m) : Fin m := ⟨if i.val=0 then 4 else i.val-1,by split <;> omega⟩
  have prev (i) : suc (pre i)=i := by apply Fin.ext; dsimp [suc,pre,next]; split <;> split <;> omega
  have turn (i : Fin m) : (N i,N (suc i))∈sides C := by
    have lt : i.val<C.length := by rw [len];exact i.isLt
    have eq := side_at C i.val lt
    refine List.mem_iff_getElem.mpr ⟨i.val,by simpa [sides_size] using lt,?_⟩
    have nj : (suc i).val=next C.length i.val := by simp [suc,len]
    have left : N i = C[i.val] := atSide_eq G W.center i
    have right : N (suc i)=C[(suc i).val]'(by rw [len];exact (suc i).isLt) := atSide_eq G W.center (suc i)
    simp [left,right,nj,eq]
  have covered (v : Face M) (cv : v∈C) : ∃ i : Fin m, N i=v := by
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp cv
    let i : Fin m := ⟨j,by rwa [←len]⟩
    exact ⟨i,atSide_eq G W.center i⟩
  obtain ⟨i,rfl⟩ := covered _ rim
  have before := turn (pre i)
  rw [prev] at before
  have inR (x : Fin m) : N x∈C := by dsimp [N]; rw [atSide_eq]; exact List.getElem_mem _
  have unequal : N (suc i)≠N (pre i) := by
    intro eq
    have e := congrArg Fin.val (atSide_inj G hh W.center eq)
    dsimp [suc,pre,next] at e; split at e <;> split at e <;> omega
  refine ⟨N (suc i),N (pre i),(turn_triangle G (i:=W.center) (turn i)).1,
    (turn_triangle G (i:=W.center) before).2,inR _,inR _,unequal,?_⟩
  intro x xu ix
  rcases (W.allFaces x).1 ix with rfl|xc
  · exact Or.inr (Or.inl rfl)
  obtain ⟨j,rfl⟩ := covered _ xc
  have neq : i≠j := fun eq => row_no_loop G hh _ (eq ▸ xu)
  have positions : j=suc i ∨ j=pre i := by
    by_cases ij : i<j
    · have o := (W.rim i j ij).1 xu
      rcases o with o|⟨lo,hi⟩
      · exact Or.inl (Fin.ext (by dsimp [suc,next];split <;> omega))
      · exact Or.inr (Fin.ext (by dsimp [pre];simp [lo,hi]))
    · have ji : j<i := by omega
      have o := (W.rim j i ji).1 ((dual_adj_symmetric G _ _).1 xu)
      rcases o with o|⟨lo,hi⟩
      · exact Or.inr (Fin.ext (by dsimp [pre]; split <;> omega))
      · exact Or.inl (Fin.ext (by dsimp [suc,next]; split <;> omega))
  exact positions.elim (fun eq => Or.inl (congrArg N eq)) (fun eq => Or.inr (Or.inr (congrArg N eq)))

/-- An interior vertex of a six-vertex arm other than its attachment has
degree five in the original dual. For a rim vertex, degree six would
leave a run of three boundary neighbors opposite its three wheel edges. -/
theorem ArmWheel.degree_five {M} {G : IsDiskFullerene M h} {D : Branch G} (W : ArmWheel G D)
    (hh : 3≤h) (hc : ¬HasChord G) {u} (um : u∈D.members) : (dualRow G u).length=5 := by
  have active : arm G D.root D.seed u=true := in_arm.mpr (Or.inr ((D.mem_iff _).1 um))
  have ui := arm_stays_inside D.rootIn D.seedIn active
  have notRoot : u≠D.root := fun eq => D.out hh (eq ▸ um)
  rcases (W.allFaces u).1 active with rfl | uc
  · exact W.degree
  obtain ⟨p,q,pc,cq,_,_,_,only⟩ := W.rim_three hh uc
  have degree := inner_degree G ((mem_diskInterior G _).1 ui).1
  rcases degree with five|six
  · exact five
  exfalso
  let R := dualRow G u
  have sz : R.length=6 := six
  have nd := row_nodup G (noRepeatOnSphere G hh) u
  obtain ⟨r⟩ := reroot nd (Or.inr six) (endsOfWordSide pc).1
  have transitions (i) (bound : i<6) : (r.atPos i,r.atPos (i+1))∈sides R := r.side _ (by omega)
  have p0 : r.atPos 0=p := r.first
  have pc' : (r.atPos 0,W.center)∈sides R := by rw [p0];exact pc
  have c1 := same_next_word nd (transitions 0 (by decide)) pc'
  have cq' : (r.atPos 1,q)∈sides R := by rw [show r.atPos 1=W.center from c1];exact cq
  have q2 := same_next_word nd (transitions 1 (by decide)) cq'
  have inject {i j} (ib : i<6) (jb : j<6) (eq : r.atPos i=r.atPos j) : i=j :=
    r.inject _ _ (by omega) (by omega) eq
  have outer (i) (lo : 3≤i) (hi : i<6) : IsBoundary G (r.atPos i) := by
    have mem : r.atPos i∈dualRow G u := (r.covers _).2 ⟨i,by omega,rfl⟩
    apply arm_frontier D.rootIn D.seedIn notRoot active _ mem
    cases act : arm G D.root D.seed (r.atPos i) with
    | false => rfl
    | true =>
      rcases only _ mem act with ip|ic|iq
      · have eq := inject hi (by decide : 0<6) (ip.trans p0.symm); omega
      · have eq := inject hi (by decide : 1<6) (ic.trans c1.symm); omega
      · have eq := inject hi (by decide : 2<6) (iq.trans q2.symm); omega
  exact no_three_on_boundary G hh hc ui (outer 3 (by decide) (by decide)) (outer 4 (by decide) (by decide))
    (outer 5 (by decide) (by decide)) (fun eq => by have := inject (by decide : 3<6) (by decide : 5<6) eq; omega)
    (transitions 3 (by decide)) (transitions 4 (by decide))

end DiskFullerene.Dual
