import DiskFullerene.CutSides

namespace DiskFullerene.EndSix
open Dual Separation

def OutsideWalk {M} (G : IsDiskFullerene M h) (K : List (Face M)) (x y : Face M) :=
  Walk (fun a b => a∉K ∧ b∉K ∧ b∈dualRow G a) x y

private def Away (c a b x : α) := x≠c ∧ x≠a ∧ x≠b

private theorem constantInterval {P : Nat → Prop} {i j : Nat} (ij : i≤j)
    (f : ∀ k, i≤k → k<j → (P k ↔ P (k+1))) : P i ↔ P j := by
  induction j with
  | zero =>
    have zero : i=0 := by omega
    rw [zero]
  | succ j ih =>
    by_cases h : i=j+1
    · subst i; rfl
    · exact (ih (by omega) (fun k a b => f k a (by omega))).trans (f j (by omega) (by omega))

/-- The two nonempty open arcs of a diagonal in an actual dual link have
different colors in the sphere cut along the triangle. Either linear order
of the exterior index is allowed. -/
private theorem separatesRim {M} (G : IsDiskFullerene M h) (hh : 3≤h) (c : Face M)
    (i j k l : Fin M.faces[c.val].length) (ij : i<j) (jk : j<k)
    (outside : l<i ∨ k<l)
    (chord : atSide G c k ∈ dualRow G (atSide G c i)) :
    ∃ S : TriangleSide G c (atSide G c i) (atSide G c k),
      ¬(S.faceColor (atSide G c j) ↔ S.faceColor (atSide G c l)) := by
  let N := atSide G c
  have inj := atSide_inj G hh c
  have neighbor z : N z ∈ dualRow G c := by dsimp [N]; rw [atSide_eq]; exact List.getElem_mem _
  have away z : N z ≠ c := fun eq => row_no_loop G hh c (eq ▸ neighbor z)
  obtain ⟨S⟩ := hasSides G hh (neighbor i) chord ((dual_adj_symmetric G ..).mp (neighbor k))
  let P := fun t : Nat => S.color (M.faces[c.val][t]?.getD 0)
  have flip (t) (ht : t+1 < M.faces[c.val].length) :
      (¬(P t ↔ P (t+1))) ↔ t=i.val ∨ t=k.val := by
    let z : Fin M.faces[c.val].length := ⟨t,by omega⟩
    have ch := around_changes hh S (away i).symm (away k) z
    have val (a) : N z = N a ↔ t=a.val := ⟨fun eq => congrArg Fin.val (inj eq),fun eq => congrArg N (Fin.ext eq)⟩
    change (¬(S.color (sideDart M c z).1 ↔ S.color (sideDart M c z).2)) ↔ N z=N i ∨ N z=N k at ch
    rw [val i,val k] at ch
    have desc := side_at M.faces[c.val] t z.isLt
    change sideDart M c z = _ at desc
    simpa [desc,P,next,ht,show t<M.faces[c.val].length by omega] using ch
  have plain (t : Nat) (h : t+1<M.faces[c.val].length) (a : t≠i.val) (b : t≠k.val) : P t ↔ P (t+1) := by
    apply Classical.byContradiction
    exact fun q => ((flip t h).mp q).elim a b
  have color (z : Fin M.faces[c.val].length) (zi : z≠i) (zk : z≠k) : S.faceColor (N z) ↔ P z.val := by
    have d := reverse_owner G (sideDart_mem M c z)
    have q := S.color_at ⟨away z,fun e => zi (inj e),fun e => zk (inj e)⟩ (sideEnds d).2
    have desc := side_at M.faces[c.val] z.val z.isLt
    change sideDart M c z = _ at desc
    change S.faceColor (N z) ↔ S.color (sideDart M c z).1 at q
    simpa [desc,P] using q
  refine ⟨S,?_⟩
  intro eq
  have cmp := (color j (by omega) (by omega)).symm.trans (eq.trans (color l (by omega) (by omega)))
  rcases outside with lo|hi
  · have a := constantInterval (P:=P) (i:=l.val) (j:=i.val) (by omega)
        (fun t a b => plain t (by omega) (by omega) (by omega))
    have b := constantInterval (P:=P) (i:=i.val+1) (j:=j.val) (by omega)
        (fun t a b => plain t (by omega) (by omega) (by omega))
    exact ((flip i.val (by omega)).mpr (Or.inl rfl)) (a.symm.trans (cmp.symm.trans b.symm))
  · have a := constantInterval (P:=P) (i:=j.val) (j:=k.val) (by omega)
        (fun t a b => plain t (by omega) (by omega) (by omega))
    have b := constantInterval (P:=P) (i:=k.val+1) (j:=l.val) (by omega)
        (fun t a b => plain t (by omega) (by omega) (by omega))
    exact ((flip k.val (by omega)).mpr (Or.inr rfl)) (a.symm.trans (cmp.trans b.symm))

/-- If a vertex of a six-vertex set misses a different member, at most four
of its possible neighbours are in the set. Thus it must touch the complement. -/
private theorem touches {M} (G : IsDiskFullerene M h) (hh : 3≤h)
    {K : List (Face M)} (len : K.length≤6)
    {x y : Face M} (hx : x∈K) (hy : y∈K) (dif : x≠y)
    (deg : 5≤(dualRow G x).length) (miss : y∉dualRow G x) :
    ∃ z, z∈dualRow G x ∧ z∉K := by
  apply Classical.byContradiction
  intro bad
  have nd := row_nodup G (noRepeatOnSphere G hh) x
  have my : y∈K.erase x := (List.mem_erase_of_ne dif.symm).mpr hy
  have subset : dualRow G x ⊆ (K.erase x).erase y := by
    intro z mz
    have notX : z≠x := fun eq => row_no_loop G hh x (eq ▸ mz)
    have notY : z≠y := fun eq => miss (eq ▸ mz)
    apply (List.mem_erase_of_ne notY).mpr
    apply (List.mem_erase_of_ne notX).mpr
    exact Classical.byContradiction (fun nz => bad ⟨z,mz,nz⟩)
  have bound := nd.length_le_of_subset subset
  rw [List.length_erase_of_mem my,List.length_erase_of_mem hx] at bound
  omega

/-- A chord of the five-cycle would put two rim vertices in different
components after deletion of its ends and the center. They cannot be adjacent,
so each has an outside neighbour by the six-vertex count. The connected
complement supplies a path between their outside neighbours. -/
theorem noRimDiagonal {M} (G : IsDiskFullerene M h) (hh : 3≤h)
    (K : List (Face M)) (len : K.length≤6)
    (off : apex M ∉ K) (c : Face M) (hc : c∈K) (closed : dualRow G c ⊆ K)
    (conn : ∀ x∉K, ∀ y∉K, OutsideWalk G K x y)
    (i j k l : Fin M.faces[c.val].length) (ij : i<j) (jk : j<k) (out : l<i ∨ k<l) :
    atSide G c k ∉ dualRow G (atSide G c i) := by
  intro chord
  obtain ⟨S,splitColor⟩ := separatesRim G hh c i j k l ij jk out chord
  let N := atSide G c
  have inj := atSide_inj G hh c
  have neigh z : N z ∈ dualRow G c := by dsimp [N]; rw [atSide_eq]; exact List.getElem_mem _
  have inside z := closed (neigh z)
  have safe z (a : z≠i) (b : z≠k) : Away c (N i) (N k) (N z) :=
    ⟨fun eq => row_no_loop G hh c (eq ▸ neigh z),fun eq => a (inj eq),fun eq => b (inj eq)⟩
  have sj := safe j (by omega) (by omega)
  have sl := safe l (by omega) (by omega)
  have miss : N l ∉ dualRow G (N j) := fun e => splitColor (S.edge_stays sj sl e)
  have miss' : N j ∉ dualRow G (N l) := fun e => miss ((dual_adj_symmetric G ..).mpr e)
  have anyDeg (v) (hv : v∈K) : 5≤(dualRow G v).length := by
    have h := inner_degree G (fun eq => off (eq ▸ hv)); omega
  have jl : N j≠N l := fun e => (by omega : j≠l) (inj e)
  obtain ⟨u,ju,uo⟩ := touches G hh len (inside j) (inside l) jl (anyDeg _ (inside j)) miss
  obtain ⟨v,lv,vo⟩ := touches G hh len (inside l) (inside j) jl.symm (anyDeg _ (inside l)) miss'
  have outSafe x (e : x∉K) : Away c (N i) (N k) x := ⟨fun q => e (q ▸ hc),
    fun q => e (q ▸ inside i),fun q => e (q ▸ inside k)⟩
  have w := conn u uo v vo
  have same {p q} (walk : OutsideWalk G K p q) : S.faceColor p ↔ S.faceColor q := by
    induction walk with
    | refl => rfl
    | step _ edge ih => exact ih.trans (S.edge_stays (outSafe _ edge.1) (outSafe _ edge.2.1) edge.2.2)
  exact splitColor ((S.edge_stays sj (outSafe _ uo) ju).trans ((same w).trans (S.edge_stays sl (outSafe _ vo) lv).symm))

private theorem rowStep {M} (G : IsDiskFullerene M h) (c : Face M)
    (i j : Fin M.faces[c.val].length) (atNext : next M.faces[c.val].length i.val=j.val) :
    atSide G c j ∈ dualRow G (atSide G c i) := by
  apply cyclic_link G c
  let r := dualRow G c
  have hi : i.val < r.length := by simp [r,row_length]
  have hj : j.val < r.length := by simp [r,row_length]
  have eq := side_at r i.val hi
  have e : next r.length i.val=j.val := by simpa [r,row_length] using atNext
  have idx : r[next r.length i.val]'(next_bound hi)=r[j.val]'hj := congrArg
    (fun a : Fin r.length => r[a.val]) (show (⟨_,next_bound hi⟩ : Fin r.length)=⟨_,hj⟩ from Fin.ext e)
  have mem := List.getElem_mem (l:=sides r) (n:=i.val) (by simpa [sides_size] using hi)
  rw [eq,idx] at mem
  simpa [r,atSide_eq] using mem

/-- On an actual input map, six interior vertices containing the whole link
of one of them, with connected complement, induce precisely the pentagonal
wheel. The labels of the rim are the five positions in the actual rotation
of the center. -/
theorem wheel {M} (G : IsDiskFullerene M h) (hh : 3≤h)
    (K : List (Face M)) (size : K.length=6) (off : apex M∉K)
    (c : Face M) (ic : c∈K) (closed : dualRow G c ⊆ K)
    (conn : ∀ x∉K, ∀ y∉K, OutsideWalk G K x y) :
    (dualRow G c).length=5 ∧ (∀ x, x∈K ↔ x=c ∨ x∈dualRow G c) ∧
      ∀ i k : Fin M.faces[c.val].length, i<k →
      (atSide G c k ∈ dualRow G (atSide G c i) ↔ k.val=i.val+1 ∨ (i.val=0 ∧ k.val=4)) := by
  have dg := inner_degree G (fun e => off (e ▸ ic))
  have nr := row_nodup G (noRepeatOnSphere G hh) c
  have away := row_no_loop G hh c
  have bound : dualRow G c ⊆ K.erase c := fun {v} hv =>
    (List.mem_erase_of_ne (show v≠c from fun e => away (e ▸ hv))).mpr (closed hv)
  have length := nr.length_le_of_subset bound
  rw [List.length_erase_of_mem ic] at length
  have five : (dualRow G c).length=5 := by omega
  have len : M.faces[c.val].length=5 := (row_length G c).symm.trans five
  refine ⟨five,?_,?_⟩
  · intro x
    constructor
    · intro hx
      by_cases eq : x=c
      · exact Or.inl eq
      · right; apply Classical.byContradiction; intro missing
        obtain ⟨z,mz,nz⟩ := touches G hh (by omega) ic hx (Ne.symm eq) (by omega) missing
        exact nz (closed mz)
    · rintro (rfl|m); exact ic; exact closed m
  · intro i k ik
    constructor
    · intro edge
      by_cases next : k.val=i.val+1
      · exact Or.inl next
      right
      let j : Fin M.faces[c.val].length := ⟨i.val+1,by omega⟩
      have ij : i<j := by change i.val<i.val+1; omega
      have jk : j<k := by change i.val+1<k.val; omega
      by_cases after : k.val+1 < M.faces[c.val].length
      · let l : Fin M.faces[c.val].length := ⟨k.val+1,after⟩
        exact False.elim (noRimDiagonal G hh K (by omega) off c ic closed conn i j k l ij jk
          (Or.inr (show k.val<k.val+1 by omega)) edge)
      · by_cases first : i.val=0
        · omega
        · let l : Fin M.faces[c.val].length := ⟨0,by omega⟩
          exact False.elim (noRimDiagonal G hh K (by omega) off c ic closed conn i j k l ij jk
            (Or.inl (show 0<i.val by omega)) edge)
    · rintro (e|⟨z,last⟩)
      · apply rowStep; unfold next; split <;> omega
      · apply (dual_adj_symmetric G ..).mpr
        apply rowStep; unfold next; split <;> omega

/-- When every selected vertex touches a connected complement, a triangle
on three selected vertices cannot cross either open arc of a selected link. -/
theorem openRim {M} (G : IsDiskFullerene M h) (hh : 3≤h) (K : List (Face M))
    (exposed : ∀ c∈K, ∃ z∈dualRow G c, z∉K)
    (conn : ∀ x∉K, ∀ y∉K, OutsideWalk G K x y)
    (c : Face M) (hc : c∈K) (i k : Fin M.faces[c.val].length) (ik : i<k)
    (ci : atSide G c i ∈ K) (ck : atSide G c k ∈ K)
    (e : atSide G c k ∈ dualRow G (atSide G c i)) :
    k.val=i.val+1 ∨ (i.val=0 ∧ k.val+1=M.faces[c.val].length) := by
  by_cases direct : k.val=i.val+1
  · exact Or.inl direct
  right
  let j : Fin M.faces[c.val].length := ⟨i.val+1,by omega⟩
  have ij : i<j := by change i.val<i.val+1; omega
  have jk : j<k := by change i.val+1<k.val; omega
  have exclude (l : Fin M.faces[c.val].length) (out : l<i ∨ k<l) : False := by
    obtain ⟨S,splitColor⟩ := separatesRim G hh c i j k l ij jk out e
    let N := atSide G c
    have inj := atSide_inj G hh c
    have good (q) (nq : q≠i) (nk : q≠k) : Away c (N i) (N k) (N q) := by
      have mem : N q∈dualRow G c := by dsimp [N]; rw [atSide_eq]; exact List.getElem_mem _
      exact ⟨fun eq => row_no_loop G hh c (eq ▸ mem),fun eq => nq (inj eq),fun eq => nk (inj eq)⟩
    have outGood (a) (na : a∉K) : Away c (N i) (N k) a :=
      ⟨fun q => na (q ▸ hc),fun q => na (q ▸ ci),fun q => na (q ▸ ck)⟩
    have reps (a) (sa : Away c (N i) (N k) a) : ∃ t, t∉K ∧ (S.faceColor a ↔ S.faceColor t) := by
      by_cases inside : a∈K
      · obtain ⟨t,at',nt⟩ := exposed a inside
        exact ⟨t,nt,S.edge_stays sa (outGood _ nt) at'⟩
      · exact ⟨a,inside,Iff.rfl⟩
    obtain ⟨u,nu,eq₁⟩ := reps (N j) (good j (by omega) (by omega))
    obtain ⟨v,nv,eq₂⟩ := reps (N l) (good l (by omega) (by omega))
    have same {a b} (w : OutsideWalk G K a b) : S.faceColor a ↔ S.faceColor b := by
      induction w with
      | refl => rfl
      | step _ edge ih => exact ih.trans (S.edge_stays (outGood _ edge.1) (outGood _ edge.2.1) edge.2.2)
    exact splitColor (eq₁.trans ((same (conn u nu v nv)).trans eq₂.symm))
  have first : i.val=0 := by
    apply Classical.byContradiction; intro no
    exact exclude ⟨0,by omega⟩ (Or.inl (show 0<i.val by omega))
  refine ⟨first,?_⟩
  apply Classical.byContradiction; intro no
  exact exclude ⟨k.val+1,by omega⟩ (Or.inr (show k.val<k.val+1 by omega))

private def unroll (n p a : Nat) := if p≤a then a-p else n+a-p

private theorem unroll_inj {n p a b : Nat} (hp : p<n) (ha : a<n) (hb : b<n)
    (eq : unroll n p a = unroll n p b) : a=b := by
  unfold unroll at eq; split at eq <;> split at eq <;> omega

/-- After cutting the vertex rotation at an exterior neighbor, all induced
link edges join consecutive positions in one linear order. -/
theorem openOrder {M} (G : IsDiskFullerene M h) (hh : 3≤h) (K : List (Face M))
    (exposed : ∀ c∈K, ∃ z∈dualRow G c, z∉K)
    (conn : ∀ x∉K, ∀ y∉K, OutsideWalk G K x y) (c : Face M) (hc : c∈K) :
    ∃ rank : Face M → Nat,
      (∀ a∈dualRow G c, ∀ b∈dualRow G c, rank a=rank b → a=b) ∧
      ∀ a∈dualRow G c, a∈K → ∀ b∈dualRow G c, b∈K → b∈dualRow G a →
        rank a+1=rank b ∨ rank b+1=rank a := by
  let R := dualRow G c
  obtain ⟨p,hp,pout⟩ := exposed c hc
  have pb := List.idxOf_lt_length_iff.mpr hp
  let pos (a : Face M) (ha : a∈R) : Fin M.faces[c.val].length :=
    ⟨R.idxOf a,by rw [←row_length G c]; exact List.idxOf_lt_length_iff.mpr ha⟩
  have atPos (a : Face M) (ha : a∈R) : atSide G c (pos a ha)=a := by
    rw [atSide_eq]; exact List.getElem_idxOf _
  let rank (a : Face M) := unroll R.length (R.idxOf p) (R.idxOf a)
  have idxinj (a b : Face M) (ia : a∈R) (ib : b∈R) (eq : R.idxOf a=R.idxOf b) : a=b :=
    (atPos a ia).symm.trans ((congrArg (atSide G c) (Fin.ext eq)).trans (atPos b ib))
  refine ⟨rank,fun a ia b ib eq => idxinj a b ia ib (unroll_inj pb
    (List.idxOf_lt_length_iff.mpr ia) (List.idxOf_lt_length_iff.mpr ib) eq),?_⟩
  intro a ia ka b ib kb edge
  have ai := List.idxOf_lt_length_iff.mpr ia
  have bi := List.idxOf_lt_length_iff.mpr ib
  have ap : R.idxOf a≠R.idxOf p := fun eq => pout ((idxinj a p ia hp eq) ▸ ka)
  have bp : R.idxOf b≠R.idxOf p := fun eq => pout ((idxinj b p ib hp eq) ▸ kb)
  have ab : R.idxOf a≠R.idxOf b := fun eq => row_no_loop G hh b ((idxinj a b ia ib eq) ▸ edge)
  have forward {v w : Face M} (hv : v∈R) (hw : w∈R) (kv : v∈K) (kw : w∈K)
      (ord : R.idxOf v < R.idxOf w) (e : w∈dualRow G v) :
      R.idxOf w=R.idxOf v+1 ∨ (R.idxOf v=0 ∧ R.idxOf w+1=R.length) := by
    have H := openRim G hh K exposed conn c hc (pos v hv) (pos w hw) ord
      (by rwa [atPos v hv]) (by rwa [atPos w hw]) (by rwa [atPos v hv,atPos w hw])
    simpa [pos,R,row_length] using H
  have order : R.idxOf b=R.idxOf a+1 ∨ (R.idxOf a=0 ∧ R.idxOf b+1=R.length) ∨
      R.idxOf a=R.idxOf b+1 ∨ (R.idxOf b=0 ∧ R.idxOf a+1=R.length) := by
    by_cases lt : R.idxOf a<R.idxOf b
    · rcases forward ia ib ka kb lt edge with h|h; exact Or.inl h; exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (forward ib ia kb ka (by omega) ((dual_adj_symmetric G ..).mp edge)))
  change R.idxOf p<R.length at pb
  change R.idxOf a<R.length at ai
  change R.idxOf b<R.length at bi
  dsimp [rank,unroll]; split <;> split <;> omega

end DiskFullerene.EndSix
