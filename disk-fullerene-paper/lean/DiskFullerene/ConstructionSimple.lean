import DiskFullerene.ConstructionWords

namespace DiskFullerene.PrimalSplice

private structure Safe (w : Word) (m : Nat) : Prop where
  unique : w.Nodup
  bounded : ∀ x ∈ w, x < m

private theorem Safe.mono (h : Safe w m) (le : m ≤ k) : Safe w k :=
  ⟨h.unique,fun x hx => Nat.lt_of_lt_of_le (h.bounded x hx) le⟩

private theorem Safe.rev (h : Safe w m) : Safe w.reverse m :=
  ⟨(List.reverse_perm _).nodup_iff.mpr h.unique,fun x hx => h.bounded x (List.mem_reverse.mp hx)⟩

private theorem Safe.extend (h : Safe w m) (hs : tail.Nodup)
    (hb : ∀ x ∈ tail, m≤x ∧ x<k) (le : m ≤ k) : Safe (w++tail) k := by
  constructor
  · apply List.nodup_append.mpr
    exact ⟨h.unique,hs,fun x hx y hy eq => (Nat.not_le_of_lt (h.bounded x hx)) (eq ▸ (hb y hy).1)⟩
  · intro x hx; obtain old|new := List.mem_append.mp hx
    · exact (h.mono le).bounded x old
    · exact (hb x new).2

private structure SafePatch (p : OpenPatch) (m : Nat) : Prop where
  closed : ∀ w ∈ p.closed, Safe w m
  w : Safe p.w m
  x : Safe p.x m
  y : Safe p.y m

private theorem capSafe (p : OpenPatch) (which : p=leftPatch ∨ p=rightPatch) : SafePatch p 22 := by
  have c : (p.closed ++ [p.w,p.x,p.y]).all (fun w => w.Nodup && w.all (·<22)) := by
    rcases which with rfl|rfl <;> decide
  have bound (w) (mem : w ∈ p.closed ++ [p.w,p.x,p.y]) : Safe w 22 := by
    have b := List.all_eq_true.mp c w mem
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at b
    exact ⟨b.1,b.2⟩
  exact ⟨fun w hw => bound w (by simp [hw]),bound _ (by simp),bound _ (by simp),bound _ (by simp)⟩

private theorem SafePatch.step (h : SafePatch p m) :
    SafePatch (p.step m) (m+4) := by
  have xs := h.x.extend (k:=m+4) (tail:=[m+3,m+2]) (by simp) (by intro x hx; simp at hx; omega) (by omega)
  have ws := h.w.extend (k:=m+4) (tail:=[m+2]) (by simp) (by intro x hx; simp at hx; omega) (by omega)
  have ys : Safe ((m+3)::p.y) (m+4) := by
    constructor
    · apply List.nodup_cons.mpr; exact ⟨fun hy => by have := h.y.bounded _ hy; omega,h.y.unique⟩
    · intro x hx; obtain e|e := List.mem_cons.mp hx
      · omega
      · have := h.y.bounded _ e; omega
  refine ⟨?_,ws.rev,ys.rev,?_⟩
  · intro u hu; obtain ⟨w,mem,rfl⟩ := List.mem_map.mp hu
    obtain first|rest := List.mem_cons.mp mem
    · exact first ▸ xs.rev
    · exact ((h.closed _ rest).mono (by omega)).rev
  · exact ⟨show [m+3,m+2].Nodup by simp,by intro j hj; change j ∈ [m+3,m+2] at hj; simp at hj; omega⟩

private theorem openSafe (k : Nat) : SafePatch (openWords k) (22+4*k) := by
  induction k with
  | zero => exact capSafe _ (Or.inl rfl)
  | succ k ih => exact ih.step

private theorem closedAcross (u v : Word) (hu : Safe u m) (hv : v.Nodup) :
    (u ++ (v.map (m+·)).reverse).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hu.unique,(List.reverse_perm _).nodup_iff.mpr (List.pairwise_map.mpr (hv.imp (fun h eq => h (Nat.add_left_cancel eq)))),?_⟩
  intro x hx y hy eq
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hy)
  have := hu.bounded _ hx; omega

theorem primalFacesSimple (n : Nat) : ∀ w ∈ (primalWords n).1 :: (primalWords n).2, w.Nodup := by
  let m := 22+4*(n+2)
  have l := openSafe (n+2)
  have r := capSafe rightPatch (Or.inr rfl)
  intro w mem
  change w ∈ _ :: (((_ :: _ :: (openWords (n+2)).closed) ++ _)) at mem
  rcases List.mem_cons.mp mem with rfl|mem
  · exact closedAcross _ _ l.w r.w.unique
  rcases List.mem_append.mp mem with mem|mem
  · rcases List.mem_cons.mp mem with rfl|mem
    · exact closedAcross _ _ l.x r.x.unique
    rcases List.mem_cons.mp mem with rfl|mem
    · exact closedAcross _ _ l.y r.y.unique
    · exact (l.closed _ mem).unique
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp mem
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact (List.reverse_perm _).nodup_iff.mpr (List.pairwise_map.mpr ((r.closed _ hv).unique.imp (fun h eq => h (Nat.add_left_cancel eq))))

end DiskFullerene.PrimalSplice
