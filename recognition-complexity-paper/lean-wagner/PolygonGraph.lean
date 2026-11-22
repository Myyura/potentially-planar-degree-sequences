import PolygonMidpoint

namespace Recognition.PolygonMidpoint

def Shape.edges : Shape → Nat → List (Nat × Nat)
  | .edge, a => [(a,a+1)]
  | .triangle l r, a =>
    l.edges a ++ r.edges (a+1+l.size) ++ [(a,a+2+l.size+r.size)]

theorem Shape.edge_bounds (t : Shape) (a : Nat) {i j : Nat} (h : (i,j) ∈ t.edges a) :
    a ≤ i ∧ i < j ∧ j ≤ a+t.size+1 := by
  induction t generalizing a with
  | edge => simp [Shape.edges] at h; simp [Shape.size]; omega
  | triangle l r L R =>
    simp only [Shape.edges,List.mem_append,List.mem_singleton,Prod.mk.injEq] at h
    simp only [Shape.size]
    rcases h with ((h|h)|h)
    · have := L _ h; omega
    · have := R _ h; omega
    · omega

def valence (es : List (Nat × Nat)) (x : Nat) : Nat :=
  (es.filter (fun e => e.1==x || e.2==x)).length

@[simp] theorem valence_append (es fs : List (Nat × Nat)) (x : Nat) :
    valence (es++fs) x = valence es x + valence fs x := by simp [valence]

@[simp] theorem valence_singleton (u v x : Nat) : valence [(u,v)] x =
    (if u=x ∨ v=x then 1 else 0) := by
  by_cases a : u=x <;> by_cases b : v=x <;> simp [valence,a,b]

private theorem far (t : Shape) (a x) (h : x<a ∨ a+t.size+1<x) :
    valence (t.edges a) x = 0 := by
  unfold valence
  rw [List.length_eq_zero_iff,List.filter_eq_nil_iff]
  rintro ⟨i,j⟩ mem
  have := t.edge_bounds a mem
  simp [show i≠x by omega,show j≠x by omega]

def Shape.interiorNames : Shape → Nat → List Nat
  | .edge, _ => []
  | .triangle l r, a =>
    l.interiorNames a ++ [a+1+l.size] ++ r.interiorNames (a+1+l.size)

private theorem append_ranges (a n m : Nat) :
    List.range' a n ++ List.range' (a+n) m = List.range' a (n+m) := by
  have h := List.range'_append (s:=a) (m:=n) (n:=m) (step:=1)
  simpa only [Nat.one_mul] using h

theorem Shape.interior_range (t : Shape) (a) :
    t.interiorNames a = List.range' (a+1) t.size := by
  induction t generalizing a with
  | edge => rfl
  | triangle l r L R =>
    simp only [Shape.interiorNames, L, R, Shape.size]
    rw [show [a+1+l.size] = List.range' (a+1+l.size) 1 from rfl]
    rw [append_ranges,show a+1+l.size+1 = a+1+(l.size+1) by omega,append_ranges,
        show l.size+1+r.size = l.size+r.size+1 by omega]

private theorem interior_bounds (t : Shape) (a x) (m : x ∈ t.interiorNames a) :
    a<x ∧ x<a+t.size+1 := by
  rw [t.interior_range] at m
  have h := List.mem_range'.mp m
  obtain ⟨i,hi,e⟩ := h
  simp only [Nat.one_mul] at e
  omega

private theorem boundary_parts (t : Shape) (a : Nat) :
    valence (t.edges a) a = t.row.first ∧
    valence (t.edges a) (a+t.size+1) = t.row.last ∧
    (t.interiorNames a).map (valence (t.edges a)) = t.row.inside := by
  induction t generalizing a with
  | edge => simp [Shape.edges,Shape.size,Shape.row,Shape.interiorNames,valence]
  | triangle l r L R =>
    let m := a+1+l.size
    let z := a+2+l.size+r.size
    obtain ⟨lf,ll,li⟩ := L a
    obtain ⟨rf,rr,ri⟩ := R m
    have lm : a+l.size+1=m := by dsimp [m];omega
    have rz : m+r.size+1=z := by dsimp [m,z];omega
    have az : a<z := by dsimp [z];omega
    have am : a<m := by dsimp [m];omega
    have mz : m<z := by dsimp [m,z];omega
    rw [lm] at ll
    rw [rz] at rr
    have cl (x) (h : x∈l.interiorNames a) :
        valence (l.edges a ++ r.edges m ++ [(a,z)]) x = valence (l.edges a) x := by
      obtain ⟨ax,xm⟩ := interior_bounds _ _ _ h
      rw [lm] at xm
      simp [far r m x (.inl xm),valence_singleton,show a≠x by omega,show z≠x by omega]
    have cr (x) (h : x∈r.interiorNames m) :
        valence (l.edges a ++ r.edges m ++ [(a,z)]) x = valence (r.edges m) x := by
      obtain ⟨mx,xz⟩ := interior_bounds _ _ _ h
      rw [rz] at xz
      simp [far l a x (.inr (lm ▸ mx)),valence_singleton,show a≠x by omega,show z≠x by omega]
    change valence (l.edges a ++ r.edges m ++ [(a,z)]) a = l.row.first+1 ∧
      valence (l.edges a ++ r.edges m ++ [(a,z)]) (a+(l.size+r.size+1)+1) = r.row.last+1 ∧
      (l.interiorNames a ++ [m] ++ r.interiorNames m).map
        (valence (l.edges a ++ r.edges m ++ [(a,z)])) =
        l.row.inside ++ [l.row.last+r.row.first] ++ r.row.inside
    rw [show a+(l.size+r.size+1)+1=z by dsimp [z];omega]
    refine ⟨?_,?_,?_⟩
    · simp [far r m a (.inl am),lf,valence_singleton]
    · simp [far l a z (.inr (lm ▸ mz)),rr,valence_singleton]
    · rw [List.map_append,List.map_append,
          List.map_congr_left (fun x hx => cl x hx),
          List.map_congr_left (fun x hx => cr x hx),li,ri]
      simp [ll,rf,valence_singleton,show a≠m by omega,show z≠m by omega]

theorem Shape.degree_row (t : Shape) (a : Nat) :
    (List.range' a (t.size+2)).map (valence (t.edges a)) = t.row.vertices := by
  obtain ⟨f,l,ins⟩ := boundary_parts t a
  rw [t.interior_range] at ins
  have e : List.range' a (t.size+2) = a :: (List.range' (a+1) t.size ++ [a+t.size+1]) := by
    rw [show a+t.size+1 = a+1+t.size by omega]
    rw [show [a+1+t.size] = List.range' (a+1+t.size) 1 from rfl]
    rw [append_ranges]
    exact List.range'_succ
  rw [e]
  simp [Row.vertices,f,l,ins]

end Recognition.PolygonMidpoint
