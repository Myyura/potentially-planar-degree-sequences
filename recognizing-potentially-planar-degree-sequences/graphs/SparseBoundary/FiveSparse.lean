import SparseBoundary.GraphFiveCore
import SparseBoundary.GraphPetals
import SparseBoundary.FanPlanar
import SparseBoundary.FanGraphicNecessity

namespace SparseBoundary

/-- Extend a suffix of twos by arbitrary edge subdivisions. -/
theorem pad_twos {h : List Nat} {s t : Nat} (hp : Planaric (h++List.replicate s 2))
    (nonzero : ∃ x∈h,0<x) (le : s≤t) : Planaric (h++List.replicate t 2) := by
  have positive : ∃ x∈h++List.replicate s 2,0<x := by
    obtain ⟨x,hx,he⟩ := nonzero
    exact ⟨x,List.mem_append_left _ hx,he⟩
  have q := planaric_add_twos hp positive (t-s)
  have perm := List.perm_append_comm (l₁:=List.replicate (t-s) 2) (l₂:=h++List.replicate s 2)
  have eq : List.replicate s 2 ++ List.replicate (t-s) 2 = List.replicate t 2 :=
    List.eq_replicate_iff.mpr ⟨by simp; omega,by simp⟩
  simpa only [List.append_assoc,eq] using (planaric_perm perm).mp q

private theorem five_regular_two : Planaric [4,4,4,4,4,2,2] := by
  let G : Graph 7 := ⟨1134330⟩
  have hp : Planaric [4,4,2,4,4,4,2] := ⟨G,by unfold Graph.Realizes; decide,
    Fan.two_apex_path_planar (by unfold Fan.TwoApexPath; decide)⟩
  exact (planaric_perm (d:=[4,4,2,4,4,4,2]) (by decide)).mp hp

private theorem five_hub (b c d e k : Nat) :
    let m := b+c+d+e
    Planaric ([4+m+2*k,4+b,4+c,3+d,3+e] ++ List.replicate (m+2*k) 2) := by
  let m := b+c+d+e
  have h := Graph.Bipyramid.realize m b c d e m (by dsimp [m];omega) (by omega)
    (by dsimp [m];omega) (by dsimp [m];omega) (by dsimp [m];omega)
  have p := planaric_petals h k
  let t := [4+b,4+c,3+d,3+e]
  have perm := List.perm_append_comm (l₁:=List.replicate (2*k) 2) (l₂:=t++List.replicate m 2)
  have eqn : List.replicate m 2 ++ List.replicate (2*k) 2 = List.replicate (m+2*k) 2 :=
    List.eq_replicate_iff.mpr ⟨by simp,by simp⟩
  exact (planaric_perm ((by simpa only [List.append_assoc,eqn] using perm :
    (List.replicate (2*k) 2 ++ (t++List.replicate m 2)).Perm (t++List.replicate (m+2*k) 2)).cons _)).mp p

/-- Five core entries of at least four, at every lower volume including
    all strictly sparser sequences. The potentially dominant vertex is
    treated by petals when the ordinary degree cap is the active bound. -/
theorem five_sparse_high (a b c d e t : Nat)
    (hab : b≤a) (hbc : c≤b) (hcd : d≤c) (hde : e≤d) (he : 4≤e)
    (bound : a+b+c+d+e ≤ 18+2*t)
    (hg : Graphic ([a,b,c,d,e] ++ List.replicate t 2))
    (hex : ([a,b,c,d,e] ++ List.replicate t 2) ≠ lowerException) :
    Planaric ([a,b,c,d,e] ++ List.replicate t 2) := by
  have eg := ErdosGallai.eg_of_graphic hg
  have parity := eg.1
  have cap := eg.2 1 (by simp)
  simp [List.sum_replicate_nat,List.map_replicate,show min 1 b=1 by omega,
    show min 1 c=1 by omega,show min 1 d=1 by omega,show min 1 e=1 by omega] at cap
  simp [List.sum_replicate_nat] at parity
  have positive : ∃ x ∈ [a,b,c,d,e], 0<x := ⟨a,by simp,by omega⟩
  by_cases reg : a=4
  · have eqs : b=4 ∧ c=4 ∧ d=4 ∧ e=4 := by omega
    obtain ⟨rfl,rfl,rfl,rfl⟩ := eqs
    subst a
    have lt2 : 2≤t := by
      have nt : t≠1 := by rintro rfl; exact hex rfl
      omega
    exact pad_twos (s:=2) five_regular_two positive lt2
  let m := (a+b+c+d+e-18)/2
  have budget : a+b+c+d+e=18+2*m := by dsimp [m]; omega
  by_cases dom : m < a-4
  · let s := (b-4)+(c-4)+(d-3)+(e-3)
    have hh := five_hub (b-4) (c-4) (d-3) (e-3) (a-4-m)
    change Planaric ([4+s+2*(a-4-m),4+(b-4),4+(c-4),3+(d-3),3+(e-3)] ++
      List.replicate (s+2*(a-4-m)) 2) at hh
    have eq : 4+s+2*(a-4-m)=a := by dsimp [s]; omega
    simp only [eq,show 4+(b-4)=b by omega,show 4+(c-4)=c by omega,
      show 3+(d-3)=d by omega,show 3+(e-3)=e by omega] at hh
    apply pad_twos hh positive
    dsimp [s]; omega
  · have pl := Graph.Bipyramid.realize (a-4) (b-4) (c-4) (d-3) (e-3) m
      (by omega) (by omega) (by omega) (by omega) (by omega)
    apply pad_twos (s:=m) _ positive (by omega)
    simpa only [show 4+(a-4)=a by omega,show 4+(b-4)=b by omega,
      show 4+(c-4)=c by omega,show 3+(d-3)=d by omega,show 3+(e-3)=e by omega] using pl

theorem lower_sparse_at_most_five {h : List Nat} {t : Nat}
    (core : Core h) (few : h.length≤5) (hg : Graphic (profile h t 0))
    (bound : (profile h t 0).sum+2≤4*(profile h t 0).length) :
    Planaric (profile h t 0) ↔ profile h t 0 ≠ lowerException := by
  constructor
  · exact fun hp eq => lower_necessary hp (eq ▸ List.Perm.rfl)
  intro no
  by_cases low : (h.filter (fun x => decide (4≤x))).length≤4
  · apply planaric_of_small_core hg
    · simp [profile]; exact Nat.le_trans (List.length_filter_le _ _) few
    · simpa [profile] using low
  · have cap := List.length_filter_le (fun x => decide (4≤x)) h
    have len : h.length=5 := by omega
    have min (x) (hx : x∈h) : 4≤x := of_decide_eq_true (List.length_filter_eq_length_iff.mp
      (show (h.filter (fun x => decide (4≤x))).length=h.length by omega) x hx)
    match h with
    | [a,b,c,d,e] =>
      have order := core.1
      simp at order
      simp only [profile,List.replicate_zero,List.append_nil]
      apply five_sparse_high a b c d e t (by grind) (by grind) (by grind) (by grind)
        (min e (by simp)) _ (by simpa [profile] using hg) (by simpa [profile] using no)
      simp [profile,List.sum_replicate_nat] at bound
      omega
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | _::_::_::_::_::_::_ => simp at len

end SparseBoundary
