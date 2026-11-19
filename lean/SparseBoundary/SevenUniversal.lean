import SparseBoundary.MinorGroups
import SparseBoundary.GraphWeighted
import SparseBoundary.GraphPerm

namespace SparseBoundary.SevenUniversal
open Graph MinorSearch

namespace Layer0

private def realization : Graph 7 := ⟨827119⟩
private def initial : Nat := 0xfeeefaaaffeffbabfeeefaffffeffbfe
private def catalog : Array (Option Nat) := ((List.range 128).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 7).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 7 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

def wheel : Graph 7 := realization

theorem wheel_planar : wheel.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

theorem support : ∃ H : Graph 7, H.Planar ∧
    List.ofFn H.degree = [6, 4, 4, 4, 4, 3, 3] ∧
    ∀ i : Fin 7, i ≠ 0 → H.adj 0 i = true :=
  ⟨realization,wheel_planar,by decide +kernel,by decide⟩

end Layer0

namespace Layer1

private def realization : Graph 7 := ⟨1164671⟩
private def initial : Nat := 0xfeffeeefeaeaeeeffafbaaabfafbfffe
private def catalog : Array (Option Nat) := ((List.range 128).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 7).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 7 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

theorem support : ∃ H : Graph 7, H.Planar ∧
    List.ofFn H.degree = [6, 4, 4, 3, 3, 3, 3] ∧
    ∀ i : Fin 7, i ≠ 0 → H.adj 0 i = true :=
  ⟨realization,planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel),by decide +kernel,by decide⟩

end Layer1

private theorem labels (f : Fin 7 → Nat) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6] := rfl

/-- The polygon and its noncrossing chord or chords supply the support.
    Each extra spoke increases the central degree and a prescribed
    peripheral degree while introducing one new degree-two vertex. -/
private theorem spokes (H : Graph 7) (hp : H.Planar) (univ : ∀ i : Fin 7, i ≠ 0 → H.adj 0 i = true)
    (a b c d e f t : Nat) (ht : a+b+c+d+e+f=t) :
    Planaric ([H.degree 0+t,H.degree 1+a,H.degree 2+b,H.degree 3+c,
      H.degree 4+d,H.degree 5+e,H.degree 6+f] ++ List.replicate t 2) := by
  let E : List (Fin 7 × Fin 7) := List.replicate a (0,1) ++ List.replicate b (0,2) ++
    List.replicate c (0,3) ++ List.replicate d (0,4) ++ List.replicate e (0,5) ++ List.replicate f (0,6)
  have good q (hq : q ∈ E) : H.adj q.1 q.2 = true := by
    simp only [E,List.mem_append,List.mem_replicate] at hq
    rcases hq with (((((⟨_,rfl⟩|⟨_,rfl⟩)|⟨_,rfl⟩)|⟨_,rfl⟩)|⟨_,rfl⟩)|⟨_,rfl⟩) <;>
      apply univ <;> decide
  have lens : E.length = t := by simpa [E,Nat.add_assoc] using ht
  have sum : [increments E 0,increments E 1,increments E 2,increments E 3,
      increments E 4,increments E 5,increments E 6] = [t,a,b,c,d,e,f] := by
    simp only [E,increments,List.countP_append,List.countP_replicate]
    change [a+b+c+d+e+f,a+0+0+0+0+0,0+b+0+0+0+0,0+0+c+0+0+0,
      0+0+0+d+0+0,0+0+0+0+e+0,0+0+0+0+0+f] = _
    simp [ht]
  simp only [List.cons.injEq,and_true] at sum
  obtain ⟨s0,s1,s2,s3,s4,s5,s6⟩ := sum
  have pl := expanded_planaric hp E good
  rw [labels] at pl
  simp only [lens,s0,s1,s2,s3,s4,s5,s6] at pl
  exact (planaric_perm List.perm_append_comm).mp pl

theorem upper (b c d e f g t : Nat) (hb : 4≤b) (hc : 4≤c) (hd : 4≤d) (he : 4≤e) (hf : 3≤f) (hg : 3≤g)
    (sum : b+c+d+e+f+g = 22+t) :
    Planaric ([6+t,b,c,d,e,f,g] ++ List.replicate t 2) := by
  obtain ⟨H,hp,deg,hu⟩ := Layer0.support
  have p := spokes H hp hu (b-4) (c-4) (d-4) (e-4) (f-3) (g-3) t (by omega)
  rw [labels] at deg
  simp only [List.cons.injEq,and_true] at deg
  obtain ⟨d0,d1,d2,d3,d4,d5,d6⟩ := deg
  simpa only [d0,d1,d2,d3,d4,d5,d6, show 4+(b-4)=b by omega, show 4+(c-4)=c by omega, show 4+(d-4)=d by omega, show 4+(e-4)=e by omega, show 3+(f-3)=f by omega, show 3+(g-3)=g by omega] using p

theorem lower (b c d e f g t : Nat) (hb : 4≤b) (hc : 4≤c) (hd : 3≤d) (he : 3≤e) (hf : 3≤f) (hg : 3≤g)
    (sum : b+c+d+e+f+g = 20+t) :
    Planaric ([6+t,b,c,d,e,f,g] ++ List.replicate t 2) := by
  obtain ⟨H,hp,deg,hu⟩ := Layer1.support
  have p := spokes H hp hu (b-4) (c-4) (d-3) (e-3) (f-3) (g-3) t (by omega)
  rw [labels] at deg
  simp only [List.cons.injEq,and_true] at deg
  obtain ⟨d0,d1,d2,d3,d4,d5,d6⟩ := deg
  simpa only [d0,d1,d2,d3,d4,d5,d6, show 4+(b-4)=b by omega, show 4+(c-4)=c by omega, show 3+(d-3)=d by omega, show 3+(e-3)=e by omega, show 3+(f-3)=f by omega, show 3+(g-3)=g by omega] using p

end SparseBoundary.SevenUniversal
