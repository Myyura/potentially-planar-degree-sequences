import StackedCensusChecks
import Mathlib.Tactic.IntervalCases

namespace Recognition.StackedCensus
open CensusEncoding StackedQuota StackedHistory

private theorem triples_checked (a b c : Nat) (size : a+b+c ≤ 7) : triples a b c = true := by
  have check (n : Nat) (small : n≤7) : ∀ i j : Fin (n+1), i.val+j.val ≤ n →
      triples i.val j.val (n-i.val-j.val) = true := by
    interval_cases n
    · exact tri0
    · exact tri1
    · exact tri2
    · exact tri3
    · exact tri4
    · exact tri5
    · exact tri6
    · exact tri7
  have h := check (a+b+c) size ⟨a,by omega⟩ ⟨b,by omega⟩ (by simp)
  simpa only [show a+b+c-a-b = c by omega] using h

private theorem quads_checked (a b c d : Nat) (size : a+b+c+d ≤ 8) :
    quadruples a b c d = true := by
  have check (n : Nat) (small : n≤8) : ∀ i j k : Fin (n+1), i.val+j.val+k.val ≤ n →
      quadruples i.val j.val k.val (n-i.val-j.val-k.val) = true := by
    interval_cases n
    · exact quad0
    · exact quad1
    · exact quad2
    · exact quad3
    · exact quad4
    · exact quad5
    · exact quad6
    · exact quad7
    · exact quad8
  have h := check (a+b+c+d) size ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨c,by omega⟩ (by simp)
  simpa only [show a+b+c+d-a-b-c = d by omega] using h

/-- Every possible three-disk construction occurs in the checked directory. -/
theorem disk_complete (t : Disk) (small : t.size ≤ 8) :
    (diskDir t.size).find (diskKey t) = some () := by
  induction t with
  | empty => exact disk_base
  | split a b c ha hb hc =>
    simp only [Disk.size] at small ⊢
    have x : a.size ≤ 8 := by omega
    have y : b.size ≤ 8 := by omega
    have z : c.size ≤ 8 := by omega
    rw [combine_key a b c x y z]
    have h := triples_checked a.size b.size c.size (by omega)
    unfold triples at h
    have h₁ := Directory.checked _ h (ha x)
    have h₂ := Directory.checked _ h₁ (hb y)
    have h₃ := Directory.checked _ h₂ (hc z)
    obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp h₃
    exact hu

private theorem shell_complete (s : Shell) (small : s.profile.length ≤ 12) :
    ((shellDir (s.profile.length-4)).find (code s.profile)).isSome = true := by
  have eq := shell_length s
  have sm : s.abc.size+s.abd.size+s.acd.size+s.bcd.size ≤ 8 := by omega
  have h := quads_checked _ _ _ _ sm
  unfold quadruples at h
  have hp := Directory.checked _ h (disk_complete s.abc (by omega))
  have hq := Directory.checked _ hp (disk_complete s.abd (by omega))
  have hr := Directory.checked _ hq (disk_complete s.acd (by omega))
  have hs := Directory.checked _ hr (disk_complete s.bcd (by omega))
  rw [shell_key s (by omega) (by omega) (by omega) (by omega),show s.profile.length-4 =
    s.abc.size+s.abd.size+s.acd.size+s.bcd.size by omega]
  exact hs

/-- For every row of a census order, dictionary membership means existence
of a tetrahedral insertion history with exactly that degree multiset. -/
theorem checked_realization (d : List Nat) (lo : 4 ≤ d.length) (hi : d.length ≤ 12) :
    ((shellDir (d.length-4)).find (code d)).isSome = true ↔ SequentialRealization (d : Multiset Nat) := by
  rw [←accepts_iff_sequential,acceptance_iff]
  constructor
  · intro present
    obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp present
    have checked := sample_valid ⟨d.length-4,by omega⟩
    change (shellDir (d.length-4)).every _ = true at checked
    have props := of_decide_eq_true (Directory.checked _ checked hs)
    have p := (code_iff (d:=s.profile) (e:=d) (by omega) (by omega)).mp props.1
    exact ⟨s,by rw [shell_degrees]; exact Quot.sound p.symm⟩
  · rintro ⟨s,eq⟩
    rw [shell_degrees] at eq
    have p : d.Perm s.profile := Quotient.exact eq
    have len := p.length_eq
    have same : code d = code s.profile := (p.map _).sum_eq
    rw [same,len]
    exact shell_complete s (by omega)

noncomputable def actualRows (n : Nat) : List (List Nat) := by
  classical
  exact (candidates n).filter fun d => decide (SequentialRealization (d : Multiset Nat))

private theorem recognition_exact (n : Nat) (lo : 4≤n) (hi : n≤12) : recognized n = actualRows n := by
  classical
  unfold recognized actualRows
  apply List.filter_congr
  intro d hd
  have len := ((rows_iff _ _ _ d).mp hd).1
  change d.length = n at len
  have equivalence := checked_realization d (by omega) (by omega)
  rw [len] at equivalence
  by_cases yes : SequentialRealization (d : Multiset Nat)
  · simpa [yes] using equivalence.mpr yes
  · simpa [yes] using Bool.eq_false_iff.mpr (fun h => yes (equivalence.mp h))

theorem stacked_counts : ([4,5,6,7,8,9,10,11,12].map fun n => (actualRows n).length) =
    [1,1,1,3,7,19,51,132,307] := by
  rw [←recognized_counts]
  apply List.map_congr_left
  intro n mem
  rw [recognition_exact n (by simp at mem; omega) (by simp at mem; omega)]

theorem census_totals :
    ([4,5,6,7,8,9,10,11,12].map fun n => (candidates n).length).sum = 1350 ∧
    ([4,5,6,7,8,9,10,11,12].map fun n => (actualRows n).length).sum = 522 := by
  rw [candidate_counts,stacked_counts]
  decide

end Recognition.StackedCensus
