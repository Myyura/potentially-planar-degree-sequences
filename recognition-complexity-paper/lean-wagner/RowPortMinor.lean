import RowPlane
import LeanPool.K5MinorFreeChoosability.Planar.MinorClosed

/-! Vertex identities and graph minors in the strip drawing. -/
namespace Recognition.RowPortMinor
open Recognition.RowRule Recognition.RowPlane LeanPool.K5MinorFreeChoosability

private theorem head_list {l : List Nat} (short : l.length≤1) : l.head?.toList=l := by
  cases l with
  | nil => rfl
  | cons a l => cases l <;> simp_all

theorem upper_unique {s d} (g : Valid s) (c : Choice s d) :
    (c.upper.filterMap id).Nodup := by
  have cut : (c.left++c.first++(c.last++c.right)).Sublist s.row := by
    rw [c.split]
    simpa only [List.append_assoc] using
      ((List.sublist_append_right c.middle (c.last++c.right)).append_left (c.left++c.first))
  have old := cut.nodup g.nodup
  have fresh : s.n ∉ c.left++c.first++(c.last++c.right) := by
    intro h
    exact (Nat.lt_irrefl _) ((g.active s.n).mp (cut.subset h)).1
  have all := List.nodup_cons.mpr ⟨fresh,old⟩
  have per := (List.perm_middle (a:=s.n) (l₁:=c.left++c.first) (l₂:=c.last++c.right)).nodup_iff.mpr all
  have U : c.upper.filterMap id = (c.left++c.first)++s.n::(c.last++c.right) := by
    generalize hf : c.first = fs
    generalize hl : c.last = ls
    unfold Choice.upper
    rw [hf,hl]
    have f := hf ▸ c.firstSize
    have l := hl ▸ c.lastSize
    cases fs with
    | nil =>
      cases ls with
      | nil => simp
      | cons x tail => cases tail <;> simp_all
    | cons x tail =>
      cases tail
      · cases ls with
        | nil => simp
        | cons y rem => cases rem <;> simp_all
      · simp_all
  rw [U]; exact per

theorem option_index {xs : List (Option Nat)} (nd : (xs.filterMap id).Nodup)
    {i j v : Nat} (a : xs[i]?=some (some v)) (b : xs[j]?=some (some v)) : i=j := by
  induction xs generalizing i j with
  | nil => simp at a
  | cons h tail ih =>
    cases h with
    | none =>
      cases i <;> cases j <;> simp_all
      exact ih a b
    | some h =>
      have g : h ∉ tail.filterMap id ∧ (tail.filterMap id).Nodup := by simpa using nd
      have gone {k : Nat} (hk : tail[k]?=some (some h)) : False := by
        exact g.1 (List.mem_filterMap.mpr ⟨some h,List.mem_of_getElem? hk,rfl⟩)
      cases i <;> cases j <;> simp_all
      exact ih a b

theorem birth_port {s d} (c : Choice s d) :
    c.upper[c.left.length+1]?=some (some s.n) := by
  unfold Choice.upper
  rw [List.getElem?_append_right (by simp)]
  simp

/-- A surviving old name follows two consecutive strokes through the
same intermediate port, from its old place to the prescribed new place. -/
theorem through_old {s d} (g : Valid s) (c : Choice s d) {j v : Nat}
    (next : (RowRule.step c).row[j]? = some v) (old : v ≠ s.n) :
    ∃ i k, Stroke c i k v v ∧ Repack c.livePorts k j v := by
  obtain ⟨k,rep,hk⟩ := next_port_connected g c next
  obtain ⟨i,m,st⟩ := (fan_strip_covers_step c).2 v (List.mem_of_getElem? next) old
  have eq := option_index (upper_unique g c) (Option.join_eq_some_iff.mp st.ports.2) hk
  exact ⟨i,k,eq ▸ st,rep⟩

theorem through_birth {s d} (g : Valid s) (c : Choice s d) {j : Nat}
    (next : (RowRule.step c).row[j]? = some s.n) :
    Repack c.livePorts (c.left.length+1) j s.n := by
  obtain ⟨k,rep,hk⟩ := next_port_connected g c next
  exact (option_index (upper_unique g c) hk (birth_port c)) ▸ rep

theorem port_bounds (w t : Nat) {i : Nat} (hi : i<w) :
    t*w ≤ slot w t i ∧ slot w t i < (t+1)*w := by
  unfold slot; rw [Nat.add_mul,Nat.one_mul];split <;> omega

theorem slot_injective {w a b i j : Nat} (hi : i<w) (hj : j<w)
    (eq : slot w a i = slot w b j) : a=b ∧ i=j := by
  have A := port_bounds w a hi
  have B := port_bounds w b hj
  have ab : a=b := by
    rcases lt_trichotomy a b with lt|e|lt
    · exact False.elim ((A.2.trans_le ((Nat.mul_le_mul_right w (show a+1≤b from lt)).trans B.1)).ne eq)
    · exact e
    · exact False.elim ((B.2.trans_le ((Nat.mul_le_mul_right w (show b+1≤a from lt)).trans A.1)).ne eq.symm)
  subst b
  unfold slot at eq
  split at eq <;> omega

theorem history_trace {ds s layers} (h : History ds s layers) : Trace ds s := by
  induction h with
  | start => exact .start
  | step _ c ih => exact .advance ih c

end Recognition.RowPortMinor
