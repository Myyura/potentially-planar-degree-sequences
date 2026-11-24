import FullBlocks
import TracePlanarity

/-! Running an ordered closed triangulation through the full recurrence,
including the numerical budget and every component-closure guard. -/
namespace Recognition.TerminalOrder
open Recognition.QuotientDP Recognition.FullBlocks

private def credit (s : State n) (d : Multiset Nat) := {s with remaining := s.remaining+d}

private theorem credit_advance {bound} {s t : State n} {a : Triangle n} (ok : fullAdvance bound s a=some t)
    (budget : Multiset Nat) : fullAdvance bound (credit s budget) a=some (credit t budget) := by
  unfold fullAdvance at ok ⊢; split at ok <;> rename_i yes
  · obtain rfl := Option.some.inj ok
    obtain ⟨inj,room,limit,legal,pay,keep⟩ := of_decide_eq_true yes
    have good : allowed bound (credit s budget) a :=
      decide_eq_true ⟨inj,room,limit,legal,pay.trans (Multiset.le_add_right ..),keep⟩
    rw [ite_eq_left good]; apply congrArg some
    have calc_ : (s.remaining+budget)-released s a = (s.remaining-released s a)+budget := by
      ext v
      have bound := Multiset.count_le_of_le v pay
      simp only [Multiset.count_sub,Multiset.count_add]; omega
    cases s with
    | mk p q b c r u f =>
      simp only [fullNext,nextState,credit,State.mk.injEq]
      first | exact calc_ | trivial
  · contradiction

private theorem credit_run {bound target past U} {s : State n} (run : FullRun bound target past U s)
    (budget : Multiset Nat) : FullRun bound (target+budget) past U (credit s budget) := by
  induction run with
  | init => exact .init
  | step prev a eligible ok ih => exact .step ih a eligible (credit_advance ok budget)

private structure Prefix (bound : Nat) (past : List (Triangle n)) (U : Finset (Name n)) (s : State n) : Prop where
  remaining : s.remaining=0
  faces : s.faces=past.length
  used : s.used=U.card
  cover : liveSet s ⊆ U
  present : ∀ x, x∈U ↔ ∃ a∈past, x∈vertices a

private theorem room_for_new {past : List (Triangle n)} {U : Finset (Name n)} {s : State n}
    (pre : Prefix bound past U s) (a : Triangle n) (inj : Function.Injective a.v)
    (fresh : ∀ k, a.v k∈U → active s.pending (a.v k)) :
    s.used+QuotientDP.fresh s a=(U ∪ vertices a).card := used_next s U a fresh pre.cover inj pre.used

/-- A prescribed full order of a paired, connected triangulation with
connected vertex links admits a successful run. The resulting target is
the multiset paid as vertices are released, independent of a guessed budget. -/
theorem realize_order (fs : List (Triangle n)) (inj : ∀ a∈fs,Function.Injective a.v)
    (covered : ∀ x : Name n, ∃ a∈fs,x∈vertices a)
    (paired : ∀ e,FullBlocks.occurrences fs e=0 ∨ FullBlocks.occurrences fs e=2)
    (connected : ∀ x y, PlanarDegrees.Frontier.Walk (Dual fs) x y) (links : ConnectedLinks fs) :
    ∃ target U s, FullRun fs.length target fs U s ∧ finished fs.length s=true := by
  classical
  have build (past future : List (Triangle n)) (all : future++past=fs) :
      ∃ target U s, FullRun fs.length target past U s ∧ Prefix fs.length past U s := by
    induction past generalizing future with
    | nil => exact ⟨0,∅,_,.init,⟨rfl,rfl,rfl,by simp [liveSet,start,active],by simp⟩⟩
    | cons a past ih =>
      obtain ⟨target,U,s,run,pre⟩ := ih (future++[a]) (by simpa using all)
      have he := congrArg List.length all
      simp only [List.length_append,List.length_cons] at he
      have last : s.faces+1=fs.length ↔ future=[] := by rw [pre.faces,←List.length_eq_zero_iff]; omega
      have whole : ∀ e, FullBlocks.occurrences (future++a::past) e=0 ∨ FullBlocks.occurrences (future++a::past) e=2 := all.symm ▸ paired
      have cap (e) : FullBlocks.occurrences (future++a::past) e≤2 := by rcases whole e with h|h <;> omega
      obtain ⟨legal,keep⟩ := component_guard run a future whole (all.symm ▸ connected) last
      have eligible := corner_eligible run a future (fun x hx => (pre.present x).mp hx) cap (all.symm ▸ links)
      have encode := inj a (all ▸ List.mem_append_right future (List.mem_cons_self ..))
      have used := room_for_new pre a encode eligible
      have room : s.used+QuotientDP.fresh s a≤n := by rw [used]; simpa using Finset.card_le_univ (U ∪ vertices a)
      let bill := released s a
      let s' := credit s bill
      have take : allowed fs.length s' a := by
        apply decide_eq_true
        refine ⟨encode,room,by change s.faces<fs.length; rw [pre.faces]; omega,legal,?_,keep⟩
        change bill ≤ s.remaining+bill; rw [pre.remaining,zero_add]
      have next : fullAdvance fs.length s' a=some (fullNext s' a) := by simp [fullAdvance,take]
      refine ⟨target+bill,U∪vertices a,fullNext s' a,.step (credit_run run bill) a eligible next,?_⟩
      constructor
      · change (s.remaining+bill)-bill=0; simp [pre.remaining]
      · change s.faces+1=past.length+1; rw [pre.faces]
      · exact used
      · intro x hx; have live := (Finset.mem_filter.mp hx).2
        rcases next_live s a x live with old|now
        · exact Finset.mem_union_left _ (pre.cover (Finset.mem_filter.mpr ⟨Finset.mem_univ _,old⟩))
        · exact Finset.mem_union_right _ now
      · intro x; simp only [Finset.mem_union,List.mem_cons,pre.present]; grind
  obtain ⟨target,U,s,run,h⟩ := build fs [] rfl
  have full : U=Finset.univ := Finset.eq_univ_iff_forall.mpr (fun x => (h.present x).mpr (covered x))
  have used : s.used=n := by simp [h.used,full]
  refine ⟨target,U,s,run,decide_eq_true ⟨h.faces,used,h.remaining,?_⟩⟩
  intro e; apply Bool.eq_false_iff.mpr; intro he
  have one := ((inventory_exact run).open_ e).mp he; rcases paired e with eq|eq <;> omega

end Recognition.TerminalOrder
