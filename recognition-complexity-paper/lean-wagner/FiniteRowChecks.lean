import IntervalSearch
import TargetLanguages
import SparseBoundary.FanGraphicNecessity
import SparseBoundary.GraphEnumeration

/-! Independently checked finite comparisons. Each accepting datum is a
short list of explicit interval moves. Rejection can use a necessary degree
inequality or a forbidden minor in every degree-compatible graph. -/
namespace Recognition.FiniteRowChecks
open SparseBoundary RowRule TargetLanguages

def candidates (n : Nat) := Listing.rows n (n-1) (n*(n-1))

theorem candidates_spec (n : Nat) (ds : List Nat) : ds∈candidates n ↔
    ds.length=n ∧ ds.Pairwise (·≥·) ∧ ∀x∈ds,x<n := by
  rw [candidates,Listing.rows_spec]
  constructor
  · rintro ⟨l,s,_,lim⟩
    refine ⟨l,s,fun x h=>?_⟩
    have := lim x h;have := List.length_pos_of_mem h;omega
  · rintro ⟨l,s,lim⟩
    have cap (x) (h : x∈ds) : x≤n-1 := by have := lim x h;omega
    have total := List.sum_le_length_nsmul ds (n-1) cap
    exact ⟨l,s,by simpa [l,smul_eq_mul] using total,cap⟩

theorem candidates_nodup (n : Nat) : (candidates n).Nodup := Listing.rows_nodup ..

def necessary (ds : List Nat) : Bool :=
  decide (ds.sum%2=0 ∧ (ds.length<4 ∨ ds.sum+12≤6*ds.length)) &&
    (List.range (ds.length+1)).all fun j =>
      decide ((ds.take j).sum≤j*(j-1)+((ds.drop j).map (min j)).sum)

theorem necessary_of_planar {ds : List Nat} (h : Planaric ds) : necessary ds=true := by
  have eg := ErdosGallai.eg_of_graphic (planaric_graphic h)
  have euler (hn : 4≤ds.length) : ds.sum+12≤6*ds.length := by
    classical
    obtain ⟨G,r,flat⟩ := h
    obtain ⟨H,inc,m⟩ := Augment.exists_maximal (Wagner.toSimple G) ((Wagner.planar_iff_rotation G).mp flat)
    obtain ⟨M⟩ := m.1
    let _ : Nonempty (Fin ds.length) := ⟨⟨0,by omega⟩⟩
    have lim := (Augment.maximal_tight M m (Augment.maximal_connected m) (by simpa using hn)).2
    have count := TargetLanguages.handshake G r
    have sub := Finset.card_le_card (SimpleGraph.edgeFinset_mono inc)
    rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card,Nat.card_fin] at lim
    rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card] at count
    omega
  simp only [necessary,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range]
  exact ⟨⟨eg.1,by by_cases hs : ds.length<4;exact Or.inl hs;exact Or.inr (euler (by omega))⟩,
    fun j h => eg.2 j (by omega)⟩

/-- Octal fields, from low to high: input degree, unchanged left length,
first-endpoint length, interior length and last-endpoint length. -/
def readStep (r : List Nat) (z : Nat) : Option (List Nat) :=
  let d:=z%8
  let l:=r.take (z/8%8)
  let s:=r.drop (z/8%8)
  let a:=s.take (z/64%8)
  let t:=s.drop (z/64%8)
  let b:=t.take (z/512%8)
  let rest:=t.drop (z/512%8)
  let c:=rest.take (z/4096%8)
  let suffix:=rest.drop (z/4096%8)
  if a.length≤1 ∧ c.length≤1 ∧ (∀x∈b,x=1) ∧ (a++b++c).length≤d then
    some ((l++(a++b).map (·-1)++(d-(a++b++c).length)::(c.map (·-1)++suffix)).filter (fun x=>0<x))
  else none

private theorem readStep_sound {r z next} (h : readStep r z=some next) :
    ∃ m : NumericalMove r (z%8),m.next=next := by
  unfold readStep at h
  dsimp only at h
  split at h
  next test =>
    refine ⟨⟨_,_,_,_,_,?_,test.1,test.2.1,test.2.2.1,test.2.2.2⟩,Option.some.inj h⟩
    simp [List.append_assoc]
  · contradiction

def follow (r : List Nat) : List Nat → Option (List Nat)
  | [] => some r
  | z::zs => (readStep r z).bind (fun next=>follow next zs)

private theorem follow_sound {zs r out} (h : follow r zs=some out) {used}
    (p : NumericalTrace used r) : NumericalTrace (used++zs.map (·%8)) out := by
  induction zs generalizing used r with
  | nil => simpa [follow] using (Option.some.inj h ▸ p)
  | cons z zs ih =>
    cases eq : readStep r z with
    | none => simp [follow,eq] at h
    | some q =>
      obtain ⟨m,e⟩ := readStep_sound eq
      have prior : NumericalTrace (used++[z%8]) q := e ▸ (p.advance m)
      simpa [List.append_assoc] using ih (by simpa [follow,eq] using h) prior

def traces (ds zs : List Nat) :=
  (zs.map (·%8)).isPerm ds && decide (follow [] zs=some [])

theorem traces_sound {ds zs} (h : traces ds zs=true) : Planaric ds := by
  simp only [traces,Bool.and_eq_true,List.isPerm_iff,decide_eq_true_eq] at h
  have trace := follow_sound h.2 NumericalTrace.start
  exact (planaric_perm h.1).mp (RowRecognition.trace_planaric trace)

/-- A branch set has at most three vertices in the supplied witnesses.
Each octal digit is one plus its label, in reverse construction order.
Five bags specify the clique and six bags the bipartite obstruction. -/
private def bag (n z : Nat) : List (Fin n) :=
  (List.range 3).filterMap fun i =>
    let digit := z / 8^i %8
    if h : digit≠0 ∧ digit-1<n then some ⟨digit-1,h.2⟩ else none

def disproves (G : Graph n) (bs : List Nat) : Bool :=
  if bs.length=5 then G.minorTest Graph.clique5 (fun i => bag n (bs[i.val]?.getD 0))
  else G.minorTest Graph.biclique33 (fun i => bag n (bs[i.val]?.getD 0))

private theorem disproves_sound {G : Graph n} {bs} (h : disproves G bs=true) : ¬G.Planar := by
  unfold disproves at h
  split at h
  · exact fun p=>p.1 ⟨_,h⟩
  · exact fun p=>p.2 ⟨_,h⟩

private def everyGraph : List (Graph n) → List (List Nat) → Bool
  | [],[] => true
  | g::gs, b::bs => disproves g b && everyGraph gs bs
  | _,_ => false

private theorem everyGraph_sound {gs : List (Graph n)} {cs} (ok : everyGraph gs cs=true) :
    ∀ g∈gs, ¬g.Planar := by
  induction gs generalizing cs with
  | nil => simp
  | cons a gs ih =>
    cases cs with
    | nil => contradiction
    | cons b bs =>
      simp only [everyGraph,Bool.and_eq_true] at ok
      intro g mem
      rcases List.mem_cons.mp mem with rfl|m
      · exact disproves_sound ok.1
      · exact ih ok.2 _ m

inductive Evidence where
  | yes (steps : List Nat)
  | no
  | forbidden (witnesses : List (List Nat))

def Evidence.positive : Evidence → Bool
  | .yes _ => true
  | _ => false

def Evidence.check (ds : List Nat) : Evidence → Bool
  | .yes steps => traces ds steps
  | .no => !necessary ds
  | .forbidden ws => everyGraph (Graph.candidates ds.length (fun i=>ds[i])) ws

theorem checked {ds : List Nat} {e : Evidence} (ok : e.check ds=true) :
    Planaric ds ↔ e.positive=true := by
  cases e with
  | yes steps => exact ⟨fun _=>rfl,fun _=>traces_sound ok⟩
  | no =>
    simp only [Evidence.check,Bool.not_eq_true'] at ok
    exact ⟨fun h=>by rw [necessary_of_planar h] at ok;contradiction, by intro e;contradiction⟩
  | forbidden ws =>
    constructor
    · rintro ⟨G,r,p⟩
      exact False.elim (everyGraph_sound ok G (Graph.candidates_complete G _ r) p)
    · intro h;contradiction

/-- Position zero is the low bit of the atlas column. Simultaneously check
its bit, the independent mathematical witness, and the lengths of the rows. -/
def audit : List (List Nat) → List Evidence → Nat → Nat → Bool
  | [],[],_,_ => true
  | d::ds,e::es,mask,i =>
    e.check d && (e.positive == mask.testBit i) && audit ds es mask (i+1)
  | _,_,_,_ => false

theorem audit_sound {ds : List (List Nat)} {es mask i} (ok : audit ds es mask i=true) :
    ∀ j : Fin ds.length, Planaric ds[j] ↔ mask.testBit (i+j.val)=true := by
  induction ds generalizing es i with
  | nil => exact fun j=>Fin.elim0 j
  | cons d ds ih =>
    cases es with
    | nil => contradiction
    | cons e es =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at ok
      refine Fin.cases ?_ (fun j=>?_)
      · simpa [←ok.1.2] using checked ok.1.1
      · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih ok.2 j

end Recognition.FiniteRowChecks
