import LeanPool.K5MinorFreeChoosability.Planar.Orbits

/-! Count components of a finite list of identifications by materializing the
representative vector after each union. No search through permutations. -/
namespace Recognition.OrbitTable
open LeanPool.K5MinorFreeChoosability
variable {D : Type} [DecidableEq D]
abbrev Rows (D : Type) := List (D × D)

def key (R : Rows D) (x : D) := (R.lookup x).getD x
def tabulate (xs : List D) (f : D → D) : Rows D := xs.map fun x => (x,f x)
def merge (xs : List D) (R : Rows D) (e : D × D) : Rows D :=
  let a := key R e.1
  let b := key R e.2
  tabulate xs (fun x => let t := key R x; if t=b then a else t)

def run (xs : List D) (pairs : List (D × D)) := pairs.foldl (merge xs) (tabulate xs id)
private def distinct : List D → List D
  | [] => []
  | x :: xs => if x ∈ xs then distinct xs else x :: distinct xs

private theorem distinct_mem (xs : List D) (v : D) : v ∈ distinct xs ↔ v ∈ xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x ∈ xs <;> simp [distinct,h,ih]; grind

private theorem distinct_nodup (xs : List D) : (distinct xs).Nodup := by
  induction xs with
  | nil => simp [distinct]
  | cons x xs ih => by_cases h : x ∈ xs <;> simp [distinct,h,ih,distinct_mem]

def count (R : Rows D) := (distinct (R.map Prod.snd)).length

@[simp] theorem count_nil : count ([] : Rows D) = 0 := rfl

theorem count_cons (u v : D) (R : Rows D) :
    count ((u,v)::R) = if v∈R.map Prod.snd then count R else count R+1 := by
  by_cases h : v∈R.map Prod.snd <;> simp [count,distinct,h]

private theorem entry (xs : List D) (f : D → D) {x} (mem : x ∈ xs) :
    (tabulate xs f).lookup x = some (f x) := by
  induction xs with
  | nil => simp at mem
  | cons a xs ih =>
    by_cases eq : x=a
    · subst a; simp [tabulate]
    · have bit : (x == a) = false := by exact beq_eq_false_iff_ne.mpr eq
      simpa [tabulate,List.lookup,bit] using ih ((List.mem_cons.mp mem).resolve_left eq)

theorem get_entry (xs : List D) (f : D → D) {x} (mem : x ∈ xs) : key (tabulate xs f) x = f x := by
  simp [key,entry xs f mem]

private theorem merged (xs : List D) (all : ∀ x, x ∈ xs) (R : Rows D) (u v x y : D) :
    key (merge xs R (u,v)) x = key (merge xs R (u,v)) y ↔
    key R x=key R y ∨ (key R x=key R u ∧ key R y=key R v) ∨ (key R x=key R v ∧ key R y=key R u) := by
  simp only [merge,get_entry xs _ (all _)]
  split <;> split <;> grind

private theorem holds (xs : List D) (all : ∀ x, x ∈ xs) (es : List (D×D)) (R : Rows D) :
    (∀ x y, key R x=key R y → key (es.foldl (merge xs) R) x=key (es.foldl (merge xs) R) y) ∧
    ∀ e ∈ es, key (es.foldl (merge xs) R) e.1=key (es.foldl (merge xs) R) e.2 := by
  induction es generalizing R with
  | nil => simp
  | cons e es ih =>
    obtain ⟨h, pairs⟩ := ih (merge xs R e)
    refine ⟨fun x y eq => h _ _ ((merged xs all R e.1 e.2 x y).mpr (.inl eq)),?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h _ _ ((merged xs all R t.1 t.2 t.1 t.2).mpr (.inr (.inl ⟨rfl,rfl⟩)))
    · exact pairs t ht

private theorem minimal (xs : List D) (all : ∀ x, x ∈ xs) (es : List (D×D)) (R : Rows D)
    (s : Setoid D) (init : ∀ x y, key R x=key R y → s x y) (gens : ∀ e ∈ es, s e.1 e.2) :
    ∀ x y, key (es.foldl (merge xs) R) x=key (es.foldl (merge xs) R) y → s x y := by
  induction es generalizing R with
  | nil => exact init
  | cons e es ih =>
    apply ih (merge xs R e) _ (fun t h => gens t (List.mem_cons_of_mem _ h))
    intro x y h
    rcases (merged xs all R e.1 e.2 x y).mp h with eq | ⟨a,b⟩ | ⟨a,b⟩
    · exact init x y eq
    · exact s.trans (init _ _ a) (s.trans (gens e (by simp)) (s.symm (init _ _ b)))
    · exact s.trans (init _ _ a) (s.trans (s.symm (gens e (by simp))) (s.symm (init _ _ b)))

theorem generated (xs : List D) (all : ∀ x, x ∈ xs) (es : List (D×D)) (s : Setoid D)
    (edges : ∀ e ∈ es, s e.1 e.2)
    (least : ∀ r : Setoid D, (∀ e ∈ es, r e.1 e.2) → ∀ x y, s x y → r x y) (x y : D) :
    key (run xs es) x = key (run xs es) y ↔ s x y := by
  constructor
  · exact minimal xs all es (tabulate xs id) s (fun a b eq => by
      simp only [get_entry xs _ (all _),id_eq] at eq; exact eq ▸ s.refl a) edges x y
  · exact least (Setoid.ker (key (run xs es))) (holds xs all es _).2 x y

private theorem materialized (xs : List D) (es : List (D×D)) (f : D → D) :
    ∃ g, es.foldl (merge xs) (tabulate xs f) = tabulate xs g := by
  induction es generalizing f with
  | nil => exact ⟨f,rfl⟩
  | cons e es ih => exact ih _

theorem count_correct {xs : List D} (all : ∀ x, x ∈ xs) (es : List (D×D)) (s : Setoid D)
    (eq : ∀ x y, key (run xs es) x = key (run xs es) y ↔ s x y) :
    count (run xs es) = numClasses s := by
  classical
  obtain ⟨f,t⟩ := materialized xs es id
  change run xs es = tabulate xs f at t
  rw [t] at eq ⊢
  simp only [get_entry xs _ (all _)] at eq
  let names := distinct (xs.map f)
  have F (x : D) : f x ∈ names := by
    apply (distinct_mem _ _).mpr; exact List.mem_map.mpr ⟨x,all x,rfl⟩
  have pre (u : {v // v ∈ names}) : ∃ x, f x=u.val := by
    obtain ⟨x,_,e⟩ := List.mem_map.mp ((distinct_mem _ _).mp u.property)
    exact ⟨x,e⟩
  let equiv : Quotient s ≃ {u // u ∈ names} := {
    toFun := Quotient.lift (fun x => ⟨f x,F x⟩) (fun a b h => Subtype.ext ((eq a b).mpr h))
    invFun := fun u => Quotient.mk s (pre u).choose
    left_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => apply Quotient.sound; exact (eq _ _).mp (pre ⟨f x,F x⟩).choose_spec
    right_inv := by intro u; apply Subtype.ext; exact (pre u).choose_spec
  }
  have card := Nat.card_congr equiv
  change Nat.card (Quotient s) = Nat.card {u // u ∈ names} at card
  have countNames : Fintype.card {u // u ∈ names} = names.length := by
    let ns : Finset D := names.toFinset
    let E : {u // u ∈ names} ≃ {u // u ∈ ns} :=
      Equiv.subtypeEquivRight (fun _ => by simp [ns])
    rw [Fintype.card_congr E,Fintype.card_coe,List.toFinset_card_of_nodup]
    exact distinct_nodup _
  rw [Nat.card_eq_fintype_card (α := {u // u ∈ names}),countNames] at card
  simpa [count,tabulate,names,Function.comp_def,numClasses,List.map_map] using card.symm

end Recognition.OrbitTable
