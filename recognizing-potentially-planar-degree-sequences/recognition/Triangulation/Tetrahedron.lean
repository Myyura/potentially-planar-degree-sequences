import Triangulation.Rigidity

namespace Recognition.Tetrahedron
open Rigidity

private abbrev V := Fin 4
private abbrev F (a b c : V) := a ≠ b ∧ b ≠ c ∧ a ≠ c
private abbrev T := Triangle V

private def other (a b c : V) : V := ⟨(6-a.val-b.val-c.val)%4, Nat.mod_lt _ (by decide)⟩

private theorem others : ∀ a b c : V, F a b c → (other a b c) ≠ c ∧
    F a b (other a b c) ∧ ∀ e, F a b e → e=c ∨ e = other a b c := by decide +kernel

private def codes (k : Nat) : List (List Nat) :=
  match k with
  | 0 => [[]]
  | n+1 => [] :: ([0,1,2] : List Nat).flatMap (fun x => (codes n).map (List.cons x))

private def run (t : T) : List Nat → T
  | [] => t
  | 0 :: moves => run ⟨t.b,t.c,t.a⟩ moves
  | 1 :: moves => run ⟨t.b,t.a,t.c⟩ moves
  | (_+2) :: moves => run ⟨t.a,t.b,other t.a t.b t.c⟩ moves

private def origin : T := ⟨0,1,2⟩

private theorem end_walk {s t : T} (moves : List Nat) (walk : Walk F s t)
    (valid : F t.a t.b t.c) : Walk F s (run t moves) := by
  induction moves generalizing t with
  | nil => exact walk
  | cons m ms ih =>
    obtain ⟨a,b,c⟩ := t
    match m with
    | 0 => exact ih (.rot walk) ⟨valid.2.1,Ne.symm valid.2.2,Ne.symm valid.1⟩
    | 1 => exact ih (.flip walk) ⟨Ne.symm valid.1,valid.2.2,valid.2.1⟩
    | _+2 => exact ih (.cross walk (others a b c valid).2.1) (others a b c valid).2.1

private def key (t : T) : Nat := 16*t.a.val + 4*t.b.val + t.c.val

private theorem key_inj {t u : T} (eq : key t = key u) : t = u := by
  obtain ⟨a,b,c⟩ := t
  obtain ⟨i,j,k⟩ := u
  simp only [key] at eq
  have ai : a=i := Fin.ext (by omega)
  have bj : b=j := Fin.ext (by omega)
  have ck : c=k := Fin.ext (by omega)
  simp [ai,bj,ck]

-- A breadth bound for the 24 oriented faces of the labelled tetrahedron.
private def cover (t : T) := (codes 5).any (fun moves => key (run t moves) == key origin)
private theorem to_origin : ∀ a b c : V, F a b c → cover ⟨a,b,c⟩ = true := by decide +kernel
private def fromRoot := (codes 5).map (fun moves => key (run origin moves))
private theorem from_origin : ∀ a b c : V, F a b c → fromRoot.contains (key ⟨a,b,c⟩) := by decide +kernel

def map : Map (Fin 4) where
  face := F
  rot := by intro a b c h; exact ⟨h.2.1,Ne.symm h.2.2,Ne.symm h.1⟩
  flip := by intro a b c h; exact ⟨Ne.symm h.1,h.2.2,h.2.1⟩
  distinct := And.left
  twoSides := by intro a b c h; exact ⟨_,others a b c h⟩
  incident := by decide +kernel
  connected := by
    intro a b c i j k f g
    obtain ⟨m,_,hh⟩ := List.any_eq_true.mp (to_origin a b c f)
    have eq := key_inj (beq_iff_eq.mp hh)
    have w : Walk F ⟨a,b,c⟩ origin := eq ▸ end_walk m (.nil : Walk F ⟨a,b,c⟩ ⟨a,b,c⟩) f
    obtain ⟨n,_,eq'⟩ := List.mem_map.mp (List.contains_iff_mem.mp (from_origin i j k g))
    have target := key_inj eq'
    exact target ▸ end_walk n w (by decide)

theorem face_iff (a b c : Fin 4) : map.face a b c ↔ a ≠ b ∧ b ≠ c ∧ a ≠ c := Iff.rfl

theorem adj_iff : ∀ a b : Fin 4, map.adj a b ↔ a≠b := by
  change ∀ a b : Fin 4, (∃ c, F a b c) ↔ a≠b
  decide +kernel

end Recognition.Tetrahedron
