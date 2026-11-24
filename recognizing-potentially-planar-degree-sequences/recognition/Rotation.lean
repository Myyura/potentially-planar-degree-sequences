import Transfer

/-! Convert facial cycles of a rotation system to the unoriented triangle
relation used by the degree compiler. Darts keep their original labels. -/
namespace Recognition.Rotation
open SparseBoundary SparseBoundary.Graph Rigidity Layers HardnessConverse

structure Dart {n : Nat} (G : Graph n) where
  src : Fin n
  dst : Fin n
  edge : G.adj src dst = true

def Dart.rev {G : Graph n} (d : Dart G) : Dart G :=
  ⟨d.dst,d.src,(G.adj_comm ..).trans d.edge⟩

theorem Dart.ext {G : Graph n} {d e : Dart G} (a : d.src = e.src) (b : d.dst = e.dst) : d=e := by
  cases d; cases e; cases a; cases b; rfl

inductive Reach {G : Graph n} (turn : Dart G → Dart G) (d : Dart G) : Dart G → Prop where
  | base : Reach turn d d
  | face {e} : Reach turn d e → Reach turn d (turn e)
  | reverse {e} : Reach turn d e → Reach turn d e.rev

theorem Reach.trans {G : Graph n} {turn : Dart G → Dart G} {d e f : Dart G}
    (h : Reach turn d e) (j : Reach turn e f) : Reach turn d f := by
  induction j with
  | base => exact h
  | face _ ih => exact .face ih
  | reverse _ ih => exact .reverse ih

theorem Reach.symm {G : Graph n} {turn : Dart G → Dart G} (period : ∀ d, turn (turn (turn d))=d)
    {a b : Dart G} (h : Reach turn a b) : Reach turn b a := by
  induction h with
  | base => exact .base
  | @face e _ ih =>
    have back : Reach turn (turn e) e := by
      simpa only [period] using (show Reach turn (turn e) (turn (turn (turn e))) from .face (.face .base))
    exact back.trans ih
  | @reverse e _ ih =>
    have back : Reach turn e.rev e := Reach.reverse Reach.base
    exact back.trans ih

/-- `turn` is the successor around a directed face. The two third corners
on an undirected edge are distinct. All darts are in one component. -/
structure TriangularRotation {n : Nat} (G : Graph n) where
  turn : Dart G → Dart G
  starts : ∀ d, (turn d).src = d.dst
  three : ∀ d, turn (turn (turn d)) = d
  distinctSides : ∀ d, (turn d).dst ≠ (turn d.rev).dst
  connected : ∀ d e, Reach turn d e

variable {n : Nat} {G : Graph n} (S : TriangularRotation G)
def Left (a b c : Fin n) := ∃ d : Dart G, d.src=a ∧ d.dst=b ∧ (S.turn d).dst=c
def face (a b c : Fin n) := Left S a b c ∨ Left S b a c

private theorem closes (d : Dart G) : (S.turn (S.turn d)).dst = d.src :=
  (S.starts (S.turn (S.turn d))).symm.trans (congrArg Dart.src (S.three d))

private theorem left_rot {a b c} (f : Left S a b c) : Left S b c a := by
  obtain ⟨d,rfl,rfl,rfl⟩ := f
  exact ⟨S.turn d,S.starts d,rfl,closes S d⟩

private theorem rot {a b c} : face S a b c → face S b c a :=
  fun h => h.elim (fun t => .inl (left_rot S t)) (fun t => .inr (left_rot S (left_rot S t)))

private theorem flip {a b c} (h : face S a b c) : face S b a c := h.symm

private theorem incident_edge {a b c} (f : face S a b c) : G.adj a b = true := by
  rcases f with ⟨d,rfl,rfl,_⟩|⟨d,rfl,rfl,_⟩
  · exact d.edge
  · exact d.rev.edge

private theorem opposite (d : Dart G) (z) :
    face S d.src d.dst z ↔ z=(S.turn d).dst ∨ z=(S.turn d.rev).dst := by
  constructor
  · rintro (⟨e,hs,ht,rfl⟩|⟨e,hs,ht,rfl⟩)
    · exact .inl (congrArg (fun t => (S.turn t).dst) (Dart.ext hs ht))
    · exact .inr (congrArg (fun t => (S.turn t).dst) (Dart.ext (e:=d.rev) hs ht))
  · rintro (rfl|rfl)
    · exact .inl ⟨d,rfl,rfl,rfl⟩
    · exact .inr ⟨d.rev,rfl,rfl,rfl⟩

def triangle (d : Dart G) : Triangle (Fin n) := ⟨d.src,d.dst,(S.turn d).dst⟩

private theorem walk_trans {F : V → V → V → Prop} {p q r} (a : Walk F p q) (b : Walk F q r) :
    Walk F p r := by
  induction b with
  | nil => exact a
  | rot h ih => exact .rot ih
  | flip h ih => exact .flip ih
  | cross h f ih => exact .cross ih f

private theorem dart_walk (d e : Dart G) : Walk (face S) (triangle S d) (triangle S e) := by
  induction S.connected d e with
  | base => exact .nil
  | @face e _ ih =>
    have eq : triangle S (S.turn e) = ⟨e.dst,(S.turn e).dst,e.src⟩ := by
      simp [triangle,S.starts,closes]
    rw [eq]; exact .rot ih
  | @reverse e _ ih =>
    exact .cross (.flip ih) (.inl ⟨e.rev,rfl,rfl,rfl⟩)

private theorem walks {a b c u v w} (f : face S a b c) (g : face S u v w) :
    Walk (face S) ⟨a,b,c⟩ ⟨u,v,w⟩ := by
  rcases f with ⟨d,rfl,rfl,rfl⟩|⟨d,rfl,rfl,rfl⟩ <;>
    rcases g with ⟨e,rfl,rfl,rfl⟩|⟨e,rfl,rfl,rfl⟩
  · exact dart_walk S d e
  · exact .flip (dart_walk S d e)
  · exact walk_trans (.flip .nil) (dart_walk S d e)
  · exact .flip (walk_trans (.flip .nil) (dart_walk S d e))

def asMap (incident : ∀ a, ∃ b, G.adj a b = true) : Rigidity.Map (Fin n) where
  face := face S
  rot := rot S
  flip := flip S
  distinct := by
    intro a b c f eq; subst b
    simpa using incident_edge S f
  twoSides := by
    intro a b c f
    let d : Dart G := ⟨a,b,incident_edge S f⟩
    have atEdge := opposite S d
    rcases (atEdge c).mp f with u | u
    · exact ⟨_,u ▸ Ne.symm (S.distinctSides d),(atEdge _).mpr (.inr rfl),
        fun z hz => ((atEdge z).mp hz).imp_left (fun eq => eq.trans u.symm)⟩
    · exact ⟨_,u ▸ S.distinctSides d,(atEdge _).mpr (.inl rfl),
        fun z hz => ((atEdge z).mp hz).symm.imp_left (fun eq => eq.trans u.symm)⟩
  incident a := by
    obtain ⟨b,h⟩ := incident a
    let d : Dart G := ⟨a,b,h⟩
    exact ⟨b,(S.turn d).dst,.inl ⟨d,rfl,rfl,rfl⟩⟩
  connected := walks S

theorem asMap_adj (inc) (a b : Fin n) : (asMap S inc).adj a b ↔ G.adj a b = true := by
  constructor
  · rintro ⟨_,h⟩; exact incident_edge S h
  · intro h
    let d : Dart G := ⟨a,b,h⟩
    exact ⟨(S.turn d).dst,.inl ⟨d,rfl,rfl,rfl⟩⟩

private def enum (n : Nat) : Enumeration (Fin n) :=
  ⟨List.finRange n,List.nodup_finRange n,List.mem_finRange⟩

private theorem count_bool (xs : List α) (f : α → Bool) :
    (xs.filter f).length = (xs.map (fun x => (f x).toNat)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : f a <;> simp [h,ih,Nat.add_comm]

theorem to_model {d : List Nat} (G : Graph d.length) (S : TriangularRotation G)
    (valid : Reduction.TableValid d) (realizes : G.Realizes d) :
    ∃ R : Layers.Model d, SameEdges R G := by
  classical
  have inc (a : Fin d.length) : ∃ b, G.adj a b = true := by
    have h : 3 ≤ d[a] := (valid.2.2 _ (List.getElem_mem a.isLt)).1
    have deg := realizes a
    change ((List.finRange d.length).filter (G.adj a)).length = d[a] at deg
    have pos : 0 < ((List.finRange d.length).filter (G.adj a)).length := by rw [deg]; omega
    obtain ⟨b,hb⟩ := List.length_pos_iff_exists_mem.mp pos
    exact ⟨b,(List.mem_filter.mp hb).2⟩
  let R : Layers.Model d := {
    V := Fin d.length
    map := asMap S inc
    vertices := enum d.length
    label := Fin.val
    inj := fun _ _ => Fin.ext
    hits := fun i => ⟨fun h => ⟨⟨i,h⟩,rfl⟩,fun ⟨v,h⟩ => h ▸ v.isLt⟩
    value := by
      intro a
      rw [List.getElem?_eq_getElem a.isLt]
      change ((List.finRange d.length).map (fun b => mark ((asMap S inc).adj a b))).sum = d[a]
      rw [← realizes a,Graph.degree,count_bool]
      apply congrArg List.sum
      apply List.map_congr_left
      intro b _
      rw [asMap_adj]
      cases h : G.adj a b <;> simp [mark]
  }
  refine ⟨R,?_⟩
  intro i j
  constructor
  · rintro ⟨x,y,hx,hy,h⟩
    rw [← Fin.ext hx,← Fin.ext hy]
    exact (asMap_adj S inc x y).mp h
  · intro h; exact ⟨i,j,rfl,rfl,(asMap_adj S inc i j).mpr h⟩

end Recognition.Rotation
