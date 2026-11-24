import PolygonGraph
import GraphCounts
import SparseBoundary.GraphPerm

namespace Recognition.RimInventory
open SparseBoundary Recognition.PolygonMidpoint

def chords (n : Nat) (A : Nat → Nat → Bool) :=
  ((List.range n).product (List.range n)).filter fun (i,j) => decide (i<j) && A i j

theorem mem_chords : (i,j) ∈ chords n A ↔ i<j ∧ j<n ∧ A i j := by
  simp [chords]
  grind

theorem nodup_chords (n A) : (chords n A).Nodup :=
  ((List.nodup_range (n:=n)).product List.nodup_range).filter _

private def mates (x : Nat) (p : Nat × Nat) := if p.1=x then p.2 else p.1

theorem degree_chords (n A) (sym : ∀ i j, A i j=A j i) (irr : ∀ i, A i i=false)
    (x : Nat) (hx : x<n) :
    valence (chords n A) x = ((List.range n).filter (A x)).length := by
  let touched := (chords n A).filter (fun p => p.1==x || p.2==x)
  have touch (p : Nat × Nat) :
      p∈touched ↔ p.1<p.2 ∧ p.2<n ∧ A p.1 p.2 ∧ (p.1=x ∨ p.2=x) := by
    rcases p with ⟨u,v⟩
    simp [touched,mem_chords,and_assoc]
  have nd : (touched.map (mates x)).Nodup := by
    apply List.pairwise_map.mpr
    apply ((nodup_chords n A).filter _).imp_of_mem
    intro p q hp hq ne eq
    obtain ⟨p1,p2⟩ := p
    obtain ⟨q1,q2⟩ := q
    have P := (touch _).mp hp
    have Q := (touch _).mp hq
    simp only [mates] at eq
    grind
  have perm : (touched.map (mates x)).Perm ((List.range n).filter (A x)) := by
    apply (List.perm_ext_iff_of_nodup nd (List.nodup_range.filter _)).mpr
    intro y
    simp only [List.mem_map,List.mem_filter,List.mem_range]
    constructor
    · rintro ⟨⟨a,b⟩,hm,h⟩
      obtain ⟨ab,bn,yes,tx⟩ := (touch _).mp hm
      rcases tx with rfl|rfl
      · simp [mates] at h
        subst y
        exact ⟨bn,yes⟩
      · have m : mates b (a,b)=a := by simp [mates,ab.ne]
        subst y
        rw [m,sym b a]
        exact ⟨by omega,yes⟩
    · rintro ⟨yn,h⟩
      rcases lt_trichotomy x y with xy|eq|yx
      · exact ⟨(x,y),(touch _).mpr ⟨xy,yn,h,Or.inl rfl⟩,by simp [mates]⟩
      · subst y; simp [irr] at h
      · exact ⟨(y,x),(touch _).mpr ⟨yx,hx,(sym y x).symm ▸ h,Or.inr rfl⟩,by simp [mates,yx.ne]⟩
  simpa [valence,touched] using perm.length_eq

theorem handshake (n : Nat) (es : List (Nat × Nat))
    (bounds : ∀ p∈es, p.1<p.2 ∧ p.2<n) :
    ((List.range n).map (valence es)).sum = 2*es.length := by
  induction es with
  | nil => change ((List.range n).map (fun _ => 0)).sum = 0
           simp
  | cons p es ih =>
    obtain ⟨i,j⟩ := p
    obtain ⟨ij,jn⟩ := bounds _ (.head _)
    have key (x : Nat) : valence ((i,j)::es) x =
        valence es x + ((x==i || x==j).toNat) := by
      change valence ([(i,j)] ++ es) x = _
      rw [valence_append,valence_singleton]
      by_cases a : i=x <;> by_cases b : j=x <;>
        simp [a,b,eq_comm (a:=x),Nat.add_comm]
    have cnt (xs : List Nat) : (xs.map (fun x => (x==i || x==j).toNat)).sum =
        (xs.filter (fun x => x==i || x==j)).length := by
      induction xs with
      | nil => rfl
      | cons a xs IH => cases e : a==i || a==j <;> simp [e,IH,Nat.add_comm]
    have perm : ((List.range n).filter (fun x => x==i || x==j)).Perm [i,j] := by
      apply (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) (by simp [ij.ne])).mpr
      intro x; simp only [List.mem_filter,List.mem_range,Bool.or_eq_true,beq_iff_eq,List.mem_cons,List.not_mem_nil,or_false]; omega
    simp only [List.length_cons]
    rw [show valence ((i,j)::es) = (fun x => valence es x + (x==i || x==j).toNat) from funext key]
    rw [List.sum_map_add,cnt,perm.length_eq,ih (fun p m => bounds p (.tail _ m))]
    simp;omega

def profile : List Nat := [12,8,6,5,5,5,5,5,3,3,3,3,3]

def adjacency (G : Graph 13) (rim : List (Fin 13)) (i j : Nat) := G.adj rim[i]! rim[j]!

theorem packed (G : Graph 13) (realizes : G.Realizes profile)
    (rim : List (Fin 13)) (size : rim.length=12) (unique : rim.Nodup)
    (covers : ∀ v, v∈rim ↔ v≠0) (univ : ∀ v : Fin 13, v≠0 → G.adj 0 v) :
    let es := chords 12 (adjacency G rim)
    es.Nodup ∧ (∀ p∈es, p.1<p.2 ∧ p.2≤11) ∧ es.length=21 ∧
      ((List.range 12).map (valence es)).Perm midPolygon := by
  let E := chords 12 (adjacency G rim)
  have all : ((0:Fin 13)::rim).Perm (List.finRange 13) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_cons.mpr ⟨by simp [covers],unique⟩) (List.nodup_finRange 13)).mpr
    intro v
    simp [covers,em]
  have indexed : (List.range 12).map (fun i => rim[i]!) = rim := by
    apply List.ext_getElem
    · simp [size]
    · intro i h h₂
      simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem h₂]
  have each (i) (hi : i∈List.range 12) :
      valence E i = G.degree rim[i]! - 1 := by
    have h : i<rim.length := size ▸ (List.mem_range.mp hi)
    have inside : rim[i]!∈rim := by simp [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem h,List.getElem_mem]
    have a := univ _ ((covers _).mp inside)
    rw [G.adj_comm] at a
    have count := (all.filter (G.adj rim[i]!)).length_eq
    rw [List.filter_cons_of_pos a] at count
    have mapped := congrArg (fun xs => (xs.filter (G.adj rim[i]!)).length) indexed
    simp only [List.filter_map,List.length_map] at mapped
    rw [show E=chords 12 (adjacency G rim) from rfl,degree_chords 12 (adjacency G rim) (fun i j => G.adj_comm _ _) (fun j => G.adj_self _) _ (List.mem_range.mp hi)]
    change ((List.range 12).filter (fun j => G.adj rim[i]! rim[j]!)).length =
      ((List.finRange 13).filter _).length - 1
    simp only [List.length_cons] at count
    change ((List.range 12).filter (fun j => G.adj rim[i]! rim[j]!)).length = _ at mapped
    omega
  have ids : rim.Perm (List.finRange 13).tail := by
    apply (List.perm_ext_iff_of_nodup unique (List.nodup_finRange 13).tail).mpr
    intro i
    rw [covers]
    have t : ∀ j : Fin 13, j≠0 ↔ j∈(List.finRange 13).tail := by decide
    exact t i
  have rows : ((List.range 12).map (valence E)).Perm midPolygon := by
    rw [List.map_congr_left each]
    change (List.map ((fun v => G.degree v - 1) ∘ (fun i => rim[i]!)) (List.range 12)).Perm _
    rw [← List.map_map,indexed]
    have indexedDegrees (v : Fin 13) : G.degree v=profile[v.val]! := by
      have h := realizes ⟨v.val,v.isLt⟩
      change G.degree v = profile[v.val] at h
      have hv : v.val < profile.length := v.isLt
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hv,Option.getD_some] using h
    simp_rw [indexedDegrees]
    have check : ((List.finRange 13).tail.map (fun v => profile[v.val]!-1)).Perm midPolygon := by decide +kernel
    exact (ids.map (fun v => profile[v.val]!-1)).trans check
  have bounds (p) (h : p∈E) : p.1<p.2 ∧ p.2<12 := ⟨(mem_chords.mp h).1,(mem_chords.mp h).2.1⟩
  have twice := handshake 12 E bounds
  have pop := rows.sum_eq
  have mass : midPolygon.sum = 42 := by decide
  change E.Nodup ∧ _ ∧ E.length=21 ∧ _
  exact ⟨nodup_chords ..,fun p h => ⟨(bounds p h).1,by have := (bounds p h).2;omega⟩,by omega,rows⟩

end Recognition.RimInventory
