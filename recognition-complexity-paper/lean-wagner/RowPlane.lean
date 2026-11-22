import Mathlib.Tactic.Linarith
import PolygonCompletion
import RowResult
import SparseBoundary.RimGrowth

/-! One common spine for every port of an entire ordered-row replay. Odd
and even strips separately form noncrossing pages on that spine. Each page
has a planar host even after adding the full spine cycle and an apex. -/
namespace Recognition.RowPlane
open Recognition.RowRule SparseBoundary

structure Layer where
  arc : Nat → Nat → Prop
  width : Nat
  bounded : ∀ {i j}, arc i j → i < width ∧ j < width
  ordered : ∀ {i j k l}, arc i j → arc k l → i < k → j ≤ l

private theorem index_lt {xs : List α} {i v} (e : xs[i]? = some v) : i < xs.length := by
  by_contra! outside
  simp [List.getElem?_eq_none outside] at e

/-- Each arc is an actual named fan stroke. -/
def fan {s d} (c : Choice s d) : Layer where
  arc i j := ∃ v u, Stroke c i j v u
  width := max s.row.length c.upper.length
  bounded := by
    rintro i j ⟨v,u,e⟩
    have p := e.ports
    have tip : j < c.upper.length := by
      by_contra! outside
      rw [List.getElem?_eq_none outside] at p
      simp at p
    exact ⟨(index_lt p.1).trans_le (Nat.le_max_left ..), tip.trans_le (Nat.le_max_right ..)⟩
  ordered := by
    rintro i j k l ⟨v,u,e⟩ ⟨x,y,f⟩ lt
    have a := e.arc
    have b := f.arc
    cases a <;> cases b <;> omega

/-- Connecting surviving ports to the next dense contour. -/
def repack {s d} (c : Choice s d) : Layer where
  arc i j := ∃ v, Repack c.livePorts i j v
  width := max c.livePorts.length (c.livePorts.filterMap id).length
  bounded := by
    rintro i j ⟨v,e⟩
    exact ⟨(index_lt e.ports.1).trans_le (Nat.le_max_left ..),
      (index_lt e.ports.2).trans_le (Nat.le_max_right ..)⟩
  ordered := by
    rintro i j k l ⟨v,e⟩ ⟨u,f⟩ lt
    exact (e.ordered f lt).le

/-- The layer list preserves the choices and names of the trace. -/
inductive History : List Nat → State → List Layer → Prop where
  | start : History [] empty []
  | step {ds s d layers} : History ds s layers → (c : Choice s d) →
      History (ds++[d]) (RowRule.step c) (layers++[fan c,repack c])

private theorem history_of_drawn {ds s} (trace : DrawnTrace ds s) : ∃ layers, History ds s layers := by
  induction trace with
  | start => exact ⟨[], .start⟩
  | advance prev c drawing ih =>
    obtain ⟨ls, h⟩ := ih
    exact ⟨_, .step h c⟩

/-- The common linear order reads alternate horizontal rows in reverse. -/
def slot (w t i : Nat) := t*w + if t%2=0 then i else w-1-i

private theorem slot_bounds {w i : Nat} (t : Nat) (inside : i < w) :
    t*w ≤ slot w t i ∧ slot w t i < (t+1)*w := by
  unfold slot
  rw [Nat.add_mul, Nat.one_mul]
  split <;> omega

private theorem before {w i j a b : Nat} (hi : i < w) (hj : j < w) (lt : a < b) :
    slot w a i < slot w b j :=
  ((slot_bounds a hi).2.trans_le (Nat.mul_le_mul_right w lt)).trans_le (slot_bounds b hj).1

/-- Every chord runs from one level to the succeeding level. -/
def Chord (layers : List Layer) (w page a b : Nat) : Prop :=
  ∃ t : Fin layers.length, ∃ i j, t.val%2=page ∧ i<w ∧ j<w ∧ layers[t].arc i j ∧
    a=slot w t.val i ∧ b=slot w (t.val+1) j

theorem chord_increases {layers w p a b} (h : Chord layers w p a b) : a<b := by
  obtain ⟨t,i,j,_,hi,hj,_,rfl,rfl⟩ := h
  exact before hi hj (Nat.lt_succ_self _)

/-- Distinct bands on one page are disjoint in spine order. Inside a band
the reversal of its upper row turns monotonicity into nonalternation. -/
theorem chords_noncross {layers w page a b c d}
    (ac : Chord layers w page a c) (bd : Chord layers w page b d)
    (ab : a<b) (bc : b<c) (cd : c<d) : False := by
  obtain ⟨t,i,j,pt,hi,hj,arc,rfl,rfl⟩ := ac
  obtain ⟨s,k,l,ps,hk,hl,arc',rfl,rfl⟩ := bd
  have eq : t=s := by
    apply Fin.ext
    rcases lt_trichotomy t.val s.val with lt|eq|gt
    · have gap : t.val+1<s.val := by omega
      exact False.elim ((before hj hk gap).not_gt bc)
    · exact eq
    · exact False.elim ((before hk hi gt).not_gt ab)
  subst s
  by_cases even : t.val%2=0
  · have odd : (t.val+1)%2≠0 := by omega
    simp only [slot, even, ite_true, ite_eq_right (fun o => (odd o).elim), Nat.add_lt_add_iff_left] at ab cd
    have monotone := layers[t].ordered arc arc' ab
    omega
  · have odd : (t.val+1)%2=0 := by omega
    simp only [slot, ite_eq_right (fun o => (even o).elim), odd, ite_true, Nat.add_lt_add_iff_left] at ab cd
    have ki : k < i := by omega
    have monotone := layers[t].ordered arc' arc ki
    omega

/-- Unaugmented port graph. Only edges of the two page relations are
present; the two guard labels are isolated. Vertices have one common spine
number across the entire history. -/
def portGraph (layers : List Layer) (w : Nat) : SimpleGraph (Fin ((layers.length+1)*w+2)) where
  Adj x y := ∃ p : Nat, p≤1 ∧ (Chord layers w p x.val y.val ∨ Chord layers w p y.val x.val)
  symm := by constructor; rintro x y ⟨p, hp, edge⟩; exact ⟨p,hp,edge.symm⟩
  loopless := by
    constructor
    rintro x ⟨p,_,e|e⟩ <;> exact (Nat.lt_irrefl _) (chord_increases e)

/-- Adjacency from a named observed layer arc, with input and output port
labels as in `replay_pages`. -/
theorem port_adj {layers w p} (hp : p≤1) {x y : Fin ((layers.length+1)*w+2)}
    (edge : Chord layers w p x.val y.val) : (portGraph layers w).Adj x y := ⟨p,hp,.inl edge⟩

/-- The two extra rim positions allow empty layers or zero usable ports.
The last position is an apex; a perimeter edge closes the full rim. -/
def pageAdj (layers : List Layer) (w page : Nat) (a b : Nat) : Prop :=
  let n := (layers.length+1)*w
  a≠b ∧ (a=n+2 ∨ b=n+2 ∨ a+1=b ∨ b+1=a ∨
    (a=0 ∧ b=n+1) ∨ (b=0 ∧ a=n+1) ∨ Chord layers w page a b ∨ Chord layers w page b a)

noncomputable def pageGraph (layers : List Layer) (w page : Nat) : Graph ((layers.length+1)*w+3) := by
  classical
  exact Graph.ofRelation (fun x y => decide (pageAdj layers w page x.val y.val))

theorem pageGraph_adj (layers : List Layer) (w page : Nat) (a b : Fin ((layers.length+1)*w+3)) :
    (pageGraph layers w page).adj a b = true ↔ pageAdj layers w page a.val b.val := by
  classical
  unfold pageGraph
  rw [Graph.adj_ofRelation]
  · simp
  · intro i j
    apply decide_eq_decide.mpr
    unfold pageAdj
    tauto
  · intro i
    simp [pageAdj]

/-- Chords land on real port labels, strictly before the two guard
positions and the apex. They are actual host edges with these labels. -/
theorem chord_edge {layers w p a b} (h : Chord layers w p a b) :
    ∃ (x y : Fin ((layers.length+1)*w+3)), x.val=a ∧ y.val=b ∧
      x.val < (layers.length+1)*w ∧ y.val < (layers.length+1)*w ∧
      (pageGraph layers w p).adj x y=true := by
  have lt := chord_increases h
  have last : b < (layers.length+1)*w := by
    obtain ⟨t,i,j,parity,hi,hj,arc,low,high⟩ := h
    rw [high]
    exact (slot_bounds (t.val+1) hj).2.trans_le (Nat.mul_le_mul_right w (by omega))
  have first := lt.trans last
  refine ⟨⟨a,by omega⟩,⟨b,by omega⟩,rfl,rfl,first,last,(pageGraph_adj ..).mpr ?_⟩
  exact ⟨lt.ne, .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))⟩

/-- An entire page, with its common boundary and external apex, has a
planar realization in the prescribed spine order. -/
theorem page_planar (layers : List Layer) (w page : Nat) : (pageGraph layers w page).Planar := by
  apply RimGrowth.ordered_planar
  intro a b c d ab bc cd top ac bd
  have h1 := (pageGraph_adj ..).mp ac
  have h2 := (pageGraph_adj ..).mp bd
  have ab' : a.val<b.val := ab
  have bc' : b.val<c.val := bc
  have cd' : c.val<d.val := cd
  rcases h1.2 with A|B|C|D|E|F|X|Y <;> try omega
  · rcases h2.2 with A|B|C|D|E|F|U|V <;> try omega
    · exact chords_noncross X U ab' bc' cd'
    · have := chord_increases V; omega
  · have := chord_increases Y; omega

private theorem global_width (layers : List Layer) : ∃ w, ∀ q∈layers, q.width ≤ w := by
  induction layers with
  | nil => exact ⟨0, by simp⟩
  | cons q tail ih =>
    obtain ⟨w,hw⟩ := ih
    refine ⟨max q.width w, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact Nat.le_max_left ..
    · exact (hw _ hp).trans (Nat.le_max_right ..)

/-- Every actual port arc in a replay belongs to one of two globally
planar page graphs, with the same order and numbers of ports on both. -/
theorem replay_pages {ds : List Nat} (h : NumericalTrace ds []) :
    ∃ s layers w, History ds s layers ∧ s.row=[] ∧
      (∀ t : Fin layers.length, ∀ {i j}, layers[t].arc i j →
        Chord layers w (t.val%2) (slot w t.val i) (slot w (t.val+1) j)) ∧
      (pageGraph layers w 0).Planar ∧ (pageGraph layers w 1).Planar := by
  obtain ⟨s,trace,closed,_⟩ := successful_trace_drawn_replay h
  obtain ⟨layers,hist⟩ := history_of_drawn trace
  obtain ⟨w,bound⟩ := global_width layers
  refine ⟨s,layers,w,hist,closed, ?_, page_planar .., page_planar ..⟩
  intro t i j edge
  have width := bound _ (List.getElem_mem t.isLt)
  have bounds := layers[t].bounded edge
  exact ⟨t,i,j,rfl,bounds.1.trans_le width,bounds.2.trans_le width,edge,rfl,rfl⟩

/-- Both page trees use exactly the same number and ordering of boundary
vertices. The additional edges triangulate their respective disks. -/
theorem page_triangulation (layers : List Layer) (w page : Nat) :
    ∃ t : PolygonMidpoint.Shape, t.size=(layers.length+1)*w ∧
      ∀ a b, Chord layers w page a b → (a,b) ∈ t.edges 0 := by
  let n := (layers.length+1)*w
  have nc : PolygonCompletion.Noncrossing (Chord layers w page) :=
    fun _ _ _ _ ab bc cd ac bd => chords_noncross ac bd ab bc cd
  obtain ⟨t,size,inside⟩ := PolygonCompletion.cover_interval _ nc 0 (n+1) (by omega)
  refine ⟨t,by simpa [n] using size, ?_⟩
  intro a b edge
  obtain ⟨x,y,_,label,_,upper,_⟩ := chord_edge edge
  exact inside _ _ (Nat.zero_le _) (chord_increases edge) (by dsimp [n]; omega) edge

/-- The signed parabola over an interval gives one simultaneous Euclidean
curve for every edge; all port vertices are the points `(index, 0)`. -/
def arch (a b : Nat) (x : ℝ) := (x - a) * (b - x)

def curveY (page a b : Nat) (x : ℝ) := if page=0 then arch a b x else -arch a b x

private theorem arch_nested {a b c d : Nat} {x : ℝ} (ac : a≤c) (db : d≤b)
    (left : (c : ℝ)<x) (right : x<d) (strict : a<c ∨ d<b) : arch c d x < arch a b x := by
  have ac' : (a:ℝ) ≤ c := by exact_mod_cast ac
  have db' : (d:ℝ) ≤ b := by exact_mod_cast db
  unfold arch
  rcases strict with small|small
  · have lt : (a:ℝ)<c := by exact_mod_cast small
    exact (mul_lt_mul_of_pos_right (by linarith : x-c<x-a) (by linarith : 0<(d:ℝ)-x)).trans_le
      (mul_le_mul_of_nonneg_left (by linarith : (d:ℝ)-x≤b-x) (by linarith))
  · have lt : (d:ℝ)<b := by exact_mod_cast small
    exact (mul_le_mul_of_nonneg_right (by linarith : x-c≤x-a) (by linarith : 0≤(d:ℝ)-x)).trans_lt
      (mul_lt_mul_of_pos_left (by linarith : (d:ℝ)-x<b-x) (by linarith))

private theorem same_page_interiors {layers w page a b c d} {x : ℝ}
    (ab : Chord layers w page a b) (cd : Chord layers w page c d)
    (l1 : (a:ℝ)<x) (r1 : x<b) (l2 : (c:ℝ)<x) (r2 : x<d)
    (meet : arch a b x=arch c d x) : a=c ∧ b=d := by
  have cb : c<b := by exact_mod_cast l2.trans r1
  have ad : a<d := by exact_mod_cast l1.trans r2
  have left_eq : a=c := by
    rcases lt_trichotomy a c with lt|eq|gt
    · by_cases nested : d≤b
      · exact False.elim ((arch_nested lt.le nested l2 r2 (.inl lt)).ne meet.symm)
      · exact False.elim (chords_noncross ab cd lt cb (by omega))
    · exact eq
    · by_cases nested : b≤d
      · exact False.elim ((arch_nested gt.le nested l1 r1 (.inl gt)).ne meet)
      · exact False.elim (chords_noncross cd ab gt ad (by omega))
  subst c
  refine ⟨rfl, ?_⟩
  unfold arch at meet
  have eql := mul_left_cancel₀ (by linarith : x-(a:ℝ) ≠ 0) meet
  exact_mod_cast (show (b:ℝ)=d by linarith)

/-- Interior points of curves in the common plane coincide only when both
the page and the two named ports coincide. -/
theorem curves_disjoint {layers w p q a b c d} {x : ℝ} (hp : p≤1) (hq : q≤1)
    (ab : Chord layers w p a b) (cd : Chord layers w q c d)
    (l1 : (a:ℝ)<x) (r1 : x<b) (l2 : (c:ℝ)<x) (r2 : x<d)
    (meet : curveY p a b x=curveY q c d x) : p=q ∧ a=c ∧ b=d := by
  have pos : 0<arch a b x := mul_pos (sub_pos.mpr l1) (sub_pos.mpr r1)
  have pos' : 0<arch c d x := mul_pos (sub_pos.mpr l2) (sub_pos.mpr r2)
  have same : p=q := by
    by_contra ne
    rcases (show (p=0 ∧ q=1) ∨ (p=1 ∧ q=0) by omega) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      simp only [curveY, ↓reduceIte, Nat.one_ne_zero] at meet <;> linarith
  subst q
  refine ⟨rfl, same_page_interiors ab cd l1 r1 l2 r2 ?_⟩
  by_cases zero : p=0 <;> simpa [curveY,zero] using meet

/-- The only points of an edge on the common line of all port vertices
are its two endpoints. -/
theorem curve_on_spine {page a b : Nat} {x : ℝ} : curveY page a b x=0 ↔ x=a ∨ x=b := by
  by_cases zero : page=0 <;> simp [curveY, zero, arch, sub_eq_zero, eq_comm (a := (b : ℝ))]

/- RowPageDisks joins the two triangulated pages with an equatorial strip.
RowSphere.portGraph_planar uses the resulting spherical rotation and contracts
the matching between the two copies of the spine. -/
end Recognition.RowPlane
