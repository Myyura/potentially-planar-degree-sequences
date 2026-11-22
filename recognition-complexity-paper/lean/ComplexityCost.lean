import Reduction

/-! Work on a unit-cost RAM with immutable singly linked lists. A stream visit
means one iteration of a constant-size word kernel: inspect a cell, perform
a bounded number of word operations, allocate a bounded number of cells.
Each stream also charges one terminal visit. List membership uses a sequential
scan. Integer fields and the bit index fit in O(log U) bits (U is the unary
input length); multiply, divide, shift, bit-length and test-bit act on words. List-valued
arguments and results are pointers. This is a RAM work bound up to absolute
constant factors, not a clock measurement of Lean's compiled runtime.
-/
namespace Recognition.ComplexityCost
open Reduction

structure Meter (α : Type) where
  value : α
  work : Nat

/-- Constant-kernel list scans and direct output streams. -/
private def stream (v : α) (visits : Nat) : Meter α := ⟨v,visits+1⟩

private def countedMap (f : α → β) (xs : List α) := stream (xs.map f) xs.length
private def selected (p : α → Bool) (xs : List α) := stream (xs.filter p) xs.length
private def copied (xs ys : List α) := stream (xs++ys) xs.length
private def enumerated (n : Nat) := stream (List.range n) n
private def repeated (n : Nat) (a : α) := stream (List.replicate n a) n
private def indexed (xs : List α) := stream xs.zipIdx xs.length
private def sumWords (xs : List Nat) := stream xs.sum xs.length

/-- Flat-map also pays for copying the callback's result into the new list. -/
private def concatMap (f : α → Meter (List β)) : List α → Meter (List β)
  | [] => ⟨[],1⟩
  | a::xs =>
    let head := f a
    let tail := concatMap f xs
    let result := copied head.value tail.value
    ⟨result.value,1+head.work+tail.work+result.work⟩

private theorem concat_value (f : α → Meter (List β)) (xs : List α) :
    (concatMap f xs).value = xs.flatMap (fun a => (f a).value) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [concatMap,copied,stream,ih]

private theorem concat_work (f : α → Meter (List β)) (xs : List α) (k : Nat)
    (cost : ∀ a ∈ xs, (f a).work+(f a).value.length ≤ k) :
    (concatMap f xs).work ≤ 1+xs.length*(k+2) := by
  induction xs with
  | nil => simp [concatMap]
  | cons a xs ih =>
    have h := cost a (by simp)
    have t := ih (fun a ha => cost a (List.mem_cons_of_mem _ ha))
    simp [concatMap,copied,stream,Nat.succ_mul]; omega

/-- The base is a pair of triples with a constant-degree run between them.
The four bonus entries per bin are emitted by one constant kernel per bin. -/
private def source (I : Instance) : Meter (List Nat) :=
  let base := stream (skeletonBase I.bins) (skeletonOrder I)
  let extra := stream (bonuses I.capacity I.bins) I.bins
  let core := stream (List.zipWith (·+·) base.value extra.value) (skeletonOrder I)
  let W := sumWords I.weights
  let items := repeated W.value 4
  let caps := repeated I.bins 3
  let front := copied core.value items.value
  let result := copied front.value caps.value
  ⟨result.value,base.work+extra.work+core.work+W.work+items.work+caps.work+front.work+result.work⟩

private theorem source_value (I : Instance) : (source I).value = sourceTable I := rfl

private def itemPass (k : Nat) : List Nat → Meter (List Edge)
  | [] => ⟨[],1⟩
  | w::ws =>
    let ids := enumerated (w-1)
    let edges := countedMap (fun j => Edge.mk (k+j) (k+j+1) (6+(k+j)%2)) ids.value
    let tail := itemPass (k+w) ws
    let result := copied edges.value tail.value
    ⟨result.value,1+ids.work+edges.work+tail.work+result.work⟩

private theorem item_value (k : Nat) (ws : List Nat) : (itemPass k ws).value = itemEdges k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih => simp [itemPass,copied,stream,countedMap,enumerated,itemEdges,ih]

private theorem item_work (k : Nat) (ws : List Nat) :
    (itemPass k ws).work ≤ 1+3*ws.sum+4*ws.length := by
  induction ws generalizing k with
  | nil => simp [itemPass]
  | cons w ws ih =>
    have h := ih (k+w)
    simp [itemPass,enumerated,countedMap,copied,stream]; omega

private def edgesPass (I : Instance) : Meter (List Edge) :=
  let q := skeletonOrder I
  let cube := concatMap (fun d =>
    let ids := enumerated (q-d)
    let edges := countedMap (fun v => Edge.mk v (v+d) (2*(d-1)+(v/d)%2)) ids.value
    ⟨edges.value,ids.work+edges.work⟩) [1,2,3]
  let items := itemPass q I.weights
  let W := sumWords I.weights
  let ids := enumerated I.bins
  let caps := countedMap (fun j => Edge.mk (4*j) (q+W.value+j) 8) ids.value
  let front := copied cube.value items.value
  let result := copied front.value caps.value
  ⟨result.value,cube.work+items.work+W.work+ids.work+caps.work+front.work+result.work⟩

private theorem edges_value (I : Instance) : (edgesPass I).value = prescribed I := by
  simp [edgesPass,copied,stream,concat_value,item_value,enumerated,countedMap,sumWords,prescribed]

private def bitPass (w : Nat) (g : List Mark) : Meter (List Test) :=
  let indices := enumerated w
  let tests := concatMap (fun b =>
    let lo := selected (fun m : Mark => !(m.edge.left.testBit b)) g
    let hi := selected (fun m : Mark => m.edge.left.testBit b) g
    let u := copied (bothSides lo.value) (bothSides hi.value)
    ⟨u.value,lo.work+hi.work+u.work⟩) indices.value
  let result := copied (bothSides g) tests.value
  ⟨result.value,indices.work+tests.work+result.work⟩

private theorem bit_value (w : Nat) (g : List Mark) : (bitPass w g).value = classTests w g := by
  simp [bitPass,concat_value,copied,selected,stream,enumerated,classTests]

private theorem bit_work (w : Nat) (g : List Mark) :
    (bitPass w g).work ≤ 5+w*(2*g.length+12) := by
  unfold bitPass
  dsimp only [enumerated,selected,copied,stream]
  apply Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left (concat_work _ _ (2*g.length+9)
    (fun _ _ => by simp [bothSides]; omega)) _) _)
  simp [bothSides,Nat.mul_add]; omega

private def makeTests (I : Instance) (s : Nat) : Meter (List Test) :=
  let edges := edgesPass I
  let indexedEdges := indexed edges.value
  let allMarks := countedMap (fun (e,i) => Mark.mk e (fullOrder s+i)) indexedEdges.value
  let schedule := concatMap (fun c =>
    let group := selected (fun m : Mark => m.edge.color == c) allMarks.value
    let tests := bitPass (bitWidth s) group.value
    ⟨tests.value,group.work+tests.work⟩) (List.range 9)
  let result := copied [full,full,full] schedule.value
  ⟨result.value,edges.work+indexedEdges.work+allMarks.work+schedule.work+result.work+12⟩

private theorem tests_value (I : Instance) :
    (makeTests I (sourceTable I).length).value = allTests I := by
  simp [makeTests,allTests,schedule,colorClass,marks,concat_value,bit_value,copied,stream,
    countedMap,indexed,selected,edges_value]

/-- A membership query visits at most the whole label list. The algorithm
below scans every cell, even after finding an equal label. -/
private def memberScan (j : Nat) : List Nat → Meter Bool
  | [] => ⟨false,1⟩
  | x::xs =>
    let t := memberScan j xs
    ⟨(x == j) || t.value,t.work+1⟩

private theorem member_value (xs : List Nat) (v : Nat) : (memberScan v xs).value = xs.contains v := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : v=x
    · subst x; simp [memberScan]
    · simp [memberScan,ih,h,Ne.symm h]

private theorem member_work (xs : List Nat) (v : Nat) : (memberScan v xs).work = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [memberScan,ih]

private def raisePass (labels : List Nat) (i : Nat) : List Nat → Meter (List Nat)
  | [] => ⟨[],1⟩
  | d::ds =>
    let selected := memberScan i labels
    let tail := raisePass labels (i+1) ds
    ⟨(2*d-selected.value.toNat)::tail.value,1+selected.work+tail.work⟩

private theorem raise_value (ls : List Nat) (i : Nat) (ds : List Nat) :
    (raisePass ls i ds).value = (ds.zipIdx i).map (fun (d,v) => 2*d-(ls.contains v).toNat) := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih => simp [raisePass,member_value,ih,List.zipIdx_cons]

private theorem raise_work (ls : List Nat) (i : Nat) (ds : List Nat) :
    (raisePass ls i ds).work = 1+ds.length*(ls.length+2) := by
  induction ds generalizing i with
  | nil => simp [raisePass]
  | cons d ds ih => simp [raisePass,ih,member_work,Nat.succ_mul]; omega

private def layerPass (T : Table) (q : Test) : Meter Table :=
  let n := stream T.degrees.length T.degrees.length
  let t := stream q.group.length q.group.length
  let mx := countedMap Mark.marker q.group
  let ex := countedMap (endpoint q.side) q.group
  let zs := stream (List.range' T.fresh t.value) t.value
  let front := copied mx.value ex.value
  let labels := copied front.value zs.value
  let old := raisePass labels.value 0 T.degrees
  let stars := repeated (2*n.value-4-t.value) 3
  let result := copied old.value stars.value
  ⟨⟨result.value,n.value⟩,n.work+t.work+mx.work+ex.work+zs.work+front.work+labels.work+old.work+stars.work+result.work⟩

private theorem layer_value (T : Table) (q : Test) : (layerPass T q).value = layer T q := by
  simp [layerPass,layer,selectedLabels,raised,copied,repeated,countedMap,stream,raise_value]

private theorem layer_work (T : Table) (q : Test) :
    (layerPass T q).work ≤ 12+7*q.group.length + T.degrees.length*(6+3*q.group.length) := by
  simp [layerPass,repeated,countedMap,copied,stream,raise_work,raise_value,Nat.mul_add,Nat.mul_left_comm T.degrees.length 3 q.group.length]
  omega

private def run (T : Table) : List Test → Meter Table
  | [] => ⟨T,1⟩
  | q::qs =>
    let u := layerPass T q
    let t := run u.value qs
    ⟨t.value,1+u.work+t.work⟩

private theorem run_value (T : Table) (qs : List Test) : (run T qs).value = qs.foldl layer T := by
  induction qs generalizing T with
  | nil => rfl
  | cons q qs ih => simp [run,layer_value,ih]

def unarySize (I : Instance) :=
  1+I.weights.length+I.weights.sum+I.bins+I.capacity

private theorem sourceBound (I : Instance) : (sourceTable I).length ≤ 5*unarySize I+3 := by
  rw [source_order]; unfold unarySize skeletonOrder; omega

private theorem source_work (I : Instance) : (source I).work ≤ 12*((sourceTable I).length+I.weights.length+1) := by
  let core := (List.zipWith (·+·) (skeletonBase I.bins) (bonuses I.capacity I.bins))
  have length : core.length = skeletonOrder I := by
    have H := source_order I
    change ((core ++ List.replicate I.weights.sum 4) ++ List.replicate I.bins 3).length = _ at H
    simp at H; omega
  simp [source,sumWords,stream,repeated,copied,source_order]
  change core.length = skeletonOrder I at length
  simp [core] at length
  omega

private theorem item_len (k : Nat) (ws : List Nat) : (itemEdges k ws).length ≤ ws.sum := by
  induction ws generalizing k with
  | nil => simp [itemEdges]
  | cons w ws ih => have := ih (k+w); simp [itemEdges]; omega

private theorem edges_work (I : Instance) :
    (edgesPass I).work ≤ 32*((sourceTable I).length+I.weights.length+1) := by
  have h := item_work (skeletonOrder I) I.weights
  have k := item_len (skeletonOrder I) I.weights
  simp [edgesPass,concatMap,copied,countedMap,enumerated,sumWords,stream,item_value,source_order]
  omega

private theorem tests_work (I : Instance) :
    let s := (sourceTable I).length
    (makeTests I s).work ≤ 32*(s+I.weights.length+1)+12*s+20+
      9*(6*s+10+(s+1)*(12*s+12)+4*(s+1)) := by
  intro s
  have edges := edges_value I
  have eBound : (prescribed I).length ≤ 6*s := by
    have h := marker_room I
    unfold fullOrder at h
    change _ ≤ 6*(sourceTable I).length; omega
  let es := (edgesPass I).value
  let ms := (es.zipIdx.map fun (e,j) => Mark.mk e (fullOrder s+j))
  let proc := fun c =>
    let g := selected (fun m : Mark => m.edge.color == c) ms
    let t := bitPass (bitWidth s) g.value
    (⟨t.value,g.work+t.work⟩ : Meter (List Test))
  have mlen : ms.length ≤ 6*s := by simpa [ms,es,edges] using eBound
  have wle : bitWidth s ≤ s+1 := Nat.succ_le_succ (Nat.log2_le_self s)
  have per (c : Nat) : (proc c).work+(proc c).value.length ≤
      6*s+8+(s+1)*(12*s+12)+4*(s+1) := by
    let g := ms.filter (fun m => m.edge.color == c)
    have gsize : g.length ≤ 6*s := Nat.le_trans (List.length_filter_le _ _) mlen
    have hh := bit_work (bitWidth s) g
    have hh' := Nat.mul_le_mul wle (show 2*g.length+12 ≤ 12*s+12 by omega)
    change (ms.length+1+(bitPass (bitWidth s) g).work)+(bitPass (bitWidth s) g).value.length ≤ _
    rw [bit_value,classTests_length]
    omega
  have CH := concat_work proc (List.range 9) _ (fun c _ => per c)
  simp only [List.length_range] at CH
  have ed := edges_work I
  change (edgesPass I).work + (es.length+1) + (es.zipIdx.length+1) +
    (concatMap proc (List.range 9)).work + (3+1) + 12 ≤ _
  have elen : es.length ≤ 6*s := by simpa [es,edges] using eBound
  rw [List.length_zipIdx]
  change (edgesPass I).work ≤ 32*(s+I.weights.length+1) at ed
  omega

private def layerBudget (N : Nat) := 13+7*N+N*(6+3*N)

private theorem layerBudget_mono {M N : Nat} (h : M≤N) : layerBudget M ≤ layerBudget N := by
  have := Nat.mul_le_mul h (show 6+3*M≤6+3*N by omega)
  unfold layerBudget; omega

private theorem order_nondec (T : Table) (qs : List Test) :
    T.degrees.length ≤ (qs.foldl layer T).degrees.length := by
  induction qs generalizing T with
  | nil => exact Nat.le_refl _
  | cons q qs ih =>
    apply Nat.le_trans _ (ih (layer T q))
    rw [layer_order]; omega

private theorem run_work {A Z qs} (steps : Run A qs Z) :
    (run A qs).work ≤ 1+qs.length*layerBudget Z.degrees.length ∧
      Z = qs.foldl layer A := by
  induction steps with
  | nil => simp [run]
  | @cons A q qs Z hv nd bounded _ ih =>
    obtain ⟨ih,eq⟩ := ih
    have h := nd.length_le_of_subset (l₂ := List.range A.degrees.length)
      (fun _ h => List.mem_range.mpr (bounded _ h))
    simp [label_count] at h
    have le : A.degrees.length ≤ Z.degrees.length := by
      rw [eq]
      exact order_nondec A (q::qs)
    have sub := layer_work A q
    have prod := Nat.mul_le_mul le (show 6+3*q.group.length ≤ 6+3*Z.degrees.length by omega)
    refine ⟨?_,eq⟩
    simp only [run,layer_value,List.length_cons,Nat.succ_mul]
    unfold layerBudget at *; omega

private def validate (I : Instance) : Meter Bool :=
  let len := stream I.weights.length I.weights.length
  let total := sumWords I.weights
  let ranges := stream (I.weights.all (fun w => decide (I.capacity < 4*w ∧ 2*w < I.capacity))) I.weights.length
  let ok := decide (0 < I.bins ∧ len.value=3*I.bins ∧ total.value=I.bins*I.capacity) && ranges.value
  ⟨ok,len.work+total.work+ranges.work+5⟩

private theorem validate_value (I : Instance) : (validate I).value = true ↔ Valid I := by
  simp [validate,stream,sumWords,Valid,List.all_eq_true]
  constructor
  · rintro ⟨h,r⟩; obtain ⟨b,l,t⟩ := of_decide_eq_true h; exact ⟨b,l,t,r⟩
  · rintro ⟨b,l,t,r⟩; exact ⟨decide_eq_true ⟨b,l,t⟩,r⟩

private theorem validate_work (I : Instance) : (validate I).work = 3*(I.weights.length+1)+5 := by
  simp [validate,stream,sumWords]; omega

/-- Parsing checks and rejection of malformed tuples precede any expansion.
A length scan, a sum scan and a universal interval scan check validity. -/
def compile (I : Instance) : Meter (List Nat) :=
  let checks := validate I
  if checks.value then
    let A := source I
    let s := stream A.value.length A.value.length
    let tests := makeTests I s.value
    let final := run ⟨A.value,0⟩ tests.value
    ⟨final.value.degrees,checks.work+A.work+s.work+tests.work+final.work⟩
  else ⟨malformedOutput,checks.work+6⟩

theorem compile_value (I : Instance) : (compile I).value = reduceInstance I := by
  by_cases v : Valid I
  · simp [compile,validate_value,v,source_value,stream,tests_value,run_value,encode]
  · simp [compile,validate_value,v,malformedOutput]

/-- One fixed polynomial. S bounds the source order; N bounds the order at
every intermediate layer. The largest term pays for scanning all selected
labels for each previously written degree at each test. -/
def workBound (U : Nat) :=
  let S := 5*U+3
  let N := 3^57*S^73
  100*(S+U+1) + 9*(6*S+10+(S+1)*(12*S+12)+4*(S+1)) + (57+36*S)*layerBudget N

theorem compile_work (I : Instance) : (compile I).work ≤ workBound (unarySize I) := by
  let U := unarySize I
  let S := 5*U+3
  let s := (sourceTable I).length
  let N := 3^57*S^73
  have wl : I.weights.length ≤ U := by dsimp [U,unarySize]; omega
  have sl : s≤S := sourceBound I
  by_cases hv : Valid I
  · have er := encoded_polynomial I
    have en : (encode I).length ≤ N := Nat.le_trans er (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sl _))
    have runBound := (run_work (compilation_run I hv)).1
    change (run ⟨sourceTable I,0⟩ (allTests I)).work ≤ 1+(allTests I).length*layerBudget (encode I).length at runBound
    have logle := Nat.log2_le_self s
    have nr : (allTests I).length ≤ 57+36*S := by
      simp only [allTests,List.length_append,List.length_cons,List.length_nil,schedule_length,bitWidth]
      change 0+1+1+1+(9*(2+4*(s.log2+1))) ≤ _; omega
    have pd := Nat.mul_le_mul nr (layerBudget_mono en)
    have so := source_work I
    have prep := tests_work I
    change (makeTests I s).work ≤ 32*(s+I.weights.length+1)+12*s+20+9*(6*s+10+(s+1)*(12*s+12)+4*(s+1)) at prep
    have sq := Nat.mul_le_mul (Nat.succ_le_succ sl) (show 12*s+12 ≤ 12*S+12 by omega)
    change (s+1)*(12*s+12) ≤ (S+1)*(12*S+12) at sq
    simp only [compile,validate_value,ite_eq_left hv,validate_work,stream]
    rw [source_value,tests_value]
    change _ ≤ 100*(S+U+1) + 9*(6*S+10+(S+1)*(12*S+12)+4*(S+1)) + (57+36*S)*layerBudget N
    change (source I).work ≤ 12*(s+I.weights.length+1) at so
    change 3*(I.weights.length+1)+5+(source I).work+(s+1)+(makeTests I s).work+_ ≤ _
    omega
  · simp only [compile,validate_value,ite_eq_right hv,validate_work]
    change _ ≤ 100*(S+U+1) + _ + _
    omega


/-- The same metered address tests used by the packing reduction, exposed
for callers with a different prescribed-edge graph. -/
def addressTests := bitPass

theorem addressTests_value (w : Nat) (g : List Mark) :
    (addressTests w g).value = classTests w g := bit_value w g

theorem addressTests_work (w : Nat) (g : List Mark) :
    (addressTests w g).work ≤ 5+w*(2*g.length+12) := bit_work w g

/-- Execute the metered degree updates of a supplied layer schedule. -/
def applyLayers := run

theorem applyLayers_value (T : Table) (qs : List Test) :
    (applyLayers T qs).value = qs.foldl layer T := run_value T qs

theorem applyLayers_work {A Z qs} (h : Run A qs Z) :
    (applyLayers A qs).work ≤
      1+qs.length*(13+7*Z.degrees.length+Z.degrees.length*(6+3*Z.degrees.length)) :=
  (run_work h).1

end Recognition.ComplexityCost
