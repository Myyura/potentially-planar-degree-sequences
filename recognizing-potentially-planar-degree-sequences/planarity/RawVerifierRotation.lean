import RawVerifierData
import RawVerifierOrbit

/-! The rotation checker constructs its generator arcs once and charges all
four families of unions, their orbit counts, and each inverse/rotation test. -/
namespace Recognition.RawVerifierRotation
open SparseBoundary Wagner RotationVerifier ComplexityCost OrbitTable RawVerifierData

private def links (xs : List D) (f : D → Meter D) : Meter (Rows D) :=
  RawVerifierData.mapM (fun x =>
    let y:=f x
    ⟨(x,y.value),y.work+1⟩) xs

private theorem links_value (xs : List D) (f : D → Meter D) :
    (links xs f).value=xs.map (fun x => (x,(f x).value)) := by simp [links,map_value]

private theorem links_work (xs : List D) (f : D → Meter D) (b : Nat)
    (bound : ∀ x,(f x).work≤b) : (links xs f).work≤xs.length*(b+3)+1 := by
  exact map_work _ _ (b+1) (fun x=>Nat.add_le_add_right (bound x) 1)

private def localTest {G : Graph n} (xs : List (toSimple G).Dart)
    (f g r : Rows (toSimple G).Dart) (x : (toSimple G).Dart) : Meter Bool :=
  let a:=RawVerifierOrbit.read f x
  let b:=RawVerifierOrbit.read g x
  let ba:=RawVerifierOrbit.read g a.value
  let ab:=RawVerifierOrbit.read f b.value
  let l:=RawVerifierOrbit.read r x
  let ends:=allM (fun y : (toSimple G).Dart =>
    let k:=RawVerifierOrbit.read r y
    ⟨x.fst != y.fst || l.value==k.value,k.work+3⟩) xs
  ⟨ba.value==x && ab.value==x && a.value.fst==x.fst && ends.value,
    a.work+b.work+ba.work+ab.work+l.work+ends.work+5⟩

private theorem local_value {G : Graph n} (xs : List (toSimple G).Dart)
    (f g r : Rows (toSimple G).Dart) (x : (toSimple G).Dart) : (localTest xs f g r x).value=
      (key g (key f x)==x && key f (key g x)==x && (key f x).fst==x.fst &&
        xs.all (fun y=>x.fst != y.fst || key r x==key r y)) := by
  simp only [localTest,RawVerifierOrbit.read_value,all_value]

private theorem local_work {G : Graph n} (xs : List (toSimple G).Dart)
    (f g r : Rows (toSimple G).Dart) (x : (toSimple G).Dart) {m : Nat}
    (sx : xs.length=m) (sf : f.length≤m) (sg : g.length≤m) (sr : r.length≤m) :
    (localTest xs f g r x).work≤64*(m+2)^2 := by
  let cap := 8*(m+1)
  have get (t : Rows (toSimple G).Dart) (h : t.length≤m) (v) :
      (RawVerifierOrbit.read t v).work≤cap :=
    (RawVerifierOrbit.read_work _ _).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))
  unfold localTest
  have e := all_work (fun y : (toSimple G).Dart =>
    (⟨x.fst != y.fst || (RawVerifierOrbit.read r x).value==(RawVerifierOrbit.read r y).value,
    (RawVerifierOrbit.read r y).work+3⟩ : Meter Bool)) xs (cap+3)
    (fun v=>Nat.add_le_add_right (get r sr v) 3)
  rw [sx] at e
  have h₁:=get f sf x;have h₂:=get g sg x
  have h₃:=get g sg (RawVerifierOrbit.read f x).value
  have h₄:=get f sf (RawVerifierOrbit.read g x).value
  have h₅:=get r sr x
  dsimp only at e ⊢
  dsimp [cap] at *
  nlinarith [Nat.zero_le (m*m)]

/-- No permutation or quotient enumeration: each call below returns its
actual labelled union table, also consumed by the remainder of the check. -/
def check {G : Graph n} (xs : List (toSimple G).Dart) (f g : Rows (toSimple G).Dart) :
    Meter Bool :=
  let a:=links xs (RawVerifierOrbit.read f)
  let b:=links xs (fun d => ⟨d.symm,1⟩)
  let c:=links xs (fun d => RawVerifierOrbit.read f d.symm)
  let rr:=RawVerifierOrbit.run xs a.value
  let rc:=RawVerifierOrbit.run xs (a.value++b.value)
  let re:=RawVerifierOrbit.run xs b.value
  let rf:=RawVerifierOrbit.run xs c.value
  let cc:=RawVerifierOrbit.count rc.value
  let vc:=RawVerifierOrbit.count rr.value
  let ec:=RawVerifierOrbit.count re.value
  let fc:=RawVerifierOrbit.count rf.value
  let tests:=allM (localTest xs f g rr.value) xs
  ⟨(f.length≤xs.length && g.length≤xs.length) && tests.value &&
    decide (xs.length+2*cc.value=vc.value+ec.value+fc.value),
    a.work+b.work+c.work+rr.work+rc.work+re.work+rf.work+cc.work+vc.work+ec.work+fc.work+
      tests.work+f.length+g.length+3*xs.length+a.value.length+10⟩

theorem check_value (G : Graph n) (f g : Rows (toSimple G).Dart) :
    (check (darts G) f g).value=checkRotation G ⟨f,g⟩ := by
  simp only [check,links_value,RawVerifierOrbit.read_value,RawVerifierOrbit.run_value,
    RawVerifierOrbit.count_value,all_value,local_value]
  rfl

def cost (m : Nat) :=
  let scans:=m*(8*(m+1)+3)+1
  let orbit:=64*(3*m+4)^4
  let classes:=16*(m+2)^2
  let keys:=m*(64*(m+2)^2+2)+1
  3*scans+4*orbit+4*classes+keys+6*m+10

theorem check_work {G : Graph n} (xs : List (toSimple G).Dart) (f g : Rows (toSimple G).Dart)
    (sf : f.length≤xs.length) (sg : g.length≤xs.length) : (check xs f g).work≤cost xs.length := by
  let m:=xs.length
  let a:=links xs (RawVerifierOrbit.read f)
  let b:=links xs (fun d => (⟨d.symm,1⟩ : Meter (toSimple G).Dart))
  let c:=links xs (fun d => RawVerifierOrbit.read f d.symm)
  have al : a.value.length=m := by simp [a,m,links_value]
  have bl : b.value.length=m := by simp [b,m,links_value]
  have cl : c.value.length=m := by simp [c,m,links_value]
  let scans:=m*(8*(m+1)+3)+1
  let groups:=64*(3*m+4)^4
  let classes:=16*(m+2)^2
  have fee (d) : (RawVerifierOrbit.read f d).work≤8*(m+1) :=
    (RawVerifierOrbit.read_work _ _).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right sf 1))
  have aw : a.work≤scans := links_work xs _ _ fee
  have bw : b.work≤scans := links_work xs _ _ (fun _=>by dsimp;omega)
  have cw : c.work≤scans := links_work xs _ _ (fun d=>fee d.symm)
  have orbit (es : Rows (toSimple G).Dart) (sz : es.length≤2*m) :
      (RawVerifierOrbit.run xs es).work≤groups := by
    apply (RawVerifierOrbit.run_work _ _).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    change m+es.length+4≤3*m+4
    omega
  have cnt (es : Rows (toSimple G).Dart) :
      (RawVerifierOrbit.count (RawVerifierOrbit.run xs es).value).work≤classes := by
    simpa [classes,m,RawVerifierOrbit.run_length] using RawVerifierOrbit.count_work (RawVerifierOrbit.run xs es).value
  have o₁:=orbit a.value (by omega)
  have o₂:=orbit (a.value++b.value) (by rw [List.length_append,al,bl];omega)
  have o₃:=orbit b.value (by omega)
  have o₄:=orbit c.value (by omega)
  have c₁:=cnt a.value;have c₂:=cnt (a.value++b.value);have c₃:=cnt b.value;have c₄:=cnt c.value
  have tests:=all_work (localTest xs f g (RawVerifierOrbit.run xs a.value).value) xs (64*(m+2)^2)
    (fun x=> local_work _ _ _ _ x rfl sf sg (RawVerifierOrbit.run_length _ _).le)
  change a.work+b.work+c.work+ (RawVerifierOrbit.run xs a.value).work+
    (RawVerifierOrbit.run xs (a.value++b.value)).work+(RawVerifierOrbit.run xs b.value).work+
    (RawVerifierOrbit.run xs c.value).work+(RawVerifierOrbit.count (RawVerifierOrbit.run xs (a.value++b.value)).value).work+
    (RawVerifierOrbit.count (RawVerifierOrbit.run xs a.value).value).work+
    (RawVerifierOrbit.count (RawVerifierOrbit.run xs b.value).value).work+
    (RawVerifierOrbit.count (RawVerifierOrbit.run xs c.value).value).work+
    (allM (localTest xs f g (RawVerifierOrbit.run xs a.value).value) xs).work+
    f.length+g.length+3*m+a.value.length+10≤3*scans+4*groups+4*classes+(m*(64*(m+2)^2+2)+1)+6*m+10
  change f.length≤m at sf;change g.length≤m at sg
  change _≤m*(64*(m+2)^2+2)+1 at tests
  omega

theorem polynomial (m : Nat) : cost m≤40000*(m+4)^4 := by
  unfold cost;ring_nf;omega

end Recognition.RawVerifierRotation
