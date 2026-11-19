import SparseBoundary.GraphSupports

namespace SparseBoundary

/-- The octahedral range of the six-core classification. The variable m is
    the number of extra edge copies and every larger budget is permitted. -/
theorem six_octahedral_range (a b c d e f m t : Nat)
    (hab : b≤a) (hbc : c≤b) (hcd : d≤c) (hde : e≤d) (hef : f≤e) (hf : 4≤f)
    (sum : a+b+c+d+e+f=24+2*m) (ends : a+f≤m+8) (budget : m≤t) :
    Planaric ([a,b,c,d,e,f] ++ List.replicate t 2) := by
  have pl := Graph.Octahedron.realize (a-4) (b-4) (c-4) (d-4) (e-4) (f-4) m
    (by omega) (by omega) (by omega) (by omega)
  simp only [show 4+(a-4)=a by omega,show 4+(b-4)=b by omega,
    show 4+(c-4)=c by omega,show 4+(d-4)=d by omega,show 4+(e-4)=e by omega,
    show 4+(f-4)=f by omega] at pl
  have p := (planaric_perm List.perm_append_comm).mp pl
  have q := planaric_add_twos p ⟨a,List.mem_append_right _ (by simp), by omega⟩ (t-m)
  have eqn : List.replicate (t-m) 2 ++ List.replicate m 2 = List.replicate t 2 := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp; omega, by simp⟩
  rw [← List.append_assoc,eqn] at q
  exact (planaric_perm List.perm_append_comm).mp q

end SparseBoundary
