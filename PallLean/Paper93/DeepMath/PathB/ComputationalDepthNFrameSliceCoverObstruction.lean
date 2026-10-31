import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRecursivePortCost

/-!
# N-Frame: the slice-cover obstruction — ports must flip, and SAT's mediators must track their selectors

The SAT-specific input to the recursive engine, at its provable strength:

  `SliceCover` / `sliceCover_of_mediated` — the covering complexity object, and its instantiation: mediated
        SAT selectors produce a selector-blind slice cover within the same budget.
  `slice_ports_must_flip` — **PROVED, the obstruction core**: wherever `f` is sensitive to a mediated
        selector, **some mediator wire flips** — the port vector cannot sit still while the output moves,
        because the slices are blind and the determination identity leaves the ports as the only channel.
  `sat3_port_tracks_selector` — **PROVED, the SAT input**: a mediated slot-2 selector's own mediator wire
        flips with the selector at the empty-clause context — the port provably *carries the selector's
        identity behavior*.  The mediator is not free to compute something unrelated: SAT's sensitivity
        structure is pushed down into the port wires.

## Honest scope

The tracking theorem is the first SAT-specific constraint on mediator computation: every mediated selector
forces its port wire to reproduce the selector's behavior at the sensitivity contexts.  What remains open is
the aggregate: many tracked ports, each a wire of the same circuit, each inheriting a block's context
structure — turning that into `Ω(K)` forced cost beyond the shared budget is the standing face, and the
conditional cash-out (duplication/reuse → kills; mediation → tracked ports) is exactly the terminal map.
Open, not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The covering complexity object -/

/-- A selector-blind slice cover of `f` through the mediator ports of `c`, with slice budget `B`. -/
def SliceCover {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (S : List (Fin n × ℕ × ℕ)) (B : ℕ) : Prop :=
  ∃ Φ : (ℕ → Bool) → (Fin n → Bool) → Bool,
    (∀ v : ℕ → Bool, cbudget (Φ v) ≤ B) ∧
    (∀ (v : ℕ → Bool) (x : Fin n → Bool) (t : Fin n × ℕ × ℕ), t ∈ S → ∀ b : Bool,
      Φ v (Function.update x t.1 b) = Φ v x) ∧
    (∀ x, f x = Φ (fun r => (runFrom x [] c).getD r false) x)

/-- **Instantiation (proved)**: mediated selectors produce a slice cover within the same budget. -/
theorem sliceCover_of_mediated {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (S : List (Fin n × ℕ × ℕ)) (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2) :
    SliceCover f c S (cbudget f) :=
  recursive_port_accounting f c hcomp hmin S hS

/-! ### The obstruction core: ports must flip -/

/-- **PORTS MUST FLIP (proved)**: wherever `f` is sensitive to a mediated selector, some mediator wire
flips — the slices are blind, so the ports are the only channel. -/
theorem slice_ports_must_flip {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (S : List (Fin n × ℕ × ℕ))
    (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2)
    (t : Fin n × ℕ × ℕ) (ht : t ∈ S) (x : Fin n → Bool)
    (hsens : f (Function.update x t.1 true) ≠ f (Function.update x t.1 false)) :
    ∃ t' ∈ S, (runFrom (Function.update x t.1 true) [] c).getD t'.2.2 false
      ≠ (runFrom (Function.update x t.1 false) [] c).getD t'.2.2 false := by
  by_contra hno
  push_neg at hno
  apply hsens
  apply joint_cube_factor f c hcomp S hS
  · intro i' hi'
    have hne := hi' t ht
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
  · exact hno

/-! ### The SAT input: mediators track their selectors -/

/-- **THE TRACKING THEOREM (proved)**: a mediated slot-2 selector's mediator wire flips with the selector at
the empty-clause context — the port carries the selector's identity behavior. -/
theorem sat3_port_tracks_selector (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) (c : List (CGate N))
    (hcomp : computes c (sat3Family N)) (p r : ℕ)
    (hmed : MediatedAt c (sat3S2Sel N cIdx j) p r) :
    (runFrom (Function.update (sat3ZBase N cIdx) (sat3S2Sel N cIdx j) true) [] c).getD
        r false
      ≠ (runFrom (Function.update (sat3ZBase N cIdx) (sat3S2Sel N cIdx j) false) [] c).getD
        r false := by
  have hsens : sat3Family N (Function.update (sat3ZBase N cIdx) (sat3S2Sel N cIdx j) true)
      ≠ sat3Family N (Function.update (sat3ZBase N cIdx) (sat3S2Sel N cIdx j) false) := by
    rw [sat3ZBase_flip_sat N hv cIdx j]
    rw [show Function.update (sat3ZBase N cIdx) (sat3S2Sel N cIdx j) false
        = sat3ZBase N cIdx by
      rw [← sat3ZBase_s2 N cIdx cIdx j]
      exact Function.update_eq_self _ _]
    rw [sat3ZBase_unsat N cIdx]
    decide
  have h := slice_ports_must_flip (sat3Family N) c hcomp
    [(⟨sat3S2Sel N cIdx j, p, r⟩ : Fin N × ℕ × ℕ)]
    (by
      intro t' ht'
      rw [List.mem_singleton] at ht'
      subst ht'
      exact hmed)
    (⟨sat3S2Sel N cIdx j, p, r⟩ : Fin N × ℕ × ℕ) List.mem_cons_self
    (sat3ZBase N cIdx) hsens
  obtain ⟨t', ht', hflip⟩ := h
  rw [List.mem_singleton] at ht'
  subst ht'
  exact hflip

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sliceCover_of_mediated
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.slice_ports_must_flip
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_port_tracks_selector
