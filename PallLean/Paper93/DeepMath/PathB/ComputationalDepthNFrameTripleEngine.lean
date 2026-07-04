import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCoverageAllPins

/-!
# N-Frame: the triple engine — rectangle closure formalized, the monotonicity obstruction removed

The rectangle-closure route, delivered as a second kill engine.  `two_squares_kill_split` needs an
XOR-square, which monotone coordinates (all selectors) can never supply.  This engine replaces it:

  `odd_matrix_triples_kill` — **PROVED, the core (pure logic)**: an odd-parity square forces the op's full
        2×2 matrix to have an odd number of ones — a unique minority cell.  A sat/sat/unsat L-triple
        (`f(u) = 1, f(u^{s₀t₀}) = 1, f(u^{t₀}) = 0`) kills the one-one table (both ones must be the unique
        cell, forcing the third corner to one); an unsat/unsat/sat triple kills the three-ones table.
        Degenerate ops die inside the triples themselves (each triple exhibits sensitivity in both
        coordinates).
  `triples_kill_split` — **PROVED, the engine**: a proper split with `s₀ ∈ S`, `t₀ ∉ S` dies from one
        odd square and two L-triples at the pair — **ten canonical evaluations, no XOR-square anywhere**.
        Every ingredient is an AND/OR-shaped pattern, available for monotone coordinates.

## Honest scope

This closes the structural gap in the discharge plan: selector-involved pairs, which admit no XOR-square,
can now be killed by odd squares and L-triples — OR-shaped patterns that SAT's selector semantics produce
naturally (`f(ZBase) = 0`, single flips `= 1`, double flips `= 1` are exactly L-triples and odd squares).
What remains is production: the odd square and both L-triples per coordinate-pair type, and the spanning
argument (both-pattern pairs covering every cut).  Named, not claimed.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

set_option maxHeartbeats 1600000 in
/-- **THE CORE (proved)**: an odd op-matrix plus the two L-triples is contradictory. -/
theorem odd_matrix_triples_kill (op : Bool → Bool → Bool)
    (p q p' q' a b a' b' c d c' d' : Bool)
    (hodd : xor (xor (op p q) (op p' q)) (xor (op p q') (op p' q')) = true)
    (h11 : op a b = true) (h12 : op a' b' = true) (h13 : op a b' = false)
    (h01 : op c d = false) (h02 : op c' d' = false) (h03 : op c d' = true) : False := by
  cases p <;> cases q <;> cases p' <;> cases q' <;>
    cases a <;> cases b <;> cases a' <;> cases b' <;>
      cases c <;> cases d <;> cases c' <;> cases d' <;>
        simp_all

/-- **THE ENGINE (proved)**: one odd square and two L-triples at a separated pair kill any split — no
XOR-square needed, so monotone coordinates are in reach. -/
theorem triples_kill_split {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (s₀ t₀ : Fin n) (hs₀ : s₀ ∈ S) (ht₀ : t₀ ∉ S) (hst : s₀ ≠ t₀)
    (w u₁ u₀ : Fin n → Bool)
    (hodd : xor (xor (f w) (f (Function.update w s₀ (!(w s₀)))))
        (xor (f (Function.update w t₀ (!(w t₀))))
          (f (Function.update (Function.update w s₀ (!(w s₀))) t₀ (!(w t₀))))) = true)
    (h11 : f u₁ = true)
    (h12 : f (Function.update (Function.update u₁ s₀ (!(u₁ s₀))) t₀ (!(u₁ t₀))) = true)
    (h13 : f (Function.update u₁ t₀ (!(u₁ t₀))) = false)
    (h01 : f u₀ = false)
    (h02 : f (Function.update (Function.update u₀ s₀ (!(u₀ s₀))) t₀ (!(u₀ t₀))) = false)
    (h03 : f (Function.update u₀ t₀ (!(u₀ t₀))) = true) : False := by
  classical
  have hhs : ∀ (z : Fin n → Bool) (v : Bool), h (Function.update z s₀ v) = h z := by
    intro z v
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hcon => hi (by rw [hcon]; exact hs₀)) _ _
  have hgt : ∀ (z : Fin n → Bool) (v : Bool), g (Function.update z t₀ v) = g z := by
    intro z v
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hcon => ht₀ (by rw [← hcon]; exact hi)) _ _
  -- the double corners: h sees only the t₀ flip
  have hhdw : h (Function.update (Function.update w s₀ (!(w s₀))) t₀ (!(w t₀)))
      = h (Function.update w t₀ (!(w t₀))) := by
    rw [show Function.update (Function.update w s₀ (!(w s₀))) t₀ (!(w t₀))
        = Function.update (Function.update w t₀ (!(w t₀))) s₀ (!(w s₀)) from
      Function.update_comm hst _ _ _]
    exact hhs _ _
  have hhd1 : h (Function.update (Function.update u₁ s₀ (!(u₁ s₀))) t₀ (!(u₁ t₀)))
      = h (Function.update u₁ t₀ (!(u₁ t₀))) := by
    rw [show Function.update (Function.update u₁ s₀ (!(u₁ s₀))) t₀ (!(u₁ t₀))
        = Function.update (Function.update u₁ t₀ (!(u₁ t₀))) s₀ (!(u₁ s₀)) from
      Function.update_comm hst _ _ _]
    exact hhs _ _
  have hhd0 : h (Function.update (Function.update u₀ s₀ (!(u₀ s₀))) t₀ (!(u₀ t₀)))
      = h (Function.update u₀ t₀ (!(u₀ t₀))) := by
    rw [show Function.update (Function.update u₀ s₀ (!(u₀ s₀))) t₀ (!(u₀ t₀))
        = Function.update (Function.update u₀ t₀ (!(u₀ t₀))) s₀ (!(u₀ s₀)) from
      Function.update_comm hst _ _ _]
    exact hhs _ _
  rw [hf, hf, hf, hf] at hodd
  rw [hf] at h11 h12 h13 h01 h02 h03
  rw [hhdw] at hodd
  rw [hhd1] at h12
  rw [hhd0] at h02
  simp only [hgt, hhs] at hodd h12 h13 h02 h03
  exact odd_matrix_triples_kill op
    (g w) (h w) (g (Function.update w s₀ (!(w s₀))))
    (h (Function.update w t₀ (!(w t₀))))
    (g u₁) (h u₁) (g (Function.update u₁ s₀ (!(u₁ s₀))))
    (h (Function.update u₁ t₀ (!(u₁ t₀))))
    (g u₀) (h u₀) (g (Function.update u₀ s₀ (!(u₀ s₀))))
    (h (Function.update u₀ t₀ (!(u₀ t₀))))
    hodd h11 h12 h13 h01 h02 h03

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.odd_matrix_triples_kill
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.triples_kill_split
