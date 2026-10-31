import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSimultaneousMediation

/-!
# N-Frame: the mediation face — the exact exception, and where the face really lives

The blockwise attack on the face, probed honestly — and step one returns an **exception theorem**, not a
capacity theorem:

  `passthrough_mediates` — **PROVED, the exact exception**: for *every* function and *every* variable, the
        identity mediator works — `h x := xᵢ`, `G v x := f (x[i := v])`.  A mediator whose cone touches
        *nothing but the selector itself* is semantically valid.  Hence **bottom-cone accounting cannot prove
        the face**: no argument about which blocks a mediator's cone sees can rule mediation out, because the
        minimal cone `{var gate, reader}` always suffices semantically.
  `minimal_bin_bidependent` — **PROVED, the syntactic counterpressure**: in a minimal circuit, every interior
        binary gate depends on **both** its arguments as an operation — projection gates are unary gates in
        disguise and die by the normal form.  So a circuit-realized pass-through mediator cannot be a bare
        projection; its second argument is operationally live, and the pressure moves to what that second
        wire and the circuit *above* the mediator must accomplish.

## Honest scope — the face, relocated

Steps 2–4 of the blockwise plan (cone/block overlap capacity) are closed by the exception: the face cannot be
won below the mediators.  What the two theorems together locate: the cost of simultaneous mediation lives in
the **top** — the `i`-free remainders `G_i` are all computed by the *same* gates above the mediators, and the
selector's information re-enters only through one bit each.  The face — that this shared top cannot service
`Ω(m·v)` SAT selectors cheaply — remains **open**, now with its locus identified: aggregate accounting of the
circuit above the mediator frontier, not of the cones below it.  The cash-out pipeline
(`unmediated_dup_or_reuse` → `cbudget_fanout_kill` → `2N + Ω(K)`) stands ready.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The exact exception: the pass-through mediator -/

/-- **THE EXCEPTION (proved)**: the identity mediator always works — a mediator cone touching only the
selector itself is semantically valid, for every function.  Bottom-cone accounting cannot prove the face. -/
theorem passthrough_mediates {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) :
    ∃ G : Bool → (Fin n → Bool) → Bool,
      (∀ x, f x = G (x i) x) ∧
      (∀ (v : Bool) (x : Fin n → Bool) (b' : Bool),
        G v (Function.update x i b') = G v x) := by
  refine ⟨fun v x => f (Function.update x i v), ?_, ?_⟩
  · intro x
    show f x = f (Function.update x i (x i))
    rw [Function.update_eq_self]
  · intro v x b'
    show f (Function.update (Function.update x i b') i v) = f (Function.update x i v)
    rw [Function.update_idem]

/-! ### The syntactic counterpressure: no projection gates inside minimal circuits -/

/-- **Normal form III (proved)**: in a minimal circuit for a non-constant function, every interior binary
gate depends on both of its arguments as an operation — projections are unary gates in disguise. -/
theorem minimal_bin_bidependent {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hnc : ∃ u w : Fin n → Bool, f u ≠ f w)
    (q : ℕ) (op : Bool → Bool → Bool) (a b : ℕ)
    (hg : c.getD q (CGate.cst false) = CGate.bin op a b)
    (hq : q < c.length - 1) :
    (¬∃ u : Bool → Bool, ∀ x y, op x y = u x) ∧
    (¬∃ u : Bool → Bool, ∀ x y, op x y = u y) := by
  have hqL : q < c.length := by omega
  have hsplit := circuit_split_at c q hqL
  rw [hg] at hsplit
  constructor
  · rintro ⟨u, hu⟩
    have hcomp' : computes (c.take q ++ CGate.bin op a b :: c.drop (q + 1)) f := by
      rw [← hsplit]
      exact hcomp
    have hrep := computes_congr_at (c.take q) (CGate.bin op a b) (CGate.un u a)
      (c.drop (q + 1)) f (by
        intro x
        show op ((runFrom x [] (c.take q)).getD a false)
            ((runFrom x [] (c.take q)).getD b false)
          = u ((runFrom x [] (c.take q)).getD a false)
        exact hu _ _) hcomp'
    have hlen : (c.take q ++ CGate.un u a :: c.drop (q + 1)).length = c.length :=
      splice_length c q (CGate.un u a) hqL
    have hlast := minimal_un_last f (c.take q ++ CGate.un u a :: c.drop (q + 1)) hrep
      (by rw [hlen]; exact hmin) hnc q u a
      (splice_getD_self c q (CGate.un u a) hqL) (by omega)
    rw [hlen] at hlast
    omega
  · rintro ⟨u, hu⟩
    have hcomp' : computes (c.take q ++ CGate.bin op a b :: c.drop (q + 1)) f := by
      rw [← hsplit]
      exact hcomp
    have hrep := computes_congr_at (c.take q) (CGate.bin op a b) (CGate.un u b)
      (c.drop (q + 1)) f (by
        intro x
        show op ((runFrom x [] (c.take q)).getD a false)
            ((runFrom x [] (c.take q)).getD b false)
          = u ((runFrom x [] (c.take q)).getD b false)
        exact hu _ _) hcomp'
    have hlen : (c.take q ++ CGate.un u b :: c.drop (q + 1)).length = c.length :=
      splice_length c q (CGate.un u b) hqL
    have hlast := minimal_un_last f (c.take q ++ CGate.un u b :: c.drop (q + 1)) hrep
      (by rw [hlen]; exact hmin) hnc q u b
      (splice_getD_self c q (CGate.un u b) hqL) (by omega)
    rw [hlen] at hlast
    omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.passthrough_mediates
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.minimal_bin_bidependent
