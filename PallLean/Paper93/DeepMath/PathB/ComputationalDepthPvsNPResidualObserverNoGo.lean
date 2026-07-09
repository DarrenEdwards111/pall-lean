import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPResidualObserver

/-!
# Residual observer no-go: SAT prefix truth alone does not force exponential boundary

This file proves the first obstruction to the naive H4-preservation hope.

The previous residual-observer socket showed:

```text
polynomial boundary + full residual distinction + n^k < 2^n ⇒ contradiction.
```

A tempting next claim would be:

```text
SAT self-reduction forces full residual distinction.
```

That claim is false at the semantic-prefix level.  A correct SAT prefix oracle has only a Boolean boundary
(`sat`/`unsat`) and is already enough for the standard bit-by-bit self-reduction.  Thus self-reduction by itself does
not force injectivity over all `2^n` full branches.

This does not kill H4; it refines it.  The observer cannot be mere residual SAT truth.  It must include stronger
algorithmic/search-transcript information, or a fooling-set / many-branch invariant for a restricted family.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserverNoGo

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserver

/-- A prefix oracle viewed as a residual observer with Boolean boundary. -/
def boolPrefixObserver (Q : CNF → RawAssignment → Bool) : ResidualObserver Bool :=
  Q

/-- A correct prefix oracle is residual-truth-sound as a Boolean observer.  Equal oracle answers imply equal residual SAT
truth values. -/
theorem prefix_oracle_truth_sound (Q : CNF → RawAssignment → Bool)
    (hQ : PrefixOracleCorrect Q) :
    ResidualTruthSound (boolPrefixObserver Q) := by
  intro φ p q heq
  constructor
  · intro hp
    have htrueP : Q φ p = true := (hQ φ p).mpr hp
    have heq' : Q φ p = Q φ q := by simpa [boolPrefixObserver] using heq
    have htrueQ : Q φ q = true := by
      simpa [heq'] using htrueP
    exact (hQ φ q).mp htrueQ
  · intro hq
    have htrueQ : Q φ q = true := (hQ φ q).mpr hq
    have heq' : Q φ p = Q φ q := by simpa [boolPrefixObserver] using heq
    have htrueP : Q φ p = true := by
      simpa [heq'] using htrueQ
    exact (hQ φ p).mp htrueP

/-- The Boolean prefix observer has exactly two boundary states. -/
theorem bool_prefix_boundary_card :
    Fintype.card Bool = 2 := by
  simp

/-- Therefore, for any `n,k` with `2 ≤ n^k` and `n^k < 2^n`, the Boolean prefix observer satisfies the polynomial
boundary hypothesis but cannot be fully residual-distinguishing. -/
theorem bool_prefix_observer_poly_but_not_full_distinguishing
    (Q : CNF → RawAssignment → Bool) (φ : CNF) {n k : ℕ}
    (htwo : 2 ≤ n ^ k) (hgap : n ^ k < 2 ^ n) :
    PolyBoundaryAt n k Bool ∧
      ¬ FullResidualDistinguishing (n := n) (boolPrefixObserver Q) φ := by
  have hpoly : PolyBoundaryAt n k Bool := by
    dsimp [PolyBoundaryAt]
    simpa using htwo
  exact ⟨hpoly, poly_boundary_not_full_residual_distinguishing
    (boolPrefixObserver Q) φ hpoly hgap⟩

/-!
Interpretation:

A correct prefix SAT oracle can be truth-sound with only two boundary states.  The classical self-reduction consumes this
Boolean boundary adaptively to construct a witness.  Hence the missing H4 preservation theorem cannot be:

```text
SAT self-reduction ⇒ full residual injectivity of prefix truth states.
```

The next viable target must strengthen the observer from truth values to one of:

1. adaptive transcript/state complexity of a uniform deterministic solver;
2. a fooling-set / many-equivalence-class lower bound for a carefully chosen formula family;
3. proof-complexity or GCT-style non-large obstruction.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserverNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserverNoGo.prefix_oracle_truth_sound
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPResidualObserverNoGo.bool_prefix_observer_poly_but_not_full_distinguishing
