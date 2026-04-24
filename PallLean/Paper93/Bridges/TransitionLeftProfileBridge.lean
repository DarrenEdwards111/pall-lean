/-
  PallLean/Paper93/Bridges/TransitionLeftProfileBridge.lean

  Paper §9 Lemma 31 — semantic bridge from N7's per-type singleton
  matching predicate `ProfileMatchesTransitionLeft` (carrying the M15
  post-span and row-in-post-span bridge hypotheses over an auxiliary
  per-type interface family `W`) to N1's canonical histogram-matching
  predicate `ProfileMatches`.

  Agent Q3 (branch `godmove-paper-faithful`).

  ## Scope

  N7's `ProfileMatchesTransitionLeft` (Agent N7, renamed under Agent P2
  at commit `e695372`) bundles:

    1. Row classification at `transitionLeft`
       (`cookLevinConstraintType M n hn htb hns i = transitionLeft`).
    2. Shift admissibility on the derivative list
       (`shift.vars ⊆ S.toFinset`).
    3. Derivative-list length admissibility
       (`S.length ≤ Nat.log 2 n`).
    4. Singleton concentration on `transitionLeft`
       (`bp.toHistogram τ = 0` for `τ ≠ transitionLeft`,
        `bp.toHistogram transitionLeft = S.length`).
    5. Two M15 bridge hypotheses over the auxiliary per-type family
       `W`:
        * `cookLevinPostSpanAt M n hn htb hns bp.toHistogram ≤
           cookLevinProfileSubspace bp W`,
        * the row-level membership clause for every transitionLeft
          factor index.

  N1's canonical `ProfileMatches` (Agent N1) is the pointwise equality
  `bp.toHistogram = rowProfile M n hn htb hns S shift i`, where
  `rowProfile` is the Kronecker indicator at
  `cookLevinConstraintType M n hn htb hns i`.  Because this indicator
  has total mass `1`, N1's predicate forces the histogram of `bp` to
  satisfy

      bp.toHistogram (cookLevinConstraintType ... i) = 1,
      bp.toHistogram τ                              = 0
          for every other `τ`.

  N7's predicate, in turn, forces

      bp.toHistogram transitionLeft = S.length,
      bp.toHistogram τ              = 0
          for every `τ ≠ transitionLeft`,

  together with `cookLevinConstraintType ... i = transitionLeft`.

  The two predicates therefore agree **on the reachable portion of
  N7's data** precisely when `S.length = 1`, i.e. the derivative list
  is a singleton.  Under this bridge hypothesis, N7's
  `ProfileMatchesTransitionLeft` implies N1's `ProfileMatches`.

  The resulting theorem `N7_implies_N1_transitionLeft` takes all of N7's
  data, together with the singleton bridge hypothesis
  `hSlen : S.length = 1`, and concludes N1's canonical `ProfileMatches`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Matching.ProfileMatches
import PallLean.Paper93.Matching.TransitionLeftAdmissible

namespace PallLean.Paper93.Bridges

open MvPolynomial
open PallLean.Paper93
open PallLean.Paper93.Matching
open SymmetricPowerBound (ConstraintType)
open TuringMachine (DTM)
open WithinProfileBound

/-- **Semantic bridge: N7 ⇒ N1 at a singleton derivative list.**

Given:
  * the Turing-machine parameter tuple `(M, n, hn, htb, hns)`;
  * an admissible derivative list `S : List (Fin n)` and shift
    polynomial `shift : MvPolynomial (Fin n) ℚ`;
  * a factor index `i` of the compiled Cook-Levin factor list;
  * a bounded profile `bp : BoundedProfile (Nat.log 2 n)`;
  * an auxiliary per-type interface family
    `W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)`;
  * the matching hypothesis
    `hmatch : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W`
    from N7; and
  * the singleton bridge hypothesis `hSlen : S.length = 1`,

N7's per-type singleton matching predicate implies N1's canonical
histogram-matching predicate `ProfileMatches`.

**Proof outline.**  Unfold `ProfileMatches` to the pointwise equality
`bp.toHistogram τ = rowProfile ... τ`.  For `τ = transitionLeft`, N7's
mass-length equation combined with `hSlen` gives
`bp.toHistogram transitionLeft = 1`, and `rowProfile ... transitionLeft`
is `1` by N7's row-classification hypothesis.  For every other `τ`,
N7's singleton-concentration clause gives `bp.toHistogram τ = 0`, and
`rowProfile ... τ = 0` because
`cookLevinConstraintType ... i = transitionLeft ≠ τ`.

The auxiliary per-type family `W` and the two M15 bridge hypotheses
carried inside `hmatch` are not consumed by this reduction: they only
enter N7's downstream V_h-embedding statement, not the histogram
equality. -/
theorem N7_implies_N1_transitionLeft
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ)
    (i : Fin (WithinProfileBound.cookLevinFactorList M n hn htb hns).length)
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hmatch : ProfileMatchesTransitionLeft M n hn htb hns S shift i bp W)
    (hSlen : S.length = 1) :
    ProfileMatches M n hn htb hns S shift i bp := by
  -- Unpack the relevant clauses of N7's `ProfileMatchesTransitionLeft`.
  -- N7's predicate is a long iterated conjunction; we destructure it
  -- into named hypotheses so the pointwise equality argument below is
  -- transparent.
  obtain
    ⟨hType, _hShiftVars, _hLenLe,
      hBool, hAdj, hRight, hLeftMass,
      _hPostSpan, _hRowInPostSpan⟩ := hmatch
  -- Reduce `ProfileMatches` to its pointwise form and case on `τ`.
  refine (profileMatches_iff M n hn htb hns S shift i bp).mpr ?_
  intro τ
  -- Evaluate `rowProfile ... τ` via its `if` definition, using the
  -- row-classification hypothesis `hType` to simplify the indicator.
  have hrow : rowProfile M n hn htb hns S shift i τ
              = (if ConstraintType.transitionLeft = τ then (1 : ℕ) else 0) := by
    unfold rowProfile
    -- Rewrite the antecedent using `hType : ... = transitionLeft`.
    rw [hType]
  -- Now the goal is `bp.toHistogram τ = if transitionLeft = τ then 1 else 0`.
  rw [hrow]
  -- Split on the four constraint types and discharge each using the
  -- corresponding clause of `hmatch`.
  cases τ with
  | booleanity =>
    -- `transitionLeft ≠ booleanity`, so the RHS is `0`.
    simp only [reduceCtorEq, if_false]
    exact hBool
  | adjacency =>
    -- `transitionLeft ≠ adjacency`, so the RHS is `0`.
    simp only [reduceCtorEq, if_false]
    exact hAdj
  | transitionLeft =>
    -- `transitionLeft = transitionLeft`, so the RHS is `1`.
    -- N7 gives `bp.toHistogram transitionLeft = S.length`; combined
    -- with `hSlen : S.length = 1` this yields the required `1`.
    simp only [if_true]
    rw [hLeftMass, hSlen]
  | transitionRight =>
    -- `transitionLeft ≠ transitionRight`, so the RHS is `0`.
    simp only [reduceCtorEq, if_false]
    exact hRight

/-! ## Kernel-only axiom trace

The semantic bridge above depends only on N7's `ProfileMatchesTransitionLeft`
accessors, N1's `profileMatches_iff` unfolding lemma, the definition
of `rowProfile`, and basic `if`/`cases` reasoning on the four-element
`ConstraintType`.  No bespoke axiom is introduced. -/

#print axioms N7_implies_N1_transitionLeft

end PallLean.Paper93.Bridges
