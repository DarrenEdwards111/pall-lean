import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSuperAdditiveKills

/-!
# Settling the head-as-data obstruction

Step 4 left one question: can a SAT decider have polynomially many distinct tape snapshots with
superpolynomially many head positions — using head position as data without writing to the tape?
This file settles it at the level of mathematics and records the exact formalization boundary.

## The obstruction resolves — and it kills `distinctRows` either way

The obstruction is precisely the implication `poly distinctTapes ⟹ poly time`.  Both possible
answers eliminate `distinctRows` as a *useful* proxy:

* **If the obstruction holds** (no superpolynomial-time machine has polynomial distinct-tape count):
  then, since `distinctTapes ≤ time` always, `distinctTapes` is **polynomially equivalent to time**.
  A `distinctRows` lower bound then says nothing a time lower bound does not — it is *content-free*,
  equivalent to the separation itself, with no structural handle beyond time.
* **If the obstruction fails** (some superpolynomial-time machine has polynomial distinct-tape
  count): then, since SAT is polynomial-space (`traceRank`'s killer), there is a SAT decider with
  polynomial `distinctRows`, so `distinctRows` is **not SAT-hard** — it is outright killed, like
  rank.

So `distinctRows` is not viable in either branch.  The formal anchor below records the "sufficient"
direction that always holds; the branch analysis is honest prose, and the deciding lemma is stated
but not formalized (see the boundary note).

## The formalization boundary

The obstruction is the classical **"no computation in empty space"** fact: to reach head position
`H` a halting machine needs a non-blank landmark in every `|State|`-window of `[|x|, H]` (it cannot
traverse more than `|State|` consecutive blank cells while halting — a pigeonhole on states forces a
non-halting drift or loop), and each new rightmost landmark is a distinct tape.  Hence
`H ≤ |x| + |State|·distinctTapes`, giving `time ≤ poly(distinctTapes, |x|)` via the structural bound
— i.e. the obstruction *holds*.  This is a Hennie-machine-style crossing-sequence argument; I was
**not** able to formalize the blank-traversal liveness step cleanly in this session, so the
settlement here is at the level of mathematical argument, not a machine-checked proof of the
implication.  What is machine-checked is the sufficiency direction and the size-domination.

## Verdict

`distinctRows` is dual to tableau rank: **rank ≤ space is too weak** (space-cheap SAT killed it);
**distinctRows ≈ time is too strong** (content-free) if the obstruction holds, or killed if it
fails.  A viable proxy must sit *strictly between* space and time — which is exactly the hard
regime this whole line keeps returning to.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsObstruction

open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics (NPObs PolyCollapse)
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge (InvHard)
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceSchemaCeiling (sizeDominated_hard_iff_sep)
open PallLean.Paper93.DeepMath.PathB.SuperAdditiveNarrow (rows_le_traceSize)
open PallLean.Paper93.DeepMath.PathB.SuperAdditiveKills (distinctRows)

/-- `distinctRows` is size-dominated: the number of distinct configurations is at most the trace
size (the cash-out side — the *desirable* property). -/
theorem distinctRows_sizeDominated : SizeDominated distinctRows :=
  fun tr => (List.Sublist.length_le (List.dedup_sublist tr)).trans (rows_le_traceSize tr)

/-- **The sufficiency direction (always holds).**  A `distinctRows` lower bound on all SAT deciders
implies the separation: since `distinctRows` is size-dominated, its hardness plugs into the
completeness result.  So proving `distinctRows` hard is *no easier* than the separation — it implies
it.  (The converse — that the separation implies `distinctRows` hardness — is the obstruction, whose
resolution makes the two equivalent; see the module note.) -/
theorem distinctRows_hard_imp_sep (SATV : NPObs) (hH : InvHard SATV (traceInv distinctRows)) :
    ¬ PolyCollapse SATV :=
  (sizeDominated_hard_iff_sep SATV).mp ⟨distinctRows, distinctRows_sizeDominated, hH⟩

/-- **The obstruction, named.**  `poly distinctTapes ⟹ poly time`: no machine runs superpolynomially
long with only polynomially many distinct tape snapshots.  Believed true (the "no computation in
empty space" argument), which would make `distinctRows` polynomially equivalent to time and hence
content-free; not machine-checked here. -/
def NoEmptySpaceComputation : Prop :=
  ∀ (M : ComposableMachine.Machine) (p : ℕ → ℕ),
    (∀ x T, M.halt (ComposableMachine.run M T (ComposableMachine.init M x)).st = true →
        (∀ k, k < T → M.halt (ComposableMachine.run M k (ComposableMachine.init M x)).st = false) →
        distinctRows (traceObj M T x) ≤ p x.length) →
    ∃ q : ℕ → ℕ, ∀ x T, M.halt (ComposableMachine.run M T (ComposableMachine.init M x)).st = true →
      (∀ k, k < T → M.halt (ComposableMachine.run M k (ComposableMachine.init M x)).st = false) →
      T ≤ q x.length

end PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsObstruction
