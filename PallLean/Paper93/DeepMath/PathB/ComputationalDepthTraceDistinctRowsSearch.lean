import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceDistinctRows

/-!
# Attacking step 3: the search for a low-`distinctRows` SAT decider

Falsification-first: does a SAT decider exist whose runs have only polynomially many distinct tape
snapshots?  If so, `distinctRows` dies like rank did.

The structural bound `time + 1 ≤ |State| · #headPositions · distinctTapes` (`TraceDistinctRows`)
determines exactly where such a decider could live.  Specialized and made monotone
(`time_bounded_of_resources`): if a run visits `≤ H` head positions and `≤ D` distinct tapes, its
halt time is `≤ |State| · H · D`.  So **bounded diversity forces bounded time**
(`poly_resources_imp_poly_time`): a decider whose head count *and* distinct-tape count are both
polynomially bounded runs in polynomial time.

**The search outcome.**  This kills the *natural* route — the one that killed rank.  Rank died
because `rank ≤ space` and SAT is space-cheap; the obvious next attempt is a *space-cheap*
(poly-head-range) decider with few distinct tapes.  But `poly_resources_imp_poly_time` shows a
poly-head-range, poly-`distinctRows` SAT decider would run in polynomial time — i.e. would put
`SAT ∈ P`.  So **no such decider exists unless `P = NP`**: the poly-space regime, where rank was
killed, is barren for `distinctRows`.

A low-`distinctRows` SAT decider would therefore need **superpolynomially many head positions**
(superpolynomial space) with only polynomially many distinct tape contents — a machine whose tape
is superpolynomially wide yet takes few distinct values.  The obstruction to building one is that
using the head position as *data* (to evaluate the formula on the assignment it encodes) seems to
require writing to the tape, which manufactures distinct rows.  Whether that obstruction is real is
the genuine open question; **the search found no kill**, and — unlike rank — `distinctRows`
survives its most dangerous regime.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  In particular this file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsSearch

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.TraceDistinctRows

variable {M : Machine}

/-- The number of distinct head positions in the run to time `T`. -/
noncomputable def headCount (M : Machine) (x : List Bool) (T : ℕ) : ℕ :=
  ((visitedConfigs (init M x) T).image (fun d => d.hd)).card

/-- The number of distinct tape snapshots (the trace's distinct-row count) to time `T`. -/
noncomputable def distinctTapes (M : Machine) (x : List Bool) (T : ℕ) : ℕ :=
  ((visitedConfigs (init M x) T).image (fun d => d.tp)).card

/-- The structural bound, specialized to a computation from the initial configuration. -/
theorem time_le' (x : List Bool) {T : ℕ}
    (hhalt : M.halt (run M T (init M x)).st = true)
    (hpre : ∀ k, k < T → M.halt (run M k (init M x)).st = false) :
    T + 1 ≤ Fintype.card M.State * headCount M x T * distinctTapes M x T :=
  time_le (init M x) hhalt hpre

/-- **Bounded diversity forces bounded time.**  A run visiting `≤ H` head positions and `≤ D`
distinct tapes halts by time `|State| · H · D`. -/
theorem time_bounded_of_resources (x : List Bool) {T H D : ℕ}
    (hhalt : M.halt (run M T (init M x)).st = true)
    (hpre : ∀ k, k < T → M.halt (run M k (init M x)).st = false)
    (hH : headCount M x T ≤ H) (hD : distinctTapes M x T ≤ D) :
    T + 1 ≤ Fintype.card M.State * H * D := by
  calc T + 1 ≤ Fintype.card M.State * headCount M x T * distinctTapes M x T :=
        time_le' x hhalt hpre
    _ ≤ Fintype.card M.State * H * D := by gcongr

/-- **Polynomial diversity implies polynomial time.**  If, on every input, a machine's head count
and distinct-tape count are both bounded by `p(|x|)`, then its halt time is bounded by
`|State| · p(|x|)²` — polynomial.  Hence a poly-head-range, poly-`distinctRows` decider is
poly-time; a SAT decider of that kind would put `SAT ∈ P`.  The poly-space regime (where tableau
rank was killed) admits **no** low-`distinctRows` SAT decider unless `P = NP`. -/
theorem poly_resources_imp_poly_time (M : Machine) (p : ℕ → ℕ)
    (hp : ∀ (x : List Bool) (T : ℕ), M.halt (run M T (init M x)).st = true →
        (∀ k, k < T → M.halt (run M k (init M x)).st = false) →
        headCount M x T ≤ p x.length ∧ distinctTapes M x T ≤ p x.length) :
    ∀ (x : List Bool) (T : ℕ), M.halt (run M T (init M x)).st = true →
      (∀ k, k < T → M.halt (run M k (init M x)).st = false) →
      T + 1 ≤ Fintype.card M.State * p x.length * p x.length := by
  intro x T hhalt hpre
  obtain ⟨hH, hD⟩ := hp x T hhalt hpre
  exact time_bounded_of_resources x hhalt hpre hH hD

end PallLean.Paper93.DeepMath.PathB.TraceDistinctRowsSearch
