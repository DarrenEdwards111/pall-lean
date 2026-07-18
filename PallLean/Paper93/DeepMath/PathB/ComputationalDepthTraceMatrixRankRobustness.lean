import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceMatrixRank

/-!
# Robustness of the tableau-rank proxy: the falsification

Falsification-first: having defined `traceRank` and its cash-out (domination) side, we now try hard
to **destroy** it — to find a low-rank simulation of SAT that would make its hard side false.

The search succeeds immediately, from one structural fact already in hand:

> `traceRank tr ≤ rowMax tr`  — **tableau rank is bounded by space** (`TraceMatrixRank`).

So *any* space-efficient computation has low rank, regardless of running time.  Concretely, the
brute-force SAT decider that enumerates assignments with an `O(n)`-bit counter uses linear space,
hence has polynomially-bounded tableau rank on all inputs — even though its running time is
exponential.  Its low rank is the "low-rank simulation" the search was looking for.

Formally:

* `traceInv_mono` / `invHard_mono` — hardness lifts along pointwise domination of measures.
* `polyBounded_traceRank_of_polyBounded_rowMax` — **low space ⟹ low rank**: a machine with
  polynomially-bounded `rowMax` (space) has polynomially-bounded `traceRank`.
* `traceRank_not_hard` — **THE KILL**: under `SATPolySpace` (SAT has a polynomial-space decider,
  which it does — `SAT ∈ NP ⊆ PSPACE`, indeed linear space), `traceRank` is **not** SAT-hard.  The
  candidate is falsified: it cannot force superpolynomial time, because it does not even force
  superpolynomial space, and SAT is space-cheap.

**Conclusion of the falsification pass:** the tableau-rank proxy is a *space* measure, not a time
measure, so it is the wrong proxy for a time lower bound.  Per the program, we do **not** proceed
to its SAT-hardness side; it is dead.  (A time-sensitive proxy would have to be *un*bounded by
space — e.g. a measure of the number of distinct configurations, which `distinctRows` shows is
itself capped, or genuinely time-structural correlation.)

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceMatrixRankRobustness

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics (NPObs)
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge (InvHard polyBounded_of_le)
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceSpaceKill (rowMax SATPolySpace rowMax_not_hard)
open PallLean.Paper93.DeepMath.PathB.TraceMatrixRank (traceRank traceRank_le_rowMax)

/-- Hardness of a smaller measure lifts through the per-length supremum. -/
theorem traceInv_mono (μ ν : List (List Bool) → ℕ) (hle : ∀ tr, μ tr ≤ ν tr)
    (M : Machine) (n : ℕ) : traceInv μ M n ≤ traceInv ν M n := by
  unfold traceInv
  apply Finset.sup_le
  intro v _
  exact le_trans (hle _)
    (Finset.le_sup (f := fun v => ν (traceObj M (minHalt M n) (List.ofFn v))) (Finset.mem_univ v))

/-- **Hardness is monotone**: if `μ ≤ ν` pointwise and `μ` is SAT-hard, so is `ν`. -/
theorem invHard_mono (SATV : NPObs) (μ ν : List (List Bool) → ℕ) (hle : ∀ tr, μ tr ≤ ν tr)
    (hH : InvHard SATV (traceInv μ)) : InvHard SATV (traceInv ν) := by
  intro M T hD hPB
  exact hH M T hD (polyBounded_of_le (fun n => traceInv_mono μ ν hle M n) hPB)

/-- **Low space ⟹ low rank.**  A machine with polynomially-bounded space (`rowMax`) has
polynomially-bounded tableau rank — the low-rank "simulation" collapsing the measure. -/
theorem polyBounded_traceRank_of_polyBounded_rowMax (M : Machine)
    (h : PvsNPSeparatingInvariant.PolyBounded (traceInv rowMax M)) :
    PvsNPSeparatingInvariant.PolyBounded (traceInv traceRank M) :=
  polyBounded_of_le (fun n => traceInv_mono traceRank rowMax traceRank_le_rowMax M n) h

/-- **THE FALSIFICATION.**  Under `SATPolySpace` — SAT has a polynomial-space decider (it does:
`SAT ∈ NP ⊆ PSPACE`, indeed linear space) — the tableau-rank measure is **not** SAT-hard.  A
space-efficient SAT decider has polynomially-bounded tableau rank, since `traceRank ≤ rowMax`
(rank ≤ width = space).  The proxy is a space measure and cannot force superpolynomial time; it is
dead. -/
theorem traceRank_not_hard (SATV : NPObs) (h : SATPolySpace SATV) :
    ¬ InvHard SATV (traceInv traceRank) := fun hH =>
  rowMax_not_hard SATV h (invHard_mono SATV traceRank rowMax traceRank_le_rowMax hH)

end PallLean.Paper93.DeepMath.PathB.TraceMatrixRankRobustness
