import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpliceExtract

/-!
# The recursive `γ` map for the splice

Defines the next-crossing-config map `nextSplice` and shows that one `nextSplice` step yields a
`SpliceStep`, dispatched by the mixed computation's head: a right phase at a rightward crossing (head
`b+1`), a left phase at a leftward crossing (head `b`).  These are the building blocks of the recursive
`γ` (`γ k = nextSplice^[k] (γ 0)`) that instantiates `splice_iterate`.

* `nextSplice` — advances the triple `(z, xL, xR)` by one phase: to `z`'s (and `xL`'s / `xR`'s) first
  exit (if `z` is at head `b+1`) or first re-entry (otherwise).
* `splice_step_right_of_next` — at head `b+1`, `nextSplice` realizes a right-phase `SpliceStep`.
* `splice_step_left_of_next` — at head `b`, `nextSplice` realizes a left-phase `SpliceStep`.

## What still remains (NOT here)

The recursion proper — `γ k = nextSplice^[k] (γ 0)` with the head-parity invariant (`γ k` at head `b+1`
for even `k`, `b` for odd `k`, from the phase landings), crossing existence threaded, and the
crossing-sequence hypothesis `C(xL) = C(xR)` supplying each step's state agreement — then `splice_iterate`,
the initial left excursion (head `0` to the first rightward crossing), the concrete palindrome family,
and the `Ω(n)`-cut summation.  This file does **not** claim the `Ω(n²)` bound (restricted:
`crossingCount ≤ time` caps the technique at polynomial, one-tape P `=` P, not `SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- Advance a crossing-config triple by one phase: right phase (to first exits) if `z` is at a
rightward crossing (head `b+1`), else left phase (to first re-entries). -/
noncomputable def nextSplice (M : Machine) (b : ℕ) (t : Cfg M × Cfg M × Cfg M) :
    Cfg M × Cfg M × Cfg M :=
  if t.1.hd = b + 1 then
    (run M (firstExitTime M b t.1) t.1, run M (firstExitTime M b t.2.1) t.2.1,
      run M (firstExitTime M b t.1) t.2.2)
  else
    (run M (firstEntryTime M b t.1) t.1, run M (firstEntryTime M b t.1) t.2.1,
      run M (firstEntryTime M b t.2.2) t.2.2)

/-- At a rightward crossing, `nextSplice` realizes a right-phase `SpliceStep`. -/
theorem splice_step_right_of_next (M : Machine) (b : ℕ) (z xL xR : Cfg M)
    (hz_entry : z.hd = b + 1)
    (hz_exit : ∃ t, (run M t z).hd ≤ b) (hxL_exit : ∃ t, (run M t xL).hd ≤ b)
    (hstate : (run M (firstExitTime M b xL) xL).st = (run M (firstExitTime M b z) xR).st) :
    SpliceStep M b z xL xR (nextSplice M b (z, xL, xR)).1 (nextSplice M b (z, xL, xR)).2.1
      (nextSplice M b (z, xL, xR)).2.2 := by
  have hnext : nextSplice M b (z, xL, xR) =
      (run M (firstExitTime M b z) z, run M (firstExitTime M b xL) xL,
        run M (firstExitTime M b z) xR) := by
    unfold nextSplice; rw [if_pos hz_entry]
  rw [hnext]
  exact extract_splice_step_right M b z xL xR hz_entry hz_exit hxL_exit hstate

/-- At a leftward crossing, `nextSplice` realizes a left-phase `SpliceStep`. -/
theorem splice_step_left_of_next (M : Machine) (b : ℕ) (z xL xR : Cfg M)
    (hz_entry : z.hd = b)
    (hz_reentry : ∃ t, b < (run M t z).hd) (hxR_reentry : ∃ t, b < (run M t xR).hd)
    (hstate : (run M (firstEntryTime M b z) xL).st = (run M (firstEntryTime M b xR) xR).st) :
    SpliceStep M b z xL xR (nextSplice M b (z, xL, xR)).1 (nextSplice M b (z, xL, xR)).2.1
      (nextSplice M b (z, xL, xR)).2.2 := by
  have hne : ¬ (z.hd = b + 1) := by omega
  have hnext : nextSplice M b (z, xL, xR) =
      (run M (firstEntryTime M b z) z, run M (firstEntryTime M b z) xL,
        run M (firstEntryTime M b xR) xR) := by
    unfold nextSplice; rw [if_neg hne]
  rw [hnext]
  exact extract_splice_step_left M b z xL xR hz_entry hz_reentry hxR_reentry hstate

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
