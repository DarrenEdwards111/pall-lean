import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpliceRecursive

/-!
# The initial left excursion of the splice

Establishes the base case `γ 0` for `splice_recursive`: from `SpliceSynced` at the *start* (head `0`,
or any head `≤ b`), the initial left excursion reaches the first rightward crossing with `SpliceSynced`
and head `b+1`.  This is a left-phase advance from head `≤ b` (the machine starts at head `0`), proved
self-contained from the run-level lemmas (mirroring `splice_advance_left`, which required head exactly
`b`).

* `splice_initial` — from `SpliceSynced z xL xR` with `z.hd ≤ b`, and `z`/`x_R` rightward-crossing,
  `nextSplice (z,xL,xR)` is `SpliceSynced` and at head `b+1` — i.e. `γ 0 = nextSplice (start)`.

With `splice_initial` (base case) and `splice_recursive` (step), the mixed computation is `SpliceSynced`
at every crossing from the start, given the shared crossing sequence.

## What still remains (NOT here)

The concrete palindrome family (furnishing the `SpliceData`/state agreements from `C(xL) = C(xR)` and
the acceptance contradiction) and the `Ω(n)`-cut summation.  This file does **not** claim the `Ω(n²)`
bound (restricted: `crossingCount ≤ time` caps the technique at polynomial, one-tape P `=` P, not
`SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Initial left excursion (base case).**  From `SpliceSynced` at head `≤ b`, the first left
excursion reaches the first rightward crossing (`nextSplice`) `SpliceSynced` and at head `b+1`. -/
theorem splice_initial (M : Machine) (b : ℕ) (z xL xR : Cfg M)
    (hsync : SpliceSynced M b z xL xR) (hz_start : z.hd ≤ b)
    (hz_re : ∃ t, b < (run M t z).hd) (hxR_re : ∃ t, b < (run M t xR).hd)
    (hstate : (run M (firstEntryTime M b z) xL).st = (run M (firstEntryTime M b xR) xR).st) :
    SpliceSynced M b (nextSplice M b (z, xL, xR)).1 (nextSplice M b (z, xL, xR)).2.1
        (nextSplice M b (z, xL, xR)).2.2
      ∧ (nextSplice M b (z, xL, xR)).1.hd = b + 1 := by
  have hne : ¬ (z.hd = b + 1) := by omega
  have hnext : nextSplice M b (z, xL, xR) =
      (run M (firstEntryTime M b z) z, run M (firstEntryTime M b z) xL,
        run M (firstEntryTime M b xR) xR) := by
    unfold nextSplice; rw [if_neg hne]
  rw [hnext]
  obtain ⟨hst_zL, _, hhd_zL, hhd_zR, hleft, hright⟩ := hsync
  have hxR_start : xR.hd ≤ b := by rw [← hhd_zR]; exact hz_start
  obtain ⟨hzp, hze⟩ := firstEntryTime_spec M b z hz_re
  obtain ⟨hxp, hxe⟩ := firstEntryTime_spec M b xR hxR_re
  obtain ⟨htr_st, htr_hd, htr_left, htr_rightfroz⟩ :=
    splice_track_left M b z xL (firstEntryTime M b z) hst_zL hhd_zL hleft hzp
  have hxR_rightfroz : ∀ p, b < p →
      (run M (firstEntryTime M b xR) xR).tp.getD p false = xR.tp.getD p false :=
    fun p hp => run_right_frozen M b xR (firstEntryTime M b xR) hxp p hp
  have hz_land : (run M (firstEntryTime M b z) z).hd = b + 1 := by
    have hpos : 1 ≤ firstEntryTime M b z := by
      rcases Nat.eq_zero_or_pos (firstEntryTime M b z) with h0 | hp
      · rw [h0, run_zero] at hze; omega
      · exact hp
    have hprev : (run M (firstEntryTime M b z - 1) z).hd ≤ b := hzp _ (by omega)
    have hstep : run M (firstEntryTime M b z) z = step M (run M (firstEntryTime M b z - 1) z) := by
      conv_lhs => rw [show firstEntryTime M b z = (firstEntryTime M b z - 1) + 1 by omega, run_succ]
    rw [hstep] at hze ⊢
    exact step_entry_head M b _ hprev hze
  have hxR_land : (run M (firstEntryTime M b xR) xR).hd = b + 1 := by
    have hpos : 1 ≤ firstEntryTime M b xR := by
      rcases Nat.eq_zero_or_pos (firstEntryTime M b xR) with h0 | hp
      · rw [h0, run_zero] at hxe; omega
      · exact hp
    have hprev : (run M (firstEntryTime M b xR - 1) xR).hd ≤ b := hxp _ (by omega)
    have hstep : run M (firstEntryTime M b xR) xR = step M (run M (firstEntryTime M b xR - 1) xR) := by
      conv_lhs => rw [show firstEntryTime M b xR = (firstEntryTime M b xR - 1) + 1 by omega, run_succ]
    rw [hstep] at hxe ⊢
    exact step_entry_head M b _ hprev hxe
  exact ⟨⟨htr_st, htr_st.trans hstate, htr_hd, hz_land.trans hxR_land.symm, htr_left,
    fun p hp => by rw [htr_rightfroz p hp, hright p hp, ← hxR_rightfroz p hp]⟩, hz_land⟩

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
