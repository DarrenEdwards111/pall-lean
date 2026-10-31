import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpliceAdvance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingChaining

/-!
# The three-way splice advance — left phase (mirror of the right phase)

The symmetric partner of `splice_advance_right`.  From `SpliceSynced` at a leftward crossing (all at
head `b`), run the left phases — `z` tracks `x_L` on the left (lockstep, `splice_track_left`) with its
right tape frozen; `x_R` runs its *own* left phase with its right tape frozen (`run_right_frozen`).  All
three land at `b+1` (`step_entry_head`; rightward crossings need no reset-freeness — only a right-move
enters the right region); the crossing-sequence hypothesis `state(run d xL) = state(run e xR)` supplies
the state agreement.  `SpliceSynced` holds again at the next (rightward) crossing.

With `splice_advance_right` and `splice_advance_left`, both phases preserve `SpliceSynced`.  The
alternating top-level induction over the crossing index, the concrete palindrome family, and the
`Ω(n)`-cut summation remain; this file does **not** claim the `Ω(n²)` bound (restricted:
`crossingCount ≤ time` caps the technique at polynomial, one-tape P `=` P, not `SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Left-phase splice advance.**  From `SpliceSynced` at a leftward crossing, after the left phases
(`z`/`x_L` lockstep of length `d`, `x_R`'s own of length `e`), `SpliceSynced` holds again at the next
crossing — given that `x_L`'s and `x_R`'s rightward-crossing states agree. -/
theorem splice_advance_left (M : Machine) (b : ℕ) (z xL xR : Cfg M) (d e : ℕ)
    (hsync : SpliceSynced M b z xL xR)
    (hz_entry : z.hd = b)
    (hz_phase : ∀ j, j < d → (run M j z).hd ≤ b) (hz_exit : b < (run M d z).hd)
    (hxR_phase : ∀ j, j < e → (run M j xR).hd ≤ b) (hxR_exit : b < (run M e xR).hd)
    (hstate : (run M d xL).st = (run M e xR).st) :
    SpliceSynced M b (run M d z) (run M d xL) (run M e xR) := by
  obtain ⟨hst_zL, _, hhd_zL, hhd_zR, hleft, hright⟩ := hsync
  have hxR_entry : xR.hd = b := by rw [← hhd_zR, hz_entry]
  obtain ⟨htr_st, htr_hd, htr_left, htr_rightfroz⟩ :=
    splice_track_left M b z xL d hst_zL hhd_zL hleft hz_phase
  have hxR_rightfroz : ∀ p, b < p → (run M e xR).tp.getD p false = xR.tp.getD p false :=
    fun p hp => run_right_frozen M b xR e hxR_phase p hp
  have hz_land : (run M d z).hd = b + 1 := by
    have hpos : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h0 | hp
      · rw [h0, run_zero, hz_entry] at hz_exit; omega
      · exact hp
    have hprev : (run M (d - 1) z).hd ≤ b := hz_phase (d - 1) (by omega)
    have hstep : run M d z = step M (run M (d - 1) z) := by
      conv_lhs => rw [show d = (d - 1) + 1 by omega, run_succ]
    rw [hstep] at hz_exit ⊢
    exact step_entry_head M b (run M (d - 1) z) hprev hz_exit
  have hxR_land : (run M e xR).hd = b + 1 := by
    have hpos : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | hp
      · rw [h0, run_zero, hxR_entry] at hxR_exit; omega
      · exact hp
    have hprev : (run M (e - 1) xR).hd ≤ b := hxR_phase (e - 1) (by omega)
    have hstep : run M e xR = step M (run M (e - 1) xR) := by
      conv_lhs => rw [show e = (e - 1) + 1 by omega, run_succ]
    rw [hstep] at hxR_exit ⊢
    exact step_entry_head M b (run M (e - 1) xR) hprev hxR_exit
  refine ⟨htr_st, htr_st.trans hstate, htr_hd, hz_land.trans hxR_land.symm, htr_left, ?_⟩
  intro p hp
  rw [htr_rightfroz p hp, hright p hp, ← hxR_rightfroz p hp]

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
