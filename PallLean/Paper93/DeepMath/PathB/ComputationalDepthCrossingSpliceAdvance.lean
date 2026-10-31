import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingResetFree

/-!
# The three-way splice advance (reset-free)

With the reset-free geometry (`leftward_lands_at_b`), the `SpliceSynced` invariant advances across a
phase.  This file proves the **right-phase advance** — the inductive step over a right excursion.

`splice_advance_right`: from `SpliceSynced z xL xR` at a rightward crossing (all at head `b+1`), run
the right phase — `z` tracks `x_R` on the right (lockstep, `splice_track_right`) with its left tape
frozen; `x_L` runs its *own* right phase with its left tape frozen (`run_left_frozen`).  All three land
at `b` (`leftward_lands_at_b`); the crossing-sequence hypothesis `state(run e xL) = state(run d xR)`
supplies the state agreement.  The result is `SpliceSynced` again at the next (leftward) crossing:
`z`'s left tape still equals `x_L`'s (both frozen from their equal entry values) and its right tape
still equals `x_R`'s (lockstep).

This is the heart of the splice induction: it composes `splice_track_right`, `run_left_frozen`, and the
reset-free landing into one three-way cycle.  The symmetric left-phase advance, the alternating
top-level induction, the concrete palindrome family, and the `Ω(n)`-cut summation remain; this file
does **not** claim the `Ω(n²)` bound (a restricted result: `crossingCount ≤ time` caps the technique
at polynomial, one-tape P `=` P, not `SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Right-phase splice advance.**  From `SpliceSynced` at a rightward crossing, after the right
phases (`z`/`x_R` lockstep of length `d`, `x_L`'s own of length `e`), `SpliceSynced` holds again at the
next crossing — given the reset-free geometry and that `x_L`'s and `x_R`'s leftward-crossing states
agree. -/
theorem splice_advance_right (M : Machine) (hrf : ResetFree M) (b : ℕ) (z xL xR : Cfg M) (d e : ℕ)
    (hsync : SpliceSynced M b z xL xR)
    (hz_entry : z.hd = b + 1)
    (hz_phase : ∀ j, j < d → b < (run M j z).hd) (hz_exit : (run M d z).hd ≤ b)
    (hxL_phase : ∀ j, j < e → b < (run M j xL).hd) (hxL_exit : (run M e xL).hd ≤ b)
    (hstate : (run M e xL).st = (run M d xR).st) :
    SpliceSynced M b (run M d z) (run M e xL) (run M d xR) := by
  obtain ⟨_, hst_zR, hhd_zL, hhd_zR, hleft, hright⟩ := hsync
  have hxL_entry : xL.hd = b + 1 := by rw [← hhd_zL, hz_entry]
  obtain ⟨htr_st, htr_hd, htr_right, htr_leftfroz⟩ :=
    splice_track_right M b z xR d hst_zR hhd_zR hright hz_phase
  have hxL_leftfroz : ∀ p, p ≤ b → (run M e xL).tp.getD p false = xL.tp.getD p false :=
    fun p hp => run_left_frozen M b xL e hxL_phase p hp
  have hz_land : (run M d z).hd = b := by
    have hpos : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h0 | hp
      · rw [h0, run_zero, hz_entry] at hz_exit; omega
      · exact hp
    have hprev : b < (run M (d - 1) z).hd := hz_phase (d - 1) (by omega)
    have hstep : run M d z = step M (run M (d - 1) z) := by
      conv_lhs => rw [show d = (d - 1) + 1 by omega, run_succ]
    rw [hstep] at hz_exit ⊢
    exact leftward_lands_at_b M hrf b (run M (d - 1) z) hprev hz_exit
  have hxL_land : (run M e xL).hd = b := by
    have hpos : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | hp
      · rw [h0, run_zero, hxL_entry] at hxL_exit; omega
      · exact hp
    have hprev : b < (run M (e - 1) xL).hd := hxL_phase (e - 1) (by omega)
    have hstep : run M e xL = step M (run M (e - 1) xL) := by
      conv_lhs => rw [show e = (e - 1) + 1 by omega, run_succ]
    rw [hstep] at hxL_exit ⊢
    exact leftward_lands_at_b M hrf b (run M (e - 1) xL) hprev hxL_exit
  refine ⟨htr_st.trans hstate.symm, htr_st, hz_land.trans hxL_land.symm, htr_hd, ?_, htr_right⟩
  intro p hp
  rw [htr_leftfroz p hp, hleft p hp, ← hxL_leftfroz p hp]

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
