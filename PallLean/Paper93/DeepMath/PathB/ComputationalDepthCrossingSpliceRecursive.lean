import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpliceGamma

/-!
# The head-parity splice recursion

Iterates `nextSplice` into the full splice: two computations sharing a crossing sequence keep the
mixed computation `z` spliced at every crossing.  The crux is the **head parity** — `nextSplice` flips
the head between `b+1` (rightward crossing) and `b` (leftward crossing) — which lets the recursion
dispatch the right/left phase step and thread `SpliceSynced`.

* `nextSplice_head_right` — at head `b+1`, `nextSplice`'s new head is `b` (`leftward_lands_at_b`).
* `nextSplice_head_left` — at head `b`, `nextSplice`'s new head is `b+1` (`step_entry_head`).
* `SpliceData` — the per-step data (conditional on the head): crossing existence and the matching
  crossing-sequence state agreement, for whichever phase applies.
* `splice_recursive` — **the recursion.**  From `SpliceSynced` at a rightward crossing (`γ 0` at head
  `b+1`) with `SpliceData` at each step, `SpliceSynced` holds at `γ k = nextSplice^[k] (γ 0)`, with the
  head at `b+1` or `b`.

So the mixed computation is provably spliced at every crossing, given the shared crossing sequence.

## What still remains (NOT here)

The initial left excursion (head `0` to `γ 0` at the first rightward crossing), the concrete palindrome
family (which furnishes the `SpliceData` state agreements from `C(xL) = C(xR)` and the acceptance
contradiction), and the `Ω(n)`-cut summation.  This file does **not** claim the `Ω(n²)` bound
(restricted: `crossingCount ≤ time` caps the technique at polynomial, one-tape P `=` P, not `SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- At a rightward crossing, `nextSplice`'s new head is `b` (a leftward crossing lands at `b`). -/
theorem nextSplice_head_right (M : Machine) (hrf : ResetFree M) (b : ℕ) (z xL xR : Cfg M)
    (hz_entry : z.hd = b + 1) (hz_exit : ∃ t, (run M t z).hd ≤ b) :
    (nextSplice M b (z, xL, xR)).1.hd = b := by
  have hnext : (nextSplice M b (z, xL, xR)).1 = run M (firstExitTime M b z) z := by
    unfold nextSplice; rw [if_pos hz_entry]
  rw [hnext]
  obtain ⟨hbefore, hexit⟩ := firstExitTime_spec M b z hz_exit
  have hpos : 1 ≤ firstExitTime M b z := by
    rcases Nat.eq_zero_or_pos (firstExitTime M b z) with h0 | hp
    · rw [h0, run_zero, hz_entry] at hexit; omega
    · exact hp
  have hprev : b < (run M (firstExitTime M b z - 1) z).hd := hbefore _ (by omega)
  have hstep : run M (firstExitTime M b z) z = step M (run M (firstExitTime M b z - 1) z) := by
    conv_lhs => rw [show firstExitTime M b z = (firstExitTime M b z - 1) + 1 by omega, run_succ]
  rw [hstep] at hexit ⊢
  exact leftward_lands_at_b M hrf b _ hprev hexit

/-- At a leftward crossing, `nextSplice`'s new head is `b+1` (a rightward crossing lands at `b+1`). -/
theorem nextSplice_head_left (M : Machine) (b : ℕ) (z xL xR : Cfg M)
    (hz_entry : z.hd = b) (hz_reentry : ∃ t, b < (run M t z).hd) :
    (nextSplice M b (z, xL, xR)).1.hd = b + 1 := by
  have hne : ¬ (z.hd = b + 1) := by omega
  have hnext : (nextSplice M b (z, xL, xR)).1 = run M (firstEntryTime M b z) z := by
    unfold nextSplice; rw [if_neg hne]
  rw [hnext]
  obtain ⟨hbefore, hentry⟩ := firstEntryTime_spec M b z hz_reentry
  have hpos : 1 ≤ firstEntryTime M b z := by
    rcases Nat.eq_zero_or_pos (firstEntryTime M b z) with h0 | hp
    · rw [h0, run_zero, hz_entry] at hentry; omega
    · exact hp
  have hprev : (run M (firstEntryTime M b z - 1) z).hd ≤ b := hbefore _ (by omega)
  have hstep : run M (firstEntryTime M b z) z = step M (run M (firstEntryTime M b z - 1) z) := by
    conv_lhs => rw [show firstEntryTime M b z = (firstEntryTime M b z - 1) + 1 by omega, run_succ]
  rw [hstep] at hentry ⊢
  exact step_entry_head M b _ hprev hentry

/-- The per-step splice data, conditional on the current head: crossing existence and the matching
crossing-sequence state agreement for whichever phase applies. -/
def SpliceData (M : Machine) (b : ℕ) (t : Cfg M × Cfg M × Cfg M) : Prop :=
  (t.1.hd = b + 1 →
      (∃ s, (run M s t.1).hd ≤ b) ∧ (∃ s, (run M s t.2.1).hd ≤ b) ∧
        (run M (firstExitTime M b t.2.1) t.2.1).st = (run M (firstExitTime M b t.1) t.2.2).st) ∧
  (t.1.hd = b →
      (∃ s, b < (run M s t.1).hd) ∧ (∃ s, b < (run M s t.2.2).hd) ∧
        (run M (firstEntryTime M b t.1) t.2.1).st = (run M (firstEntryTime M b t.2.2) t.2.2).st)

/-- **The head-parity splice recursion.**  From `SpliceSynced` at a rightward crossing (`γ 0` at head
`b+1`) with `SpliceData` at each of the first `k` steps, `SpliceSynced` holds at `γ k`, with the head
at `b+1` or `b`. -/
theorem splice_recursive (M : Machine) (hrf : ResetFree M) (b : ℕ) (k : ℕ)
    (t₀ : Cfg M × Cfg M × Cfg M)
    (h0 : SpliceSynced M b t₀.1 t₀.2.1 t₀.2.2) (hhd0 : t₀.1.hd = b + 1)
    (hdata : ∀ j, j < k → SpliceData M b ((nextSplice M b)^[j] t₀)) :
    SpliceSynced M b ((nextSplice M b)^[k] t₀).1 ((nextSplice M b)^[k] t₀).2.1
        ((nextSplice M b)^[k] t₀).2.2
      ∧ (((nextSplice M b)^[k] t₀).1.hd = b + 1 ∨ ((nextSplice M b)^[k] t₀).1.hd = b) := by
  revert hdata
  induction k with
  | zero => intro _; exact ⟨h0, Or.inl hhd0⟩
  | succ k ih =>
    intro hdata
    obtain ⟨ihsync, ihhd⟩ := ih (fun j hj => hdata j (by omega))
    have hdk := hdata k (by omega)
    rw [Function.iterate_succ_apply']
    set g := (nextSplice M b)^[k] t₀ with hg
    rcases ihhd with hb1 | hb
    · obtain ⟨hz_exit, hxL_exit, hstate⟩ := hdk.1 hb1
      have hstep := splice_step_right_of_next M b g.1 g.2.1 g.2.2 hb1 hz_exit hxL_exit hstate
      exact ⟨SpliceStep_preserves M hrf b _ _ _ _ _ _ ihsync hstep,
        Or.inr (nextSplice_head_right M hrf b g.1 g.2.1 g.2.2 hb1 hz_exit)⟩
    · obtain ⟨hz_re, hxR_re, hstate⟩ := hdk.2 hb
      have hstep := splice_step_left_of_next M b g.1 g.2.1 g.2.2 hb hz_re hxR_re hstate
      exact ⟨SpliceStep_preserves M hrf b _ _ _ _ _ _ ihsync hstep,
        Or.inl (nextSplice_head_left M b g.1 g.2.1 g.2.2 hb hz_re)⟩

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
