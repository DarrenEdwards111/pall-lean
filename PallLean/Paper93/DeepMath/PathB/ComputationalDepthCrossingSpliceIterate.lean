import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpliceAdvanceLeft

/-!
# The alternating top-level splice induction

Assembles the two phase advances into the induction over the crossing index.  A `SpliceStep` is one
phase advance — a right-phase advance (dispatched when the mixed computation is at a rightward crossing,
head `b+1`) or a left-phase advance (head `b`) — and the `SpliceSynced` invariant is preserved across
any `SpliceStep`, hence across `k` of them.

* `SpliceStep` — one phase advance, packaging the excursion structure of either a right phase (`z`/`x_R`
  lockstep, `x_L` own) or a left phase (`z`/`x_L` lockstep, `x_R` own), with the matching
  crossing-sequence state agreement.
* `SpliceStep_preserves` — `SpliceSynced` + `SpliceStep` ⇒ `SpliceSynced` (case split, applying
  `splice_advance_right` or `splice_advance_left`).
* `splice_iterate` — **the alternating induction.**  Given crossing-config triples `γ 0, …, γ k` that
  are `SpliceSynced` at `γ 0` and joined by a `SpliceStep` at each consecutive pair, `SpliceSynced`
  holds at `γ k`.

So the mixed computation stays spliced — left tape matching `x_L`, right tape matching `x_R`, same
state and head — at every crossing, given the shared crossing sequence supplies the per-step state
agreements.  From this, `z` accepts iff the references do (the fooling contradiction).

## What still remains (NOT here)

Instantiating `γ` from an actual computation (extracting the crossing configs and discharging each
`SpliceStep` from the real crossing times, as for the right-side determinism), the concrete palindrome
family, and the `Ω(n)`-cut summation are the remaining work; this file does **not** claim the `Ω(n²)`
bound (restricted: `crossingCount ≤ time` caps the technique at polynomial, one-tape P `=` P, not
`SAT ∉ P`).

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- One splice phase advance: a right phase (head `b+1`; `z`/`x_R` lockstep of length `d`, `x_L` own of
length `e`) or a left phase (head `b`; `z`/`x_L` lockstep of length `d`, `x_R` own of length `e`), with
the matching crossing-sequence state agreement, taking `(z,xL,xR)` to `(z',xL',xR')`. -/
def SpliceStep (M : Machine) (b : ℕ) (z xL xR z' xL' xR' : Cfg M) : Prop :=
  (∃ d e, z.hd = b + 1 ∧
      (∀ j, j < d → b < (run M j z).hd) ∧ (run M d z).hd ≤ b ∧
      (∀ j, j < e → b < (run M j xL).hd) ∧ (run M e xL).hd ≤ b ∧
      (run M e xL).st = (run M d xR).st ∧
      z' = run M d z ∧ xL' = run M e xL ∧ xR' = run M d xR)
  ∨ (∃ d e, z.hd = b ∧
      (∀ j, j < d → (run M j z).hd ≤ b) ∧ b < (run M d z).hd ∧
      (∀ j, j < e → (run M j xR).hd ≤ b) ∧ b < (run M e xR).hd ∧
      (run M d xL).st = (run M e xR).st ∧
      z' = run M d z ∧ xL' = run M d xL ∧ xR' = run M e xR)

/-- `SpliceSynced` is preserved across one `SpliceStep` (reset-free). -/
theorem SpliceStep_preserves (M : Machine) (hrf : ResetFree M) (b : ℕ) (z xL xR z' xL' xR' : Cfg M)
    (h : SpliceSynced M b z xL xR) (hstep : SpliceStep M b z xL xR z' xL' xR') :
    SpliceSynced M b z' xL' xR' := by
  rcases hstep with ⟨d, e, he, hzp, hze, hxp, hxe, hs, rfl, rfl, rfl⟩ |
      ⟨d, e, he, hzp, hze, hxp, hxe, hs, rfl, rfl, rfl⟩
  · exact splice_advance_right M hrf b z xL xR d e h he hzp hze hxp hxe hs
  · exact splice_advance_left M b z xL xR d e h he hzp hze hxp hxe hs

/-- **The alternating top-level induction.**  Crossing-config triples `γ 0, …, γ k` that are
`SpliceSynced` at `γ 0` and joined by a `SpliceStep` at each consecutive pair are `SpliceSynced` at
`γ k`. -/
theorem splice_iterate (M : Machine) (hrf : ResetFree M) (b : ℕ) (k : ℕ)
    (γ : ℕ → Cfg M × Cfg M × Cfg M)
    (h0 : SpliceSynced M b (γ 0).1 (γ 0).2.1 (γ 0).2.2)
    (hstep : ∀ j, j < k → SpliceStep M b (γ j).1 (γ j).2.1 (γ j).2.2
      (γ (j + 1)).1 (γ (j + 1)).2.1 (γ (j + 1)).2.2) :
    SpliceSynced M b (γ k).1 (γ k).2.1 (γ k).2.2 := by
  revert hstep
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hstep
    exact SpliceStep_preserves M hrf b (γ k).1 (γ k).2.1 (γ k).2.2
      (γ (k + 1)).1 (γ (k + 1)).2.1 (γ (k + 1)).2.2
      (ih (fun j hj => hstep j (by omega))) (hstep k (by omega))

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
