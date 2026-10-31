import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLoadBearing

/-!
# Calibrating the central N-Frame capture conjecture

The central conjecture (`nframe_separation_conditional`) needs `NFrameCaptures F GenModel B` for a
general model `GenModel ⊇ P/poly` at a *polynomial* bound `B`.  This file pins a hard, unconditional
constraint on that bound: since `MOD_q` (an `ACC⁰ ⊆ P/poly` function) has N-Frame complexity
`≥ ⌈n/2⌉` (`nframeComplexity_omegaFn_univ_ge`), any class containing `MOD_q` — in particular P/poly —
cannot be captured below `⌈n/2⌉`.

* `capture_bound_ge_of_contains_modq` — a class containing `MOD_q`, captured at `B`, has `B ≥ ⌈n/2⌉`.
* `separation_target_exceeds_modq_floor` — hence, in any N-Frame separation carried by such a class
  (capture at `B` + target gap), the target's N-Frame complexity strictly exceeds `⌈n/2⌉`.

**What this calibrates.**  `MOD_q`'s `⌈n/2⌉` gap yields only the *restricted* separation
(`modq_not_smallTree_via_beam`), because it is exactly at — not above — the floor any P/poly-capture
bound must reach.  The *general* separation via this route therefore requires a target with
**superlinear** N-Frame complexity, beyond what any P/poly function (including `MOD_q`) can have if the
capture holds.  This is a genuine sharpening of the conjecture, not a discharge: the capture itself
(`≡` Valiant rigidity in the linear case) remains the open, P≠NP-strength core.

Nothing here proves `P ≠ NP`, discharges the capture, or is `NEXP ⊄ ACC⁰`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing

open PallLean.Paper93.DeepMath.PathB.NFrameACC0
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- **The capture bound is forced `≥ ⌈n/2⌉`.**  Any class containing `MOD_q` and captured by the
N-Frame invariant at bound `B` must have `B ≥ ⌈n/2⌉`, because `MOD_q`'s own N-Frame complexity is
`≥ ⌈n/2⌉`. -/
theorem capture_bound_ge_of_contains_modq [Fintype F] [DecidableEq F] {q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) {B : ℕ}
    (InClass : ((Fin n → Bool) → F) → Prop)
    (hcap : NFrameCaptures F InClass B)
    (hmem : InClass (omegaFn ω (Finset.univ : Finset (Fin n)))) :
    n - n / 2 ≤ B :=
  le_trans (nframeComplexity_omegaFn_univ_ge ω hω hq2) (hcap _ hmem)

/-- **The general separation target must exceed the `MOD_q` floor.**  In any N-Frame separation carried
by a class containing `MOD_q` (capture at `B`, plus a target gap `B < NFrameComplexity tgt`), the
target's N-Frame complexity strictly exceeds `⌈n/2⌉` — so it is superlinear, beyond `MOD_q`'s own
restricted gap. -/
theorem separation_target_exceeds_modq_floor [Fintype F] [DecidableEq F] {q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) {B : ℕ} {tgt : (Fin n → Bool) → F}
    (InClass : ((Fin n → Bool) → F) → Prop)
    (hcap : NFrameCaptures F InClass B)
    (hmem : InClass (omegaFn ω (Finset.univ : Finset (Fin n))))
    (hgap : NFrameGap F B tgt) :
    n - n / 2 < NFrameComplexity F tgt :=
  lt_of_le_of_lt (capture_bound_ge_of_contains_modq ω hω hq2 InClass hcap hmem) hgap

end PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing
