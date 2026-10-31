import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLoadBearing

/-!
# N-Frame: the necessity direction — the gap cannot be sidestepped

The beam gives *sufficiency*: an observer class captured at bound `B` cannot decide a target above `B`
(`nframe_essential_bridge`).  This file proves the **necessity** direction — the N-Frame gap is not a lossy lower-bound
method but a **complete obstruction**: any separation of the target from a class that *contains* every low-N-Frame
function is *forced* to go through the N-Frame gap.  The invariant cannot be routed around.

The two directions rest on **dual** containments, and this is the honest structural payoff:

* **Sufficiency** needs `NFrameCaptures F InClass B` — `InClass ⊆ {low N-Frame}` — a **lower bound** ("membership ⇒ low
  N-Frame dimension").  For the real P-time model this is the `P ≠ NP`-strength member.
* **Necessity** needs `NFrameSaturates F InClass B` — `{low N-Frame} ⊆ InClass` — an **upper bound** ("low N-Frame ⇒ the
  model can realize it"), the *expressiveness* direction, which is not a lower bound and is generally the easier half.

So the entire difficulty of a separation via N-Frame is concentrated in the single *capture (lower-bound)* direction; the
*necessity* direction is comparatively cheap, and it shows the gap is unavoidable.

  `nframe_gap_necessary` — **PROVED**: saturation + separation ⇒ the N-Frame gap.  The gap is a necessary certificate.
  `nframe_separation_iff_gap_of_saturated` — **PROVED**: for a class the invariant both captures and saturates,
        `separation ↔ gap` — the obstruction is exact, with no slack.
  `modq_not_lowNFrame` — **PROVED, UNCONDITIONAL**: `MOD_q` is genuinely not low-N-Frame — the gap is a real obstruction,
        necessity realised.

## Honest scope

Necessity uses the *saturation* (upper-bound / expressiveness) containment, sufficiency the *capture* (lower-bound)
containment.  Discharging either for the real P-time model is still open; but the split is informative — the hard,
`P ≠ NP`-strength half is exactly and only the capture direction.  The gap being necessary (given saturation) shows the
N-Frame invariant is a complete obstruction that cannot be sidestepped.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameNecessity

open PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- A class **saturates** the N-Frame invariant at bound `B` when it contains *every* low-N-Frame function
(`{low N-Frame} ⊆ InClass`).  This is the *upper-bound* / expressiveness dual of `NFrameCaptures`. -/
def NFrameSaturates (F : Type*) [Field F] {n : ℕ}
    (InClass : ((Fin n → Bool) → F) → Prop) (B : ℕ) : Prop :=
  ∀ f : (Fin n → Bool) → F, LowNFrame F B f → InClass f

/-- **The N-Frame gap is necessary (proved).**  If the class contains every low-N-Frame function and the target is
separated from it, then the target genuinely has the N-Frame gap.  The gap is a necessary certificate of the separation —
it cannot be sidestepped. -/
theorem nframe_gap_necessary {B : ℕ} {tgt : (Fin n → Bool) → F}
    (InClass : ((Fin n → Bool) → F) → Prop)
    (sat : NFrameSaturates F InClass B) (hsep : ¬ InClass tgt) :
    NFrameGap F B tgt :=
  (nframe_gap_iff_separation B tgt).mpr (fun hlow => hsep (sat tgt hlow))

/-- **The obstruction is exact (proved).**  For a class the N-Frame invariant both captures and saturates (i.e. equals the
low-N-Frame class extensionally), separation and the gap are *equivalent*: there is no slack, and every separation is
exactly the gap. -/
theorem nframe_separation_iff_gap_of_saturated {B : ℕ} {tgt : (Fin n → Bool) → F}
    (InClass : ((Fin n → Bool) → F) → Prop)
    (cap : NFrameCaptures F InClass B) (sat : NFrameSaturates F InClass B) :
    ¬ InClass tgt ↔ NFrameGap F B tgt :=
  ⟨nframe_gap_necessary InClass sat, fun hgap => nframe_essential_bridge InClass cap hgap⟩

/-- The low-N-Frame class trivially captures itself. -/
theorem lowNFrame_captures (B : ℕ) : NFrameCaptures F (LowNFrame (n := n) F B) B := fun _ h => h

/-- The low-N-Frame class trivially saturates itself. -/
theorem lowNFrame_saturates (B : ℕ) : NFrameSaturates F (LowNFrame (n := n) F B) B := fun _ h => h

/-- **Complete obstruction at the canonical class (proved).**  Over the low-N-Frame class itself, separation is exactly
the gap — the N-Frame invariant is a complete, non-lossy obstruction. -/
theorem separation_iff_gap_lowNFrame (B : ℕ) (tgt : (Fin n → Bool) → F) :
    ¬ LowNFrame F B tgt ↔ NFrameGap F B tgt :=
  nframe_separation_iff_gap_of_saturated (LowNFrame F B) (lowNFrame_captures B) (lowNFrame_saturates B)

/-- **`MOD_q` is genuinely not low-N-Frame (proved, UNCONDITIONAL).**  The proved gap makes `MOD_q`'s separation from the
low-N-Frame class real — necessity realised on a concrete target. -/
theorem modq_not_lowNFrame [Fintype F] [DecidableEq F] {q d w : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (hn : 2 ^ d * w < n - n / 2) :
    ¬ LowNFrame F (2 ^ d * w) (omegaFn ω (Finset.univ : Finset (Fin n))) :=
  (separation_iff_gap_lowNFrame _ _).mpr (modq_gap ω hω hq2 hn)

end PallLean.Paper93.DeepMath.PathB.NFrameNecessity

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNecessity.nframe_gap_necessary
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNecessity.nframe_separation_iff_gap_of_saturated
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNecessity.modq_not_lowNFrame
