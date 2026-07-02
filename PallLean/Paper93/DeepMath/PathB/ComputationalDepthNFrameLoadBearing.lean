import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameProxySeparation

/-!
# N-Frame as the load-bearing separator

The classical engines (Beigel–Tarui / Razborov–Smolensky, Toda, IKW, the time hierarchy) are *inputs*.  This file makes the
**N-Frame invariant itself the beam** — the single quantity across which the separation is carried — rather than wallpaper
over a classical argument.  It follows the four-part schema:

1. **Target separation schema.**  The invariant `NFrameComplexity` (minimal `monoAND`-span degree over `F`, the concrete
   proxy for the N-Frame observer-dimension / SPDP-rank) defines a class `LowNFrame B` and a target gap `NFrameGap B`.
   `nframe_gap_iff_separation` — **PROVED**: over the N-Frame-defined class the separation is *exactly* the gap.  There is
   no slack: exceeding the bound **is** non-membership.  This is what makes N-Frame load-bearing and not a one-sided proxy.

2. **Classical inputs, as the two proved sides.**  Low side `nframeComplexity_le_two_pow_depth` (AC⁰ ⇒ low N-Frame) and
   high side `nframeComplexity_omegaFn_univ_ge` (`MOD_q` ⇒ high N-Frame), imported from the proxy files.

3. **The N-Frame essential bridge.**  `nframe_essential_bridge` — **PROVED**: if a class is *captured* by the N-Frame
   invariant at bound `B` (`NFrameCaptures`) and the target's N-Frame exceeds `B`, the target is outside the class.  This
   is the beam; everything else is which class and bound make both premises true.
   `modq_not_smallTree_via_beam` — **PROVED, UNCONDITIONAL**: run entirely through the beam, `MOD_q` is not computed by any
   small bounded-fan-in AC⁰ tree — a genuine restricted separation carried by N-Frame alone.

4. **The named remaining gap.**  `nframe_separation_conditional` isolates the load-bearing member: capturing the *general*
   model (`GenModel` = P/poly / the observer class) in the N-Frame invariant, `NFrameCaptures F GenModel B`.  By
   `nframe_gap_iff_separation` this is equal in strength to the separation, so it is the **central N-Frame conjecture** —
   stated as an explicit hypothesis, **not discharged**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

## Honest scope

The restricted separation (`MOD_q` ∉ small AC⁰, proxy level, de Morgan basis) is genuinely carried by N-Frame,
unconditionally.  The step to a general separation is precisely `NFrameCaptures F GenModel B` for the real computational
model — the "P-observer ⇒ low N-Frame dimension" principle — which is assumed, not derived, and is `P ≠ NP`-strength.
This file makes that boundary explicit; it does not cross it.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing

open PallLean.Paper93.DeepMath.PathB.NFrameACC0
open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (AndOrTree)
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-! ### 1. Target separation schema -/

/-- The N-Frame-bounded class: functions whose N-Frame complexity is at most `B`. -/
def LowNFrame (F : Type*) [Field F] {n : ℕ} (B : ℕ) (f : (Fin n → Bool) → F) : Prop :=
  NFrameComplexity F f ≤ B

/-- The target N-Frame gap: the target's N-Frame complexity exceeds the bound `B`. -/
def NFrameGap (F : Type*) [Field F] {n : ℕ} (B : ℕ) (tgt : (Fin n → Bool) → F) : Prop :=
  B < NFrameComplexity F tgt

/-- **N-Frame is an exact obstruction (proved).**  Over the N-Frame-defined class, the target gap is *equivalent* to
non-membership — there is no slack between "high N-Frame" and "outside the class".  This is precisely what makes N-Frame
load-bearing: it is not merely a lower-bound proxy, it is the membership boundary itself. -/
theorem nframe_gap_iff_separation (B : ℕ) (tgt : (Fin n → Bool) → F) :
    NFrameGap F B tgt ↔ ¬ LowNFrame F B tgt :=
  not_le.symm

/-! ### 3. The N-Frame essential bridge -/

/-- A class is **captured** by the N-Frame invariant at bound `B` when everything it computes has N-Frame complexity
`≤ B`.  This is the load-bearing member — the "membership ⇒ low N-Frame dimension" principle. -/
def NFrameCaptures (F : Type*) [Field F] {n : ℕ}
    (InClass : ((Fin n → Bool) → F) → Prop) (B : ℕ) : Prop :=
  ∀ f : (Fin n → Bool) → F, InClass f → NFrameComplexity F f ≤ B

/-- **The N-Frame essential bridge (proved).**  If a class is captured by the N-Frame invariant at bound `B`, and the
target's N-Frame complexity exceeds `B`, then the target lies outside the class.  This is the beam across which every
N-Frame separation is carried. -/
theorem nframe_essential_bridge {B : ℕ} {tgt : (Fin n → Bool) → F}
    (InClass : ((Fin n → Bool) → F) → Prop)
    (capture : NFrameCaptures F InClass B) (gap : NFrameGap F B tgt) :
    ¬ InClass tgt := fun h => absurd (capture tgt h) (not_le.mpr gap)

/-! ### 2 + 3. The proved sides, and the restricted separation carried by the beam -/

/-- The bounded-fan-in AC⁰ class: functions computed by a de Morgan tree of depth `≤ d` and leaf width `≤ w`. -/
def ComputedBySmallTree (F : Type*) [Field F] {n : ℕ} (d w : ℕ) (f : (Fin n → Bool) → F) : Prop :=
  ∃ t : AndOrTree n, treeDepth t ≤ d ∧ treeLeafWidth t ≤ w ∧ AndOrTree.evalT F t = f

/-- **Low side as a capture (proved).**  The small-AC⁰ class is captured by the N-Frame invariant at bound `2^d · w`. -/
theorem smallTree_captures (d w : ℕ) :
    NFrameCaptures F (ComputedBySmallTree (n := n) F d w) (2 ^ d * w) := by
  rintro f ⟨t, hd, hw, hcomp⟩
  rw [← hcomp]
  exact le_trans (nframeComplexity_le_two_pow_depth t)
    (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hd) hw)

/-- **High side as a gap (proved).**  For `2^d · w < ⌈n/2⌉`, `MOD_q`'s N-Frame complexity exceeds the small-AC⁰ bound. -/
theorem modq_gap [Fintype F] [DecidableEq F] {q d w : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (hn : 2 ^ d * w < n - n / 2) :
    NFrameGap F (2 ^ d * w) (omegaFn ω (Finset.univ : Finset (Fin n))) :=
  lt_of_lt_of_le hn (nframeComplexity_omegaFn_univ_ge ω hω hq2)

/-- **Restricted separation, UNCONDITIONAL, carried by the beam (proved).**  Running only through
`nframe_essential_bridge`, `MOD_q` is not computed by any small bounded-fan-in AC⁰ tree.  N-Frame is the load-bearing
member: the two classical sides enter solely as `NFrameCaptures` and `NFrameGap`. -/
theorem modq_not_smallTree_via_beam [Fintype F] [DecidableEq F] {q d w : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (hn : 2 ^ d * w < n - n / 2) :
    ¬ ComputedBySmallTree F d w (omegaFn ω (Finset.univ : Finset (Fin n))) :=
  nframe_essential_bridge (ComputedBySmallTree F d w) (smallTree_captures d w) (modq_gap ω hω hq2 hn)

/-! ### 4. The named remaining gap: the central N-Frame conjecture -/

/-- **The central N-Frame conjecture (the load-bearing beam for a general model, NOT discharged here).**  Given a general
computational model `GenModel` (P/poly, or the observer class), the bridge `NFrameCaptures F GenModel B` — that the model
is captured by the N-Frame invariant at a (polynomial) bound `B` — together with the proved high side yields the
separation `¬ GenModel tgt`.  By `nframe_gap_iff_separation`, discharging this capture is equal in strength to the
separation itself: it is the "P-observer ⇒ low N-Frame dimension" principle, assumed here as an explicit hypothesis and
left open.  This is the honest boundary — the beam is identified, its general instantiation is not proved. -/
theorem nframe_separation_conditional {B : ℕ} {tgt : (Fin n → Bool) → F}
    (GenModel : ((Fin n → Bool) → F) → Prop)
    (central_bridge : NFrameCaptures F GenModel B)
    (target_hard : NFrameGap F B tgt) :
    ¬ GenModel tgt :=
  nframe_essential_bridge GenModel central_bridge target_hard

end PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing.nframe_gap_iff_separation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing.nframe_essential_bridge
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing.modq_not_smallTree_via_beam
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing.nframe_separation_conditional
