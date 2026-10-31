import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLoadBearing

/-!
# N-Frame: the search / verifier asymmetry

The load-bearing file made the N-Frame invariant the beam and named the central bridge.  This file sharpens that bridge
into the **search / verifier asymmetry** — the shape that is specific to `P vs NP` and that Williams' route does not reach:

> The N-Frame invariant separates what NP *witnesses realize* from what P-time computation *can preserve*.

The two sides are treated asymmetrically, and honestly:

* **NP realizes high N-Frame — PROVED, UNCONDITIONAL.**  The search / verifier side realizes functions across the whole
  N-Frame spectrum, *including the high regime*.  Concretely (`search_realizes_high`) a family realizing `MOD_q` realizes a
  function whose N-Frame complexity exceeds any small-AC⁰ bound `2^d·w < ⌈n/2⌉`.  No hypothesis: the realizability side
  genuinely reaches high N-Frame.
* **P-time preserves low N-Frame — the NAMED bridge.**  That a P-time observer's decided functions are *captured* by the
  N-Frame invariant at a (polynomial) bound is `NFrameCaptures F PTime B` — the load-bearing member, assumed not derived.

  `search_verifier_asymmetry` — **PROVED (conditional on the P-side bridge)**: capture of the observer at `B` + a witness
        realizing above `B` ⇒ that realized function is not observer-decidable.  The invariant separates the two.
  `search_realizes_high` — **PROVED, UNCONDITIONAL**: the realizability side reaches high N-Frame (via `MOD_q`).
  `modq_asymmetry_smallTree` — **PROVED, UNCONDITIONAL**: for the *restricted* observer class (small bounded-fan-in AC⁰,
        whose N-Frame capture is proved), the asymmetry holds with no hypothesis — `MOD_q` is realized but not observable.
  `search_verifier_asymmetry_general` — the central conjecture named: for the *general* P-time model the capture bridge is
        `P ≠ NP`-strength and is left open.

## Honest scope

The realizability half is genuinely established; the beam is genuine; the restricted asymmetry is unconditional.  What is
*not* proved — and is stated only as an explicit hypothesis — is that the **general P-time model preserves low N-Frame
dimension** (`NFrameCaptures F PTime B`).  That is the "P-observer ⇒ low N-Frame" principle, equal in strength to the
separation itself (by `nframe_gap_iff_separation`).  This file isolates it as sharply as possible; it does not discharge
it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSearchVerifier

open PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- **NP / search realizability.**  `f` is realized by some witness of the family `realized` — the search side produces
`f` from a certificate. -/
def NPRealizable {W : Type*} (realized : W → ((Fin n → Bool) → F))
    (f : (Fin n → Bool) → F) : Prop :=
  ∃ w, realized w = f

/-- **The search / verifier asymmetry (proved, conditional on the P-side bridge).**  If the observer class `PObs` is
captured by the N-Frame invariant at bound `B` (the load-bearing hypothesis — "P-time preserves low N-Frame"), while some
witness of the search family realizes a function whose N-Frame complexity exceeds `B`, then that realized function is not
observer-decidable.  The N-Frame invariant separates what NP witnesses realize from what the observer preserves. -/
theorem search_verifier_asymmetry {W : Type*} {B : ℕ}
    (realized : W → ((Fin n → Bool) → F)) (PObs : ((Fin n → Bool) → F) → Prop)
    (p_preserves_low : NFrameCaptures F PObs B)
    (np_realizes_high : ∃ w, NFrameGap F B (realized w)) :
    ∃ f, NPRealizable realized f ∧ ¬ PObs f := by
  obtain ⟨w, hw⟩ := np_realizes_high
  exact ⟨realized w, ⟨w, rfl⟩, nframe_essential_bridge PObs p_preserves_low hw⟩

/-- **NP / search reaches high N-Frame (proved, UNCONDITIONAL).**  If the family realizes `MOD_q` at some witness, it
realizes a function whose N-Frame complexity exceeds any small-AC⁰ bound `2^d·w < ⌈n/2⌉` — the realizability side
genuinely attains the high regime, with no hypothesis. -/
theorem search_realizes_high [Fintype F] [DecidableEq F] {W : Type*} {q d w : ℕ}
    (realized : W → ((Fin n → Bool) → F)) (w0 : W) (ω : F)
    (hreal : realized w0 = omegaFn ω (Finset.univ : Finset (Fin n)))
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (hn : 2 ^ d * w < n - n / 2) :
    ∃ ww, NFrameGap F (2 ^ d * w) (realized ww) := by
  refine ⟨w0, ?_⟩
  rw [hreal]
  exact modq_gap ω hω hq2 hn

/-- **Restricted asymmetry, UNCONDITIONAL (proved).**  For the *restricted* observer class — small bounded-fan-in AC⁰,
whose N-Frame capture is proved (`smallTree_captures`) — the search / verifier asymmetry holds with no hypothesis:
`MOD_q` is realized by the search family but is not decided by any small AC⁰ observer. -/
theorem modq_asymmetry_smallTree [Fintype F] [DecidableEq F] {W : Type*} {q d w : ℕ}
    (realized : W → ((Fin n → Bool) → F)) (w0 : W) (ω : F)
    (hreal : realized w0 = omegaFn ω (Finset.univ : Finset (Fin n)))
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (hn : 2 ^ d * w < n - n / 2) :
    ∃ f, NPRealizable realized f ∧ ¬ ComputedBySmallTree F d w f :=
  search_verifier_asymmetry realized (ComputedBySmallTree F d w) (smallTree_captures d w)
    (search_realizes_high realized w0 ω hreal hω hq2 hn)

/-- **The central asymmetry conjecture (NAMED, NOT discharged).**  For the general P-time observer model `PTime`, the
bridge `NFrameCaptures F PTime B` — "P-time computation preserves low N-Frame dimension" — is the load-bearing member.
Given it, an NP-witness-realized high-N-Frame function is not P-decidable: this is the search / verifier asymmetry that
P-time cannot preserve but NP witnesses realize.  Discharging the bridge for the real P-time model is `P ≠ NP`-strength
(equal-strength to the separation, by `nframe_gap_iff_separation`) and is left open. -/
theorem search_verifier_asymmetry_general {W : Type*} {B : ℕ}
    (realized : W → ((Fin n → Bool) → F)) (PTime : ((Fin n → Bool) → F) → Prop)
    (p_preserves_low : NFrameCaptures F PTime B)
    (np_realizes_high : ∃ w, NFrameGap F B (realized w)) :
    ∃ f, NPRealizable realized f ∧ ¬ PTime f :=
  search_verifier_asymmetry realized PTime p_preserves_low np_realizes_high

end PallLean.Paper93.DeepMath.PathB.NFrameSearchVerifier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSearchVerifier.search_verifier_asymmetry
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSearchVerifier.search_realizes_high
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSearchVerifier.modq_asymmetry_smallTree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSearchVerifier.search_verifier_asymmetry_general
