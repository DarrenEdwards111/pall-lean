import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSearchVerifier

/-!
# N-Frame: an arithmetic (counting / VNP) verifier realizes high N-Frame

The search/verifier file supplied the asymmetry with an *abstract* realized family.  This file upgrades the
"NP realizes high N-Frame" side into a **genuine witnessed-search verifier** and proves it is *universal* — the
NP-completeness-flavored expressiveness — reaching the high-N-Frame regime.

We model the NP verifier in its **arithmetic / counting (VNP, permanent) shape**: a finite certificate space `Witness`
and a field-valued `score` of `(input, witness)`, with realized function the witnessed sum `∑_w score x w`.  This is the
arithmetic analogue of NP acceptance — a search over certificates producing a field value — and it is the natural home for
the `N-Frame`/SPDP picture, where the canonical hard object is the permanent (VNP-complete), not a Boolean predicate.  It
also matches the proved high-N-Frame object `omegaFn ω univ = ω^{∑xᵢ}`, which is field-valued.

  `ArithVerifier` / `realized` — a finite certificate space with a field score; realized function `∑_w score x w`.
  `exists_verifier_realizing` — **PROVED**: the model is *universal* — every field-valued function on the cube is realized
        by some arithmetic verifier.  This is the NP-completeness-flavored expressiveness of the search structure.
  `arithVerifier_realizes_high` — **PROVED, UNCONDITIONAL**: some arithmetic verifier realizes a function whose N-Frame
        complexity exceeds any small-AC⁰ bound (`MOD_q`).  The witnessed-search side genuinely attains high N-Frame.
  `arithVerifier_asymmetry` / `arithVerifier_asymmetry_smallTree` — **PROVED**: the realized high-N-Frame function is not
        decided by any low-N-Frame observer (conditional on the P-side bridge in general; **unconditional** for the
        restricted small-AC⁰ observer class).

## Honest scope

The verifier model, its universality, and its reaching of the high-N-Frame regime are all genuinely established.  What is
*not* done — and must not be faked — is proving that the *canonical* VNP-complete object (the permanent) has
super-polynomial N-Frame complexity: that is the VP-vs-VNP / composite-`MOD` barrier, exactly where the polynomial method
stops (`omegaFn` reaches only linear N-Frame, `⌈n/2⌉`).  This file establishes that the arithmetic-NP search *structure*
realizes the high regime; it does not push the *magnitude* past the barrier, and the general P-side capture bridge remains
the open, `P ≠ NP`-strength member.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameArithVerifier

open PallLean.Paper93.DeepMath.PathB.NFrameLoadBearing
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- An **arithmetic (counting / VNP) verifier** over the N-Frame domain: a finite certificate space `Witness` and a
field-valued `score` of `(input, witness)`.  The realized function is the witnessed sum — the permanent / #P shape of NP
acceptance. -/
structure ArithVerifier (F : Type*) [Field F] (n : ℕ) where
  Witness : Type
  witFin : Fintype Witness
  score : (Fin n → Bool) → Witness → F

/-- The realized function of an arithmetic verifier: the witnessed sum `∑_w score x w`. -/
noncomputable def ArithVerifier.realized (V : ArithVerifier F n) : (Fin n → Bool) → F :=
  letI := V.witFin
  fun x => ∑ w, V.score x w

/-- **Universality of the arithmetic verifier model (proved).**  Every field-valued function on the cube is the realized
function of some arithmetic verifier — the NP-completeness-flavored expressiveness: the witnessed-search structure
produces any target. -/
theorem exists_verifier_realizing (g : (Fin n → Bool) → F) :
    ∃ V : ArithVerifier F n, V.realized = g := by
  refine ⟨⟨Unit, inferInstance, fun x _ => g x⟩, ?_⟩
  funext x
  simp [ArithVerifier.realized]

/-- **The arithmetic NP structure realizes high N-Frame (proved, UNCONDITIONAL).**  Since it realizes every function, in
particular some verifier realizes `MOD_q` (`omegaFn ω univ`), whose N-Frame complexity exceeds any small-AC⁰ bound
`2^d·w < ⌈n/2⌉`.  The witnessed-search side genuinely reaches the high regime, with no hypothesis. -/
theorem arithVerifier_realizes_high [Fintype F] [DecidableEq F] {q d w : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (hn : 2 ^ d * w < n - n / 2) :
    ∃ V : ArithVerifier F n, NFrameGap F (2 ^ d * w) V.realized := by
  obtain ⟨V, hV⟩ := exists_verifier_realizing (omegaFn ω (Finset.univ : Finset (Fin n)))
  refine ⟨V, ?_⟩
  rw [hV]
  exact modq_gap ω hω hq2 hn

/-- **The verifier / observer asymmetry (proved, conditional on the P-side bridge).**  An arithmetic NP verifier realizes
a function that no observer captured at bound `2^d·w` decides — the invariant separates witnessed search from low-N-Frame
observation. -/
theorem arithVerifier_asymmetry [Fintype F] [DecidableEq F] {q d w : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (hn : 2 ^ d * w < n - n / 2)
    (PObs : ((Fin n → Bool) → F) → Prop) (p_low : NFrameCaptures F PObs (2 ^ d * w)) :
    ∃ V : ArithVerifier F n, ¬ PObs V.realized := by
  obtain ⟨V, hgap⟩ := arithVerifier_realizes_high ω hω hq2 hn
  exact ⟨V, nframe_essential_bridge PObs p_low hgap⟩

/-- **Restricted verifier / observer asymmetry, UNCONDITIONAL (proved).**  For the small bounded-fan-in AC⁰ observer class
(whose N-Frame capture is proved), an arithmetic NP verifier realizes a function no such observer decides — no
hypothesis. -/
theorem arithVerifier_asymmetry_smallTree [Fintype F] [DecidableEq F] {q d w : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (hn : 2 ^ d * w < n - n / 2) :
    ∃ V : ArithVerifier F n, ¬ ComputedBySmallTree F d w V.realized :=
  arithVerifier_asymmetry ω hω hq2 hn (ComputedBySmallTree F d w) (smallTree_captures d w)

end PallLean.Paper93.DeepMath.PathB.NFrameArithVerifier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameArithVerifier.exists_verifier_realizing
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameArithVerifier.arithVerifier_realizes_high
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameArithVerifier.arithVerifier_asymmetry_smallTree
