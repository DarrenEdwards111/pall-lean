import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMlPoly

/-!
# AC⁰ circuits have bounded literal `SPDP.spdpRank` (`acc0_implies_low_spdpRank`)

Lifting the AC⁰ side of the N-Frame separation skeleton from the *proxy* to the repo's *literal* SPDP object.  The
socket (`…NFrameACC0Socket`) gave `NFrameComplexity (evalT F t) ≤ 2^{depth}·leafWidth`; the function-level bridge
(`…NFrameMlPoly`) turns low N-Frame complexity into a literal multilinear `MvPolynomial` representative with bounded
`SPDP.spdpRank`.  Composing:

  `andOrTree_spdpRank_le` — every bounded-fan-in AC⁰ (de Morgan basis) circuit `t` has a literal multilinear
        `MvPolynomial` representative `p` (`∀ x, evalT F t x = eval (boolToField∘x) p`) with
        `spdpRank κ ℓ p ≤ finrank(restrictTotalDegree (Fin n) F (ℓ + 2^{depth t}·leafWidth t))`.

So **constant-depth bounded-fan-in circuits have bounded literal `SPDP.spdpRank`** — the `acc0_implies_low_spdpRank`
direction, now against the repo's actual SPDP object rather than the proxy.

## Honest scope

Still the **safe** half (AC⁰ ⇒ bounded SPDP rank) and the **bounded-fan-in de Morgan basis** (no `MOD` gates inside).
The hard direction (an SPDP rank *lower* bound for an explicit hard family) and full ACC⁰ with unbounded composite
`MOD` are the barriers, untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge

open MvPolynomial SPDP
open PallLean.Paper93.DeepMath.PathB.Layer4 (boolToField)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0 (treeDepth treeLeafWidth nframeComplexity_le_two_pow_depth)
open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (AndOrTree)

variable {n : ℕ} {F : Type*} [Field F]

/-- **AC⁰ ⇒ bounded literal `spdpRank` (proved).**  Every bounded-fan-in de Morgan circuit `t` has a literal
multilinear `MvPolynomial` representative whose literal `SPDP.spdpRank` is bounded by
`finrank(restrictTotalDegree (ℓ + 2^{depth}·leafWidth))`. -/
theorem andOrTree_spdpRank_le [Fintype F] [DecidableEq F] (κ ℓ : ℕ) (t : AndOrTree n) :
    ∃ p : MvPolynomial (Fin n) F,
      (∀ x, AndOrTree.evalT F t x = eval (fun i => boolToField F (x i)) p) ∧
      spdpRank κ ℓ p ≤
        Module.finrank F (restrictTotalDegree (Fin n) F (ℓ + 2 ^ treeDepth t * treeLeafWidth t)) :=
  nframeComplexity_le_imp_spdpRank_le κ ℓ (AndOrTree.evalT F t) (nframeComplexity_le_two_pow_depth t)

end PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSPDPBridge.andOrTree_spdpRank_le
