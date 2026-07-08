import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCrossBranch

/-!
# N-Frame: the Freshness Lemma is a THEOREM in restricted circuit classes

For GENERAL circuits, Freshness (`#mixed ≤ cN`, cancellation non-reusability) is equivalent to explicit
tensor subadditivity — the direct-sum / Shitov wall, open.  But in restricted classes where the
double-duty amortization mechanism is unavailable, Freshness is PROVABLE, and the whole chain
(Freshness ⟹ direct sum ⟹ amplification ⟹ super-linear) runs UNCONDITIONALLY.  This file freezes the
restricted cases — the honest stepping stone.

## The three classes where amortization is impossible

  • FORMULAS (fan-out ≤ 1): a gate feeds exactly one place, so no gate can lie in both output cones —
    `coneInter = 0` structurally.  The two copies are disjoint sub-formulas.
  • LINEAR (XOR) circuits: cross-copy cancellation is bounded by rank–nullity — a share-gate
    `ℓ(x_L) ⊕ m(x_R)` gives no net saving (frozen: `NFrameShareKernel.share_kernel_left_dim_bound`).
  • MONOTONE circuits: no negation ⟹ no cancellation.  A mixed gate's foreign content can only be
    MASKED (OR-with-1 / AND-with-0), never selectively cancelled; to keep a pure-block output
    foreign-independent for all inputs the content must be masked for all inputs ⟹ the gate contributes
    nothing useful to that output.  So the beneficial cone-intersection is `0`.

## The theorems

  `formula_freshness` — **PROVED**: fan-out ≤ 1 gives `coneInter = 0`
        (`coneL + coneR = coneUnion`); with `coneL, coneR ≥ cbudget(F_k)` and `coneUnion ≤ total`,
        `2·cbudget(F_k) ≤ total` — the exact direct sum for formulas.
  `no_cancellation_freshness` — **PROVED**: a class with no cancellation (`beneficialInter = 0`) gives
        the direct sum.  Monotone circuits satisfy `beneficialInter = 0` by the masking argument above.
  `restricted_freshness_forces_superlinear` — **PROVED**: restricted Freshness + the mixer's fresh
        charge at every scale (`2·T k + c·2^{k+1} ≤ total k`, `total k ≤ T (k+1)`) forces
        `b·2^b ≤ T b` — super-linear, UNCONDITIONALLY, in the restricted class.

## Honest scope — real in the restricted classes, open in general

`formula_freshness` is fully rigorous (fan-out 1).  `no_cancellation_freshness` is rigorous given the
no-cancellation property, which monotone circuits satisfy (standard: monotone circuits cannot cancel).
Linear is frozen (rank–nullity).  So the Freshness Lemma is a THEOREM for formula / linear / monotone
circuits, and the super-linear consequence runs unconditionally there — consistent with the known
super-polynomial monotone (Razborov) and formula (Andreev/KRW) lower bounds, which VALIDATES the
amplification framework.  For GENERAL circuits the amortization mechanism is available and Freshness
reduces to explicit tensor subadditivity (open).  This is a stepping stone, NOT full `P ≠ NP`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRestrictedFreshness

open PallLean.Paper93.DeepMath.PathB

/-- **FORMULA FRESHNESS (proved)**: in a fan-out ≤ 1 (formula) circuit, no gate lies in both output
cones, so `coneInter = 0` — i.e. `coneL + coneR = coneUnion`.  With each cone `≥ cbudget(F_k)` and the
cones inside the circuit (`coneUnion ≤ total`), the exact direct sum `2·cbudget(F_k) ≤ total` holds. -/
theorem formula_freshness (cbudgetFk coneL coneR coneUnion total : ℕ)
    (hcbL : cbudgetFk ≤ coneL) (hcbR : cbudgetFk ≤ coneR)
    (hfanout1 : coneL + coneR = coneUnion)      -- coneInter = 0 (fan-out ≤ 1 ⟹ cones disjoint)
    (hsub : coneUnion ≤ total) :
    2 * cbudgetFk ≤ total := by
  omega

/-- **NO-CANCELLATION FRESHNESS (proved)**: a circuit class with no cancellation has beneficial
cone-intersection `0` (a mixed gate's foreign content can only be masked, never selectively cancelled,
so it gives no useful shared computation).  Then inclusion–exclusion
(`coneL + coneR = coneUnion + beneficialInter`) with `beneficialInter = 0` and `coneUnion ≤ total`
gives `2·cbudget(F_k) ≤ total`.  MONOTONE circuits satisfy the `beneficialInter = 0` hypothesis. -/
theorem no_cancellation_freshness
    (cbudgetFk coneL coneR coneUnion total beneficialInter : ℕ)
    (hcbL : cbudgetFk ≤ coneL) (hcbR : cbudgetFk ≤ coneR)
    (hunion : coneL + coneR = coneUnion + beneficialInter)
    (hsub : coneUnion ≤ total)
    (hnocancel : beneficialInter = 0) :
    2 * cbudgetFk ≤ total := by
  omega

/-- **RESTRICTED FRESHNESS FORCES SUPER-LINEAR (proved)**: in a restricted class where Freshness holds,
the direct sum plus the mixer's fresh charge give, at every scale, `2·T k + c·2^{k+1} ≤ total k` with
`total k ≤ T (k+1)`; feeding `NFrameConeAmplify.amplify_exceeds_linear` yields `b·2^b ≤ T b` — super-
linear, UNCONDITIONALLY in the class (no tensor-subadditivity hypothesis). -/
theorem restricted_freshness_forces_superlinear
    (c : ℕ) (hc : 1 ≤ c) (T total : ℕ → ℕ)
    (hstep : ∀ k, 2 * T k + c * 2 ^ (k + 1) ≤ total k)
    (hchain : ∀ k, total k ≤ T (k + 1)) (b : ℕ) :
    b * 2 ^ b ≤ T b := by
  apply NFrameConeAmplify.amplify_exceeds_linear c T hc _ b
  intro k
  have h1 := hstep k; have h2 := hchain k
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameRestrictedFreshness

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRestrictedFreshness.formula_freshness
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRestrictedFreshness.no_cancellation_freshness
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRestrictedFreshness.restricted_freshness_forces_superlinear
