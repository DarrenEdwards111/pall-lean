import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame: the true step-2 target — the NON-LINEAR no-net-saving inequality

Step 1 (`NFrameShareKernel.share_kernel_left_dim_bound`) closed the LINEAR share-gate case via
rank-nullity.  This file writes down the true step-2 target for GENERAL (non-linear) circuits,
proves that it is SUFFICIENT to close the single-scale direct sum, and marks precisely what remains
open.

## The target inequality (no net saving)

For `g` share-gates — arbitrary boolean functions `h_i(x_L, x_R)` — define, via the downstream
(possibly non-linear) post-processing that must eliminate the wrong block's dependence:
  • `shareLeft`  — the pure-`x_L` content the share-gates can contribute to `F_k(x_L)` (the number of
        independent `x_L`-quantities extractable by cancelling `x_R`-dependence downstream);
  • `shareRight` — symmetric, the pure-`x_R` content.
The step-2 target is the NO-NET-SAVING inequality
  `shareLeft + shareRight ≤ CE_share`  (`= g`),
i.e. `g` share-gates yield at most `g` pure forms total — no advantage over `g` separate gates.

  `direct_sum_from_no_net_saving` — **PROVED (sufficiency)**: given the gate partition, the
        restriction bounds `CEF ≤ CE_L + shareLeft`, `CEF ≤ CE_R + shareRight` (each block's full
        computation = its pure gates plus the share-gate content it can use), the mixer fresh cost,
        AND the no-net-saving inequality `shareLeft + shareRight ≤ CE_share`, the single-scale direct
        sum `2·CEF + fresh ≤ CE` holds — which (via the vertical annulus tree-sum, already proved)
        gives `Ω(N log N)`.

## The dichotomy (the non-linear analog of rank-nullity) — per-distinction form is PROVED

Rank-nullity separated `shareLeft` from `shareRight` linearly.  The non-linear replacement is a
RESTRICTION-PROFILE dichotomy.  Fix a right-restriction `x_R = c_R`; the circuit reconstructs
`F_k(x_L) = reconstruct(share(x_L, c_R), pureL(x_L))` from the share-gate values and the pure-`x_L`
gates.  Then for any two inputs the firewall forces a dichotomy:

  `firewall_covers_distinction` — **PROVED**: if `F_k(x) ≠ F_k(x')` then EITHER the share-gate
        restriction profiles differ (`share x c_R ≠ share x' c_R` — the gates carry this `x_L`
        distinction, charge it as separate cost) OR the pure-`x_L` gates differ
        (`pureL x ≠ pureL x'` — charged to `CE_L`).  Contrapositive: if BOTH collapse on an
        `F_k`-distinct pair, `reconstruct` cannot recover `F_k` — the firewall
        (`NFrameMixingFirewall.firewall_restriction_distinguishes`) FAILS.

So every `F_k`-distinction is covered by the share-profile or the pure gates — the exact dichotomy
"enough independent restriction profiles ⇒ separate cost, else restrictions collapse ⇒ firewall
fails."  The OPEN aggregate is: summing over all `F_k`-distinctions on both sides, the share-profile
cannot cover more than `g = CE_share` total (no gate covers a left AND a right distinction beyond
its own profile).  That aggregate — `nonlinear_share_no_saving` — is the true step-2 target.

## What is proved, what is the LINEAR instance, and what is OPEN

The sufficiency is proved here: no-net-saving ⟹ direct sum ⟹ super-linear.  The no-net-saving
inequality itself:
  • LINEAR instance — PROVED: `shareLeft = dim(L(ker M))`, `shareRight = dim(M(ker L))`, and
    `shareLeft + shareRight ≤ g` by rank-nullity (`NFrameShareKernel.share_kernel_left_dim_bound`
    and its two-sided form).
  • NON-LINEAR case — OPEN, and NOT universally true.  Uhlig's mass production shows the direct sum
    FAILS for near-maximally-hard functions (shared universal table), so no-net-saving cannot hold
    for ALL `F_k`; it must use the quasi-linear structure of the recursive `F_k` specifically.  For
    non-linear `h_i`, the blocks are ENTANGLED (e.g. `h = x_{L,1}·x_{R,1}`), so there is no
    rank-nullity separation of `shareLeft` from `shareRight`; the linear-algebraic argument of
    step 1 does not apply.

## Honest scope — the step-2 target, written down and localized

This file does NOT close step 2.  It states the exact inequality step 2 must establish
(`shareLeft + shareRight ≤ CE_share` for non-linear share-gates over the quasi-linear `F_k`), proves
that inequality suffices for the whole chain, and records that it is (i) TRUE and proved in the
linear model, (ii) OPEN and not universally valid (Uhlig) in the non-linear model — hence a genuine
theorem requiring `F_k`'s structure, the direct-sum-for-circuits / KRW core.  The count-additive
measures that could prove it (information / communication content of the share-gates) are exactly
those from the IC-accounting scope; their non-linear direct sum is the open frontier.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameNonlinearShare

open PallLean.Paper93.DeepMath.PathB.NFrameConeAmplify

/-- **SUFFICIENCY OF NO-NET-SAVING (proved)**: the single-scale direct sum `2·CEF + fresh ≤ CE`
follows from the gate partition, the restriction bounds `CEF ≤ CE_L + shareLeft` and
`CEF ≤ CE_R + shareRight` (each block computed by its pure gates plus usable share content), the
mixer fresh cost `fresh ≤ CE_mix`, and the no-net-saving inequality
`shareLeft + shareRight ≤ CE_share`.  The last hypothesis is the true step-2 target: PROVED for
linear share-gates (rank-nullity), OPEN for non-linear. -/
theorem direct_sum_from_no_net_saving
    (CE CE_L CE_R CE_mix CE_share shareLeft shareRight CEF fresh : ℕ)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hmix : fresh ≤ CE_mix)
    (hPL : CEF ≤ CE_L + shareLeft)
    (hPR : CEF ≤ CE_R + shareRight)
    (hnosaving : shareLeft + shareRight ≤ CE_share) :
    2 * CEF + fresh ≤ CE := by
  omega

/-- **THE RESTRICTION-PROFILE DICHOTOMY (proved)**: the non-linear analog of rank-nullity, at the
per-distinction level.  Under a right-restriction `c_R`, `F_k(x_L)` is reconstructed from the
share-gate values `share(x_L, c_R)` and the pure-`x_L` gates `pureL(x_L)`.  Then any `F_k`
distinction is covered by ONE of them: `F_k(x) ≠ F_k(x')` forces `share x c_R ≠ share x' c_R`
(charge to the share-profile) OR `pureL x ≠ pureL x'` (charge to `CE_L`).  If BOTH collapse the
firewall fails (`reconstruct` cannot be a function recovering `F_k`). -/
theorem firewall_covers_distinction {XL XR S V O : Type*}
    (share : XL → XR → S) (pureL : XL → V) (c_R : XR)
    (reconstruct : S → V → O) (Fk : XL → O)
    (hrec : ∀ x, Fk x = reconstruct (share x c_R) (pureL x))
    (x x' : XL) (hdistinct : Fk x ≠ Fk x') :
    share x c_R ≠ share x' c_R ∨ pureL x ≠ pureL x' := by
  by_contra hc
  push_neg at hc
  obtain ⟨hs, hp⟩ := hc
  exact hdistinct (by rw [hrec x, hrec x', hs, hp])

/-- **NO-NET-SAVING AMPLIFIES (proved)**: if the no-net-saving direct sum holds at every scale — i.e.
the coneExcess profile `T` satisfies `2·T(k) + c·2^{k+1} ≤ T(k+1)` (the output of
`direct_sum_from_no_net_saving` at each level, with `fresh = c·2^{k+1}`) — then
`T(k) ≥ c·(k·2^k) = c·N·log₂N`.  So the ONLY missing ingredient for super-linear is the non-linear
no-net-saving inequality; everything downstream of it is proved. -/
theorem no_net_saving_amplifies (c : ℕ) (T : ℕ → ℕ)
    (hstep : ∀ k, 2 * T k + c * 2 ^ (k + 1) ≤ T (k + 1)) :
    ∀ k, c * (k * 2 ^ k) ≤ T k :=
  coneExcess_amplify c T hstep

end PallLean.Paper93.DeepMath.PathB.NFrameNonlinearShare

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNonlinearShare.direct_sum_from_no_net_saving
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNonlinearShare.firewall_covers_distinction
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNonlinearShare.no_net_saving_amplifies
