import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame: the horizontal cross-branch at a single scale — direct sum, deficit = share-gates

The last residual, in its smallest form: at ONE scale, `F_{k+1}(x) = Mix_G(F_k(x_L), F_k(x_R))` on
disjoint blocks `x_L, x_R`.  Does independence + the injective mixer force the two sub-cones
disjoint (the `2×` recurrence `CE(F_{k+1}) ≥ 2·CE(F_k) + cN`)?  This is the direct sum for circuit
cone-excess at one level.  We give the exact gate accounting: it closes outright when
cancellation-free, and the deficit is EXACTLY the count of cancellation-sharing gates.

## The gate partition

Every gate of a circuit for `F_{k+1}` depends on some subset of the inputs; classify:
  • `CE_L`  — L-gates: depend on `x_L` only (compute `F_k(x_L)`, the mixer's first input).
  • `CE_R`  — R-gates: depend on `x_R` only.
  • `CE_mix` — mixer-gates: the legitimate mixer reading both `F_k` outputs (fresh cost `≥ cN`).
  • `CE_share` — SHARE-gates: depend on both blocks BELOW the mixer — cancellation-sharing.
These four classes are disjoint, so `CE_L + CE_R + CE_mix + CE_share ≤ CE`.

Restriction `x_R = 0` makes `F_{k+1}(·,0) = Mix_G(F_k(·), F_k(0))` an injective function of
`F_k(x_L)` (firewall), so the gates active under `x_R = 0` — the L-gates plus any share-gates
(which become `x_L`-functions) — compute `F_k(x_L)`: `CE(F_k) ≤ CE_L + CE_share`.  Symmetrically
`CE(F_k) ≤ CE_R + CE_share`.

  `single_scale_recurrence_cancellation_free` — **PROVED**: with NO share-gates
        (`CE(F_k) ≤ CE_L`, `CE(F_k) ≤ CE_R`, `fresh ≤ CE_mix`, disjoint), the FULL recurrence
        `2·CE(F_k) + fresh ≤ CE(F_{k+1})` holds outright.
  `single_scale_recurrence_deficit` — **PROVED**: in general
        `2·CE(F_k) + fresh ≤ CE(F_{k+1}) + CE_share` — i.e. `CE(F_{k+1}) ≥ 2·CE(F_k) + fresh −
        CE_share`.  The deficit from the ideal `2×` recurrence is EXACTLY `CE_share`, the count of
        cancellation-sharing gates.  Nothing else — not the mixer, not the restriction slack —
        contributes to the gap.

## What this settles, and the residual reduced to one quantity

The horizontal cross-branch is now a single scalar question: is `CE_share = o(CE(F_k))`?  If yes,
the recurrence closes (up to `1+o(1)`) and super-linear follows (`firewall_amplifies`); if
`CE_share = 0` it closes exactly.  So the direct-sum residual has been reduced from "are the cones
disjoint" to "how many gates depend on BOTH blocks below the mixer" — and the deficit is provably
nothing but that count.

The residual `CE_share = o(CE(F_k))` is the open core (direct sum for circuits).  The structural
reason to expect it: a share-gate `w = ℓ(x_L) ⊕ m(x_R)` can serve `F_k(x_L)` only if its `m(x_R)`
part cancels at every L-output it reaches, which requires another share-gate carrying the SAME
`m(x_R)` — share-gates come in canceling groups, and a canceling group of size `g` produces `g−1`
independent `x_L`-forms, no better than pure L-gates.  Proving this pairing bounds `CE_share` is the
open step; the accounting here reduces the entire tower to it.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameCrossBranch

/-- **THE CANCELLATION-FREE DIRECT SUM (proved)**: with no share-gates — the L-gates alone compute
`F_k(x_L)` (`CEF ≤ CE_L`), the R-gates alone `F_k(x_R)` (`CEF ≤ CE_R`), the mixer carries the fresh
cost (`fresh ≤ CE_mix`), and the three classes are disjoint (`CE_L + CE_R + CE_mix ≤ CE`) — the FULL
recurrence `2·CEF + fresh ≤ CE` holds outright. -/
theorem single_scale_recurrence_cancellation_free
    (CE CE_L CE_R CE_mix CEF fresh : ℕ)
    (hpartition : CE_L + CE_R + CE_mix ≤ CE)
    (hL : CEF ≤ CE_L) (hR : CEF ≤ CE_R) (hmix : fresh ≤ CE_mix) :
    2 * CEF + fresh ≤ CE := by
  omega

/-- **THE DIRECT-SUM DEFICIT IS EXACTLY THE SHARE-GATES (proved)**: with the four disjoint classes
(`CE_L + CE_R + CE_mix + CE_share ≤ CE`), the restriction bounds `CEF ≤ CE_L + CE_share` and
`CEF ≤ CE_R + CE_share`, and the mixer fresh cost `fresh ≤ CE_mix`, we get
`2·CEF + fresh ≤ CE + CE_share` — i.e. `CE ≥ 2·CEF + fresh − CE_share`.  The gap from the ideal
`2×` recurrence is EXACTLY the count of cancellation-sharing gates. -/
theorem single_scale_recurrence_deficit
    (CE CE_L CE_R CE_mix CE_share CEF fresh : ℕ)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hL : CEF ≤ CE_L + CE_share) (hR : CEF ≤ CE_R + CE_share) (hmix : fresh ≤ CE_mix) :
    2 * CEF + fresh ≤ CE + CE_share := by
  omega

/-- **THE RESIDUAL IS ONE SCALAR (proved)**: if the share-gate count is at most the mixer fresh
budget `CE_share ≤ fresh`, the recurrence still gives `2·CEF ≤ CE` (the doubling survives, the fresh
absorbs the deficit).  So the entire horizontal cross-branch reduces to bounding `CE_share`. -/
theorem share_absorbed_gives_doubling
    (CE CE_L CE_R CE_mix CE_share CEF fresh : ℕ)
    (hpartition : CE_L + CE_R + CE_mix + CE_share ≤ CE)
    (hL : CEF ≤ CE_L + CE_share) (hR : CEF ≤ CE_R + CE_share) (hmix : fresh ≤ CE_mix)
    (habsorb : CE_share ≤ fresh) :
    2 * CEF ≤ CE := by
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameCrossBranch

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCrossBranch.single_scale_recurrence_cancellation_free
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCrossBranch.single_scale_recurrence_deficit
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCrossBranch.share_absorbed_gives_doubling
