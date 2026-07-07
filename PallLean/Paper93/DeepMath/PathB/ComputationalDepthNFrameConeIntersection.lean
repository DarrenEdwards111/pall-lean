import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame: repairing the mixer double-counting — the cone-intersection deficit

The two-sided-restriction attack double-counted the mixer: under `x_R = const` a mixer gate becomes a
single-variable function of `F_k(x_L)`, so it is ACTIVE, and restriction cannot exclude it from either
side.  The repair uses CONES, not restriction: `F_k(x_L)` is the mixer's INPUT, computed by gates
BELOW the mixer, so the cone of `F_k(x_L)` excludes the mixer by construction.  This puts the mixer on
the `+` (fresh) side and isolates the deficit to the cone INTERSECTION — the gates feeding BOTH
sub-computations.

## The repaired bound

Let `coneL = |cone(F_k(x_L))|`, `coneR = |cone(F_k(x_R))|` (gates below the mixer feeding each input),
`coneUnion = |cone_L ∪ cone_R|`, `coneInter = |cone_L ∩ cone_R|`, `mixer` = the mixer gates (disjoint
from the cones, above them), `total` = all gates.

  • FIREWALL: `F_k(x_L)` is genuinely computed (mixer injective), so `coneL ≥ cbudget(F_k)`; sym `coneR`.
  • DISJOINTNESS: `coneUnion + mixer ≤ total` (cone gates feed `F_k` outputs; mixer reads them — distinct).
  • INCLUSION–EXCLUSION: `coneL + coneR = coneUnion + coneInter`.

  `cone_intersection_deficit` — **PROVED**: `2·cbudget(F_k) + mixer ≤ total + coneInter`, i.e.
        `total ≥ 2·cbudget(F_k) + mixer − coneInter`.  The mixer is now on the `+` side (fresh), and
        the deficit is EXACTLY `coneInter` — the gates in BOTH cones.  With `mixer ≥ cN`, this is
        `total ≥ 2·cbudget(F_k) + cN − coneInter`.
  `direct_sum_from_cone_inter_le_mixer` — **PROVED**: if `coneInter ≤ mixer`, then
        `2·cbudget(F_k) ≤ total` — the full `2×`.

## What this repairs, and the residual

This fixes the double-counting the previous attack exposed: the plain restriction gave
`total ≥ 2·cbudget − cross` (mixer subtracted, wrong side); the cone argument gives
`total ≥ 2·cbudget + mixer − coneInter` (mixer added, correct side) — a genuine `+2·mixer` correction.
The deficit is now the CONE INTERSECTION, not all cross-gates: only gates feeding BOTH `F_k`
computations count against the bound.  These are the boundary-neutral cancellation shares (a gate
serving both disjoint-input cones does so via cancellation), exactly as the boundary-carrying picture
predicted; the mixer's `Ω(cN)` boundary-carrying gates are correctly excluded.

The direct sum now closes iff `coneInter ≤ mixer` (`= cN`): the gates feeding both sub-computations
number at most the mixer's fresh count.  That residual — `coneInter ≤ cN` — is the cross-branch direct
sum in its cleanest combinatorial form (a cone-intersection count, no info-vs-size gap), and it is NOT
proved here.  So this is a genuine accounting repair that isolates the deficit correctly; it does not
close the direct sum.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameConeIntersection

/-- **THE CONE-INTERSECTION DEFICIT (proved)**: with the two `F_k` sub-cones each `≥ cbudget(F_k)`,
the cones disjoint from the mixer (`coneUnion + mixer ≤ total`), and inclusion–exclusion
(`coneL + coneR = coneUnion + coneInter`), the mixer is charged as FRESH and the deficit is exactly
the cone intersection: `2·cbudget(F_k) + mixer ≤ total + coneInter`. -/
theorem cone_intersection_deficit
    (cbudgetFk coneL coneR coneUnion coneInter mixer total : ℕ)
    (hcbL : cbudgetFk ≤ coneL) (hcbR : cbudgetFk ≤ coneR)
    (hunion : coneL + coneR = coneUnion + coneInter)
    (hsub : coneUnion + mixer ≤ total) :
    2 * cbudgetFk + mixer ≤ total + coneInter := by
  omega

/-- **THE REPAIRED CLOSER (proved)**: if the cone intersection is at most the mixer's fresh count
(`coneInter ≤ mixer`), the deficit vanishes and `2·cbudget(F_k) ≤ total` — the full `2×` direct sum.
The residual is `coneInter ≤ cN`: the gates feeding both sub-computations number at most the mixer's
fresh gates. -/
theorem direct_sum_from_cone_inter_le_mixer
    (cbudgetFk mixer coneInter total : ℕ)
    (hdef : 2 * cbudgetFk + mixer ≤ total + coneInter)
    (hinter : coneInter ≤ mixer) :
    2 * cbudgetFk ≤ total := by
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameConeIntersection

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConeIntersection.cone_intersection_deficit
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConeIntersection.direct_sum_from_cone_inter_le_mixer
