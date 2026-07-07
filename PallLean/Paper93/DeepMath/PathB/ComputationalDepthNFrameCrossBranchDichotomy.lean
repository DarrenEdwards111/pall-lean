import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame: the cross-branch direct sum holds OUTSIDE the middle-sharing regime

Attacking the single open inequality head-on for the specific recursive `F_k`:
`CE(F_{k+1}) ≥ 2·cbudget(F_k) + cN` (the horizontal cross-branch direct sum).  Result: not a closure,
but a genuine SHARPENING — the `2×` bound is PROVED except in one bounded `coneExcess` regime.

## The three established inputs

For any circuit `C` computing `F_{k+1}`, with `savings` = length cut by cross-cone sharing:
  • DISJOINT-DEFICIT (firewall forces both `F_k`, `single_scale_recurrence_deficit`):
      `2·cbudget(F_k) + cN ≤ length + savings`   (i.e. `length ≥ 2·cbudget(F_k) + cN − savings`).
  • LEDGER (connectivity-fanout): `2·|ESS| + coneExcess ≤ length + 1`.
  • PER-SHARE ACCOUNTING: a cross-cone shared gate serves both cones, so it has fan-out `≥ 2`
    (`coneExcess` contribution `≥ 1`) while cutting `≤ 1` gate — hence `savings ≤ coneExcess`.

## The dichotomy

  `cross_branch_2x_outside_middle` — **PROVED**: from the three inputs above, if EITHER
  `coneExcess ≤ cN` OR `2·cbudget(F_k) ≤ 2·|ESS| + coneExcess`, then `2·cbudget(F_k) ≤ length + 1`
  — the full `2×` direct-sum bound.
    * Low regime (`coneExcess ≤ cN`): then `savings ≤ coneExcess ≤ cN`, so the disjoint-deficit gives
      `2·cbudget(F_k) + cN ≤ length + cN`, i.e. `2·cbudget(F_k) ≤ length`.
    * High regime (`2·cbudget(F_k) ≤ 2|ESS| + coneExcess`): the ledger alone gives it.

So the adversary is squeezed at BOTH ends: little sharing ⟹ the cones are ~disjoint (`2×` directly);
much sharing ⟹ the ledger charges the resulting `coneExcess` (`2×` via the ledger).

## The remaining open set — the middle regime

The `2×` bound is open ONLY when BOTH `cN < coneExcess` AND `2|ESS| + coneExcess < 2·cbudget(F_k)`,
i.e. `cN < coneExcess < 2·cbudget(F_k) − 2|ESS|`: the MODERATE-sharing regime, where `savings ≈
coneExcess` lets a circuit trade length for cone-excess and land near `1×`.  Closing the direct sum
is now exactly: rule out this middle regime — equivalently, prove that in it the per-share accounting
is strictly better than `savings ≤ coneExcess` (each cross-cone share must add `≥ 2` to `coneExcess`,
`savings ≤ coneExcess/2`), which for the expander mixer would follow if a share that helps both sides
must reconstruct `Ω(1)` fresh boundary crossings on each side.  That per-share `≥ 2` bound is the
residual — not proved here.

This does NOT close the cross-branch; it localizes it to one bounded regime and names the exact
per-share inequality that would finish it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameCrossBranchDichotomy

/-- **THE DICHOTOMY (proved)**: the cross-branch `2×` direct-sum bound `2·cbudget(F_k) ≤ length + 1`
holds outside the middle-sharing regime.  Inputs: the disjoint-deficit bound
(`2·cbudgetFk + cN ≤ length + savings`), the ledger (`2·ess + coneExcess ≤ length + 1`), the
per-share accounting (`savings ≤ coneExcess`), and the case split `coneExcess ≤ cN` (low sharing) or
`2·cbudgetFk ≤ 2·ess + coneExcess` (high cone-excess). -/
theorem cross_branch_2x_outside_middle
    (length cbudgetFk coneExcess ess savings cN : ℕ)
    (hdisjoint : 2 * cbudgetFk + cN ≤ length + savings)
    (hledger : 2 * ess + coneExcess ≤ length + 1)
    (hsavings : savings ≤ coneExcess)
    (hcase : coneExcess ≤ cN ∨ 2 * cbudgetFk ≤ 2 * ess + coneExcess) :
    2 * cbudgetFk ≤ length + 1 := by
  rcases hcase with h | h <;> omega

/-- **THE MIDDLE REGIME IS THE ONLY GAP (proved)**: if the `2×` bound FAILS
(`length + 1 < 2·cbudgetFk`), then — given the three inputs — the cone-excess must lie strictly in
the middle band `cN < coneExcess` and `2·ess + coneExcess < 2·cbudgetFk`.  So the entire open content
of the cross-branch direct sum is confined to that band. -/
theorem cross_branch_gap_is_middle
    (length cbudgetFk coneExcess ess savings cN : ℕ)
    (hdisjoint : 2 * cbudgetFk + cN ≤ length + savings)
    (hledger : 2 * ess + coneExcess ≤ length + 1)
    (hsavings : savings ≤ coneExcess)
    (hfail : length + 1 < 2 * cbudgetFk) :
    cN < coneExcess ∧ 2 * ess + coneExcess < 2 * cbudgetFk := by
  refine ⟨?_, ?_⟩ <;> omega

end PallLean.Paper93.DeepMath.PathB.NFrameCrossBranchDichotomy

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCrossBranchDichotomy.cross_branch_2x_outside_middle
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameCrossBranchDichotomy.cross_branch_gap_is_middle
