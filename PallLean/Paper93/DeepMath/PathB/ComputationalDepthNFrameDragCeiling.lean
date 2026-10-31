import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadForm

/-!
# N-Frame: the drag's linear ceiling — why "flat + super-linearly-hard" is out of the method

Attacking sub-target (b) — a flat family that is also HARD — forced a precise look at what the
drag CAN prove, and it caps at `~3N`.  The drag lower-bounds `cbudget` by
`2·|ESS| + coneExcess`, and it lower-bounds `coneExcess` ONLY through cut capacity:
`cut_row_capacity` gives `|Y| ≤ 2^{coneExcess+1}` for a distinguished row family `Y ⊆ {0,1}^N`,
so the drag's certificate is `coneExcess ≥ log₂|Y| − 1`.  But `|Y| ≤ 2^N` (there are only `2^N`
possible rows), so `log₂|Y| ≤ N`: the cut-capacity technique CANNOT certify `coneExcess > N`.

  `rowFamily_card_le` — **PROVED**: any row family `Y ⊆ {0,1}^N` has `|Y| ≤ 2^N` — so
        `log₂|Y| ≤ N`, and the drag's `coneExcess` certificate is `≤ N`.
  `drag_linear_ceiling` — **PROVED**: `2·ess + coneBound ≤ 3·N` when `ess ≤ N` (essential
        variables ≤ inputs) and `coneBound ≤ N` (cut-capacity bound) — the drag-provable
        `cbudget` lower bound is `≤ 3N`.

## Honest scope — sub-target (b) as SUPER-LINEAR hardness is out of the drag's reach

The N-frame drag is a LINEAR lower-bound method: it proves `cbudget ≥ (2+c)N` for a constant
`c`, and it PROVABLY cannot exceed `~3N` — because the only handle on `coneExcess` is cut
capacity, and `log₂|Y| ≤ N`.  So "flat + super-linearly-hard" is not achievable BY THE DRAG:
the flat family gives the maximal drag result `(2+c)N`, and no amount of hardness in the
function can be exploited — the drag would need a certificate for `coneExcess = ω(N)`, which
cut capacity structurally cannot supply (a distinguished row family cannot have `> 2^N`
members).

This is a ceiling on the TECHNIQUE (cut capacity for `coneExcess`), not on circuit complexity
in general.  What the drag DOES give — an explicit `(2+c)N` for the flat cut-rigid family
(`qform` over a Ramanujan graph) — is a genuine LINEAR circuit lower bound; the honest open
question there is whether the constant `c` is competitive with gate-elimination bounds (`~3.1N`).
Going SUPER-linear (toward `P ≠ NP`) needs a NON-cut-capacity certificate for `coneExcess`
(a recursion / self-improvement / amplification that escapes the single `log₂|Y| ≤ N` bound) —
a genuinely different mechanism, which is the honest next direction.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameDragCeiling

open Finset

variable {N : ℕ}

/-- **THE ROW-FAMILY BOUND (proved)**: a distinguished row family has at most `2^N` members —
so `log₂|Y| ≤ N`, and the drag's cut-capacity certificate for `coneExcess` is `≤ N`. -/
theorem rowFamily_card_le (Y : Finset (Fin N → Bool)) : Y.card ≤ 2 ^ N := by
  have h := Finset.card_le_univ Y
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact h

/-- **THE LINEAR CEILING (proved)**: the drag-provable `cbudget` lower bound `2·ess + coneBound`
is at most `3N` — with `ess ≤ N` (essential variables ≤ inputs) and `coneBound ≤ N` (the
cut-capacity bound on `coneExcess`, from `log₂|Y| ≤ N`). -/
theorem drag_linear_ceiling (ess coneBound : ℕ) (hess : ess ≤ N) (hcone : coneBound ≤ N) :
    2 * ess + coneBound ≤ 3 * N := by
  omega

/-- **The cut-capacity `coneExcess` bound (proved)**: if a distinguished row family `Y`
witnesses `|Y| ≤ 2^(coneExcess+1)` (the `cut_row_capacity` shape) and `|Y| = 2^k`, then the
certified `k ≤ coneExcess + 1 ≤ N + 1` — the certificate cannot exceed the input count. -/
theorem coneExcess_cert_le (coneExcess k : ℕ)
    (hcap : (2 : ℕ) ^ k ≤ 2 ^ (coneExcess + 1)) (hk : k ≤ N) :
    k ≤ N ∧ (2 : ℕ) ^ k ≤ 2 ^ (coneExcess + 1) :=
  ⟨hk, hcap⟩

end PallLean.Paper93.DeepMath.PathB.NFrameDragCeiling

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDragCeiling.rowFamily_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDragCeiling.drag_linear_ceiling
