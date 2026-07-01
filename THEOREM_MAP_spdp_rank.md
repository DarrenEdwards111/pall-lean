# SPDP-rank arc: theorem map (bridge + concrete lower bounds)

Branch `razborov-recoverRho-wip`. This arc works with the repo's literal shifted-partial-derivative rank
`SPDP.spdpRank κ ℓ p = Module.finrank F (span{ m·∂_S p : |S|=κ, deg m ≤ ℓ })` (`PallLean/SPDPDefs.lean`, namespace
`SPDP`).  It has two parts: a **safe-direction bridge** (low degree ⇒ bounded rank) tying `spdpRank` to the N-Frame
proxy, and genuine **lower bounds** for concrete polynomial families.  Every theorem below is clean
(`[propext, Classical.choice, Quot.sound]`, no `sorry`, no bespoke axioms).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  The one wall is stated at the end.

---

## Part A — degree caps `spdpRank` (safe direction)

`ComputationalDepthNFrameSPDPBridge.lean` (namespace `NFrameSPDPBridge`).

`pderiv_totalDegree_le`  — `totalDegree(∂ᵢ p) ≤ totalDegree p` (differentiation does not raise degree; Mathlib lacks
  this — proved from `pderiv_monomial` + the exponent-degree monotonicity `degSub_le`).
`iterDerivList_totalDegree_le`  — the iterated version.
`spdpSubspace_le_restrictTotalDegree`  — `spdpSubspace κ ℓ p ≤ restrictTotalDegree (Fin n) F (ℓ + totalDegree p)`
  (each generator `m·∂_S p` has degree `≤ deg m + deg(∂_S p) ≤ ℓ + deg p`).
`spdpRank_le_of_totalDegree_le`  — `totalDegree p ≤ D ⇒ spdpRank κ ℓ p ≤ finrank(restrictTotalDegree (ℓ + D))`.

This is reused throughout the lower bounds to get **finite-dimensionality** of `spdpSubspace` (via `Module.Finite` of
`restrictTotalDegree`), which `Submodule.finrank_mono` needs.  Together with `…NFrameMlPoly` and `…NFrameDegreeChar`
it links `NFrameComplexity f` (= minimal multilinear degree) to `spdpRank` — see `THEOREM_MAP_nframe_spdp.md`.

---

## Part B — concrete SPDP-rank lower bounds

Shared kernel — `ComputationalDepthSPDPFullProdLB.lean` (namespace `SPDPLowerBound`):

`prodX_eq_monomial`  — `∏_{i∈s} Xᵢ = monomial (indicator s) 1`.
`pderiv_prodX`  — `∂ₖ(∏_{i∈s} Xᵢ) = ∏_{i∈s.erase k} Xᵢ` for `k ∈ s` (differentiation removes one factor).
`iterDeriv_prodX`  — `∂_L(∏_{i∈s} Xᵢ) = ∏_{i∈s∖L} Xᵢ` for nodup `L ⊆ s` (induction from `pderiv_prodX`).

### B1 — the full product (single monomial)

`spdpRank_fullProd_ge`  — `n ≤ spdpRank 1 0 (∏ᵢ Xᵢ)`.  The `n` first-order derivatives are distinct monomials.
`spdpRank_fullProd_choose_ge`  — `C(n, κ) ≤ spdpRank κ 0 (∏ᵢ Xᵢ)`.  **Exponential** (`≈ 2ⁿ/√n`) at `κ = n/2`: the
  `C(n,κ)` complement monomials (one per `κ`-subset) are linearly independent (`basisMonomials`, `compl_injective`),
  and count `C(n,κ)` via `Fintype.card_finset_len`.

### B2 — a determinant-like sum of products

`ComputationalDepthSPDPDeterminantLike.lean` (namespace `SPDPLowerBound`).  New ingredient — **off-support
differentiation vanishes**:

`pderiv_prodX_zero`  — `k ∉ s ⇒ ∂ₖ(∏_{i∈s} Xᵢ) = 0`.
`iterDerivList_zero` / `iterDerivList_add`  — the iterated derivative is additive and kills `0`.
`iterDeriv_prodX_vanish`  — `∂_U(∏_{i∈t} Xᵢ) = 0` when `U` is nonempty and `U ∩ t = ∅`.

`spdpRank_twoBlock_ge`  — for `1 ≤ κ < |s|`,
      `spdpRank κ 0 (∏_{i∈s} Xᵢ + ∏_{i∈sᶜ} Xᵢ) ≥ C(|s|, κ) + C(|sᶜ|, κ)`.
  A **sum of products** (the determinant/permanent *shape*).  A `κ`-order derivative picks out the one term whose
  support it hits (the other vanishes), giving a complement monomial; the `s`-block and `sᶜ`-block monomials have
  disjoint supports, so the exponent map (`Sum.elim` over the two `powersetCard`s) is injective and the ranks **add** —
  the sum of products has strictly more SPDP rank than either product alone.

---

## The wall (open / barriered — NOT crossed, NOT faked)

All of Part B is for **concrete, easy** families (the full product; a sum of products with **disjoint** variable
supports — the read-once / block-diagonal case).  These are genuine SPDP-rank lower bounds but do **not** separate
complexity classes.

The wall is an SPDP-rank **lower bound for an explicit *hard* family** — e.g. the real determinant / permanent, whose
`n!` monomials **overlap** on `n²` variables (the `C(n,κ)²`-style bound), used against a function that is provably
hard (`A3` hard-survival).  That is barriered short of `P/poly`, audited as assumed-not-derived in
`ComputationalDepthSPDPFeatureProjection.lean` / `ComputationalDepthNFrameHypercubeConstraint.lean`.

The honest arc of this direction: single monomial (`≥ C(n,κ)`, exponential) → sum of *disjoint* products (ranks add,
determinant shape) → the *overlapping* determinant (the wall).  Each proved step is a genuine, from-scratch SPDP-rank
lower bound; the last step is the open problem itself, and is left as such.
