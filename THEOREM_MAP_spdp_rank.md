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

## Part C — dynamic / observer-boundary invariants (fixing raw rank's flaw)

Raw `spdpRank` is exponential even for the *easy* `∏Xᵢ` (Part B1), so it does not track hardness.  This part tests
*dynamic* / *restriction-based* refinements.  Key fact throughout: `MOD_q`'s multilinear polynomial is itself an
**affine product** `∏ᵢ(1 + (ω-1)Xᵢ)` (`ComputationalDepthSPDPRestricted.lean`), so it has the *same* exponential raw
rank as `∏Xᵢ` — the two can only be told apart by a *finer* measure.

### C0 — two proved no-gos on accumulation measures

`ComputationalDepthSPDPDynamic.lean` — `spdpRank_add_le` (the genuine `+`-gate subadditivity), and
  `fullProd_dynamicTraceCost_ge`: "max `spdpRank` across a construction trace" is `≥ C(n,κ)` for `∏Xᵢ` (the final
  state is in the trace) — the max-rank dynamic cost **cannot** make `∏Xᵢ` cheap.
`ComputationalDepthSPDPIncremental.lean` — `fullProd_incrementalSum_ge` (per-step increments telescope to `C(n,κ)`)
  and `fullProd_length_mul_maxInc_ge` (bounded increments force super-poly trace length).  Per-step incremental rank
  **also** fails.  ⇒ no rank-*accumulation* measure escapes the exponential final rank.
`ComputationalDepthPcrankTest.lean` — the existing communication `pcrank`: `crank_and_le_two` (`∏Xᵢ` rank `≤ 2`) and
  `crank_modq_le` (`MOD_q` rank `≤ q`) — `pcrank` makes **both low**, failing to separate (`MOD_q` factors across a
  cut, easy for communication though hard for `AC⁰`).

### C1 — the restriction / observer-boundary invariant (the one that separates)

`ComputationalDepthSPDPRestricted.lean` — qualitative: `fullProd_restrict_zero` (`∏Xᵢ` killable by `Xⱼ:=0`) vs
  `modqPoly_restrict_ne_zero` (`MOD_q`'s affine factors never vanish at `0/1`, so it is never killed).

Quantitative engine — `ComputationalDepthAffinePderiv.lean`:
`pderiv_aeval_aff` — **the pderiv-under-affine chain rule `pderiv i (aeval(1+cX) p) = C c · aeval(1+cX)(pderiv i p)`,
  which Mathlib lacks** — plus `iterDerivList_aeval_aff` and `aeval_aff_injective` (`φ = aeval(1+cX)` an automorphism).
`ComputationalDepthAffineProdBound.lean` — `spdpRank_affProd_choose_ge`: `spdpRank κ 0 (∏ᵢ(1+cXᵢ)) ≥ C(n,κ)` (`φ`
  carries the linear independence from the monomials to the affine products).
`ComputationalDepthObserverBoundary.lean` — the invariant:
  `spdpRank_affProd_subset_ge` (visible-slice bound `≥ C(|s|,κ)`), `spdpRank_le_C_mul` (constant factors are free),
  `spdpRank_restrictBoundary_modqPoly_ge` — **`MOD_q` is boundary-robust: `≥ (visible.card).choose κ`** across every
  Boolean boundary; `fullProd_restrictBoundary_zero` — **`∏Xᵢ` is fragile (`= 0`)**.  So the observer-boundary
  invariant separates `MOD_q` from `∏Xᵢ` quantitatively where raw rank and `pcrank` could not.

**N-Frame Book 1 mapping** (`ComputationalDepthBoundaryHardFail.lean` docstring): observer boundary `b` ↦
`ObserverBoundary`; boundary actualization/collapse ↦ `restrictBoundary B p`; boundary robustness ↦
`spdpRank_restrictBoundary_modqPoly_ge`; boundary fragility ↦ `fullProd_restrictBoundary_zero`.  Observer-boundary SPDP
formalizes N-Frame *boundary actualization*: the observer selects a context, and SPDP rank measures what algebraic
structure survives it.

### C2 — but over *arbitrary* boundaries it is NOT a hardness measure (proved on a hard target)

`ComputationalDepthBoundaryHardFail.lean` — `permPoly_restrictRow_zero`: the **permanent** (`VNP`-complete) is killed
  by fixing one row to `0` (`n²−n` variables still visible), because every monomial covers every row.  So over
  *arbitrary* boundaries a genuinely hard target is fragile (`BoundarySPDP = 0`), *like the easy `∏Xᵢ`* — the invariant
  detects *nonvanishing-product structure*, not hardness.

### C3 — the refinement: admissible (minor-preserving) boundaries

A destructive boundary (zero a row) is not an admissible observer context — it destroys the witness/minor structure.
Restricting to **admissible** boundaries repairs this.  Warm-up (`ComputationalDepthBoundaryHardFail.lean`):
  `permPoly_restrictDiagonal_eq` / `permPoly_restrictDiagonal_ne_zero` — fixing the *off-diagonal* to `0` reduces the
  permanent to `∏ᵢ X_{i,i}` (nonzero, SPDP rank `≥ C(n,κ)`) — the `k=n` diagonal case.

**The general `Permₙ ↦ Permₖ` reduction** — `ComputationalDepthAdmissibleBoundary.lean`.  For an embedding
`e : Fin k ↪ Fin n` (the visible `k×k` minor), the block boundary `blockBoundary e` keeps `X_{i,j}` when both `i,j`
are in the block `B = range e` and fixes `1`/`0` on/off the diagonal outside:
  `permPoly_blockBoundary_eq` — `aeval (blockBoundary e) Permₙ = subPermPoly e`, the block sub-permanent
        `∑_{τ∈Sₖ} ∏ₐ X_{e a, e(τ a)}`.  Proof: only permutations mapping `B` into itself survive (a permutation crossing
        out of `B` hits a fixed `0`); these are exactly the `extendDomain`s of `Sₖ` (`Equiv.Perm.extendDomain`), and the
        surviving sum reindexes bijectively onto `Permₖ` (`Finset.sum_bij`, `extendDomainHom_injective`).
  `subPermPoly_eq_rename` — `subPermPoly e = aeval (X_{a,b} ↦ X_{e a, e b}) Permₖ`: it is literally `Permₖ` reindexed
        into the block, so this is a genuine `Permₙ ↦ Permₖ` reduction.
  `permPoly_ne_zero` / `subPermPoly_ne_zero` / `permPoly_blockBoundary_ne_zero` — evaluate at the identity matrix
        (`perm(I)=1`): the permanent, and its block reduction, are nonzero.  So the permanent **survives** every
        admissible block boundary, reducing functorially `Permₙ ↦ Permₖ`.

So the correct N-Frame object is `BoundarySPDP` over *admissible* boundaries, under which the hardest object we have (the
`VNP`-complete permanent) is robust — exactly the structure a hardness-aimed invariant needs, and what *destructive*
boundaries destroy.

### C4 — the `A3` rank lower bound over the block family

`ComputationalDepthBlockPermRankLB.lean` supplies the quantitative half — a genuine SPDP-rank *lower* bound for the
restricted permanent, **uniform over the whole admissible block family**:
  `spdpRank_subPermPoly_flat_ge` — for every embedding `e : Fin k ↪ Fin n`, the (flattened) block permanent
        `subPermPoly e` has `spdpRank 1 0 ≥ k²`.
  `spdpRank_renamePerm_ge` — the abstract core: for any injective relabelling `ψ`, `spdpRank 1 0 (rename ψ Permₖ) ≥ k²`.
Mechanism: `pderiv_permPoly` — the permanent's `k²` first partials are the minors `∂_{(a,b)} Permₖ = minorₐᵦ`;
`minorPoly_support_key` — every monomial of `minorₐᵦ` uses row-set `univ.erase a` and col-set `univ.erase b`, so distinct
`(a,b)` give pairwise-disjoint supports; `linearIndependent_of_key` (reusable) — disjoint supports ⟹ linear independence;
hence the order-`1` SPDP subspace has dimension `≥ k²`.  Uniform over `e` because `subPermPoly e = rename ψₑ Permₖ` and
injective renaming preserves derivatives (`pderiv_rename`) and independence (`rename_injective`).

This is `k²` (from `κ = 1`); the exponential `κ = k/2` bound `C(k,κ)²` (iterated derivatives → complementary
sub-permanents, same disjoint-support argument) is the natural extension.  Crucially this is the *easy* side: a large
lower bound on a *hard* polynomial's rank does **not** separate classes.  Making a hard target admissibly-robust *and*
matching it with the *upper* bound (small circuits ⟹ small rank) is the barriered `A3`/wall — the lower bound here is
real and uniform, the upper bound is the open problem.

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

Part C reaches the same wall from the *refinement* side: every accumulation measure inherits `∏Xᵢ`'s exponential rank
(C0, proved), and the one measure that separates `MOD_q` from `∏Xᵢ` — restriction/boundary robustness (C1, proved) —
separates by *nonvanishing-product structure*, not hardness, so it classifies the hard permanent as fragile (C2,
proved).  Making a genuinely hard target boundary-robust *and* proving its rank stays high **is** the barriered `A3`
hard-survival — the same wall.  Every step across both parts is proved; the wall is located, not crossed.
