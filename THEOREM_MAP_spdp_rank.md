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

This is `k²` (from `κ = 1`); the exponential version follows in C5.

### C5 — the exponential `C(k,κ)²` bound

`ComputationalDepthBlockPermRankExp.lean` upgrades C4 to the full order-`κ` bound:
  `spdpRank_subPermPoly_flat_choose_ge` — for every embedding `e`, `spdpRank κ 0 (subPermPoly e) ≥ C(k,κ)²`
        — **exponential** (`≈ 4^k/k`) at `κ = k/2`, uniform over the whole block family.
  `spdpRank_renamePerm_choose_ge` — abstract core: `spdpRank κ 0 (rename ψ Permₖ) ≥ C(k,κ)²` for injective `ψ`.
Mechanism: the order-`κ` derivative of the permanent along a partial-permutation matching a `κ`-row-set `R` to a
`κ`-col-set `C` is the **complementary sub-permanent** on `(Rᶜ,Cᶜ)` (`blockDeriv`, `blockDeriv_eq_sum` via the iterated
`iterPD` + `iterPD_monomial`); every monomial uses row-set `Rᶜ`, col-set `Cᶜ` (`blockDeriv_support_key`), nonzero via
the explicit matching permutation `matchPerm` (`blockDeriv_ne_zero`); the `C(k,κ)²` choices of `(R,C)` give
pairwise-disjoint supports ⟹ linearly independent (`linearIndependent_of_key`).

Crucially this is the *easy* side: a large lower bound on a *hard* polynomial's rank does **not** separate classes.
The matching *upper* bound is C6.

### C6 — the upper-bound half of the wall (restricted, proved)

`ComputationalDepthSPDPProductUB.lean` (namespace `SPDPUpperBound`) proves the honest, provable half of the wall: a
polynomial from a *shallow/product* model has **small** SPDP rank.
  `spdpSubspace_prod_le` — the core: for `f = ∏_{j=1}^m Q_j` with `deg Q_j ≤ t`, `spdpSubspace κ 0 f ≤ prodDerivSpace Q t κ`,
        where `prodDerivSpace Q t κ = span{(∏_{j∉J}Q_j)·M : |J|≤κ, deg M ≤ κt}`.  Mechanism: each derivative touches
        `≤ κ` of the `m` factors, so `∂_S(∏Q) ∈ span{(∏ of m−|J| factors)·M : |J|≤κ}` — proved by induction on the
        derivative order (`pderiv_mem_prodDerivSpace`: one derivative raises the deletion-count by one, via the finset
        product rule `pderiv_prod`), from `∏Q ∈ prodDerivSpace 0`.
  `spdpRank_prod_le` — hence `spdpRank κ 0 (∏Q_j) ≤ finrank(prodDerivSpace Q t κ)`, a space spanned by
        `(#{J:|J|≤κ})·(#monomials of degree ≤ κt)` generators — **small** for shallow circuits.
  `spdpRank_sum_le` — subadditivity over a sum (the depth-`4` `∑` layer): `spdpRank κ ℓ (∑_i f_i) ≤ ∑_i spdpRank κ ℓ (f_i)`,
        so a depth-`4` circuit `∑_{i=1}^s ∏_j Q_{ij}` has `spdpRank ≤ s·(single-product bound)`.

### C7 — the two halves meet: the concrete numerical separation

`ComputationalDepthSPDPWall.lean` (namespace `SPDPWall`) makes the lower/upper meeting fully quantitative.  Concrete
`finrank` bound first (`ComputationalDepthSPDPProductUB.lean`):
  `spdpRank_prod_le_card` — `spdpRank κ 0 (∏_{j=1}^m Q_j) ≤ (#{J⊆[m]:|J|≤κ}) · finrank(restrictTotalDegree κt)`
        (via `prodDerivSpace ≤ Finset.sup of pieces` (`prodDerivSpace_le_sup`) + `finrank_finset_sup_le` +
        `Submodule.finrank_map_le`) — an explicit, small number.
Then the separation:
  `permanent_depth4_bound` — if `Permₖ` (flattened by injective `ψ`) `= ∑_{i<s} ∏_j Q_{ij}` (depth-`4`, `≤ mm` factors,
        degree `≤ t`), then `C(k,κ)² ≤ s · (#{J:|J|≤κ}) · (#monomials of degree ≤ κt)`.  (C5 lower ∘ C6 subadditivity
        ∘ the concrete C7 per-product bound.)
  `permanent_no_small_depth4` — contrapositive: if that RHS is `< C(k,κ)²`, the permanent has **no** such circuit.

At `κ = k/2` the threshold `C(k,κ)² ≈ 4ᵏ/k` is exponential while the RHS is polynomial in `s`, `#J ≤ 2^{mm}`, and
`#monomials ≤ binom(N+κt, N)` — so a shallow circuit provably cannot compute the permanent.  This is the GKKS-style
restricted separation, fully quantitative.

**Honest scope.**  Restricted (depth-`4`, bounded bottom fan-in), **not** `P ≠ NP` or `NEXP ⊄ ACC⁰`.  The *full* wall —
"every poly-size circuit ⟹ small SPDP rank" — is false / `P`-vs-`NP`-strength (SPDP rank does not upper-bound general
circuits).  C1–C7 prove exactly the honest, provable object: lower bound (exponential, uniform), upper bound
(shallow/product), and their concrete numerical meeting point.  The general wall remains the barrier.

### C8 — toward ACC: an ACC-normal-form bound stable under admissible boundaries

`ComputationalDepthACCNormalForm.lean` (namespace `SPDPUpperBound`) takes the honest reachable step toward `ACC` — a
compression theorem for a *specific* ACC-like normal form (the Beigel–Tarui inner layer), **not** all `ACC⁰`.
  `spdpRank_sumProd_le` — for `f = ∑_{i<s} ∏_{j<m} Q_{ij}` with `deg Q_{ij} ≤ t`,
        `spdpRank κ 0 f ≤ s·(#{J:|J|≤κ})·finrank(restrictTotalDegree κt)`.
  `spdpRank_aevalBoundary_sumProd_le` — **the functorial compression**: an admissible boundary is a ring endomorphism
        `aeval g` with `deg (g v) ≤ 1` (keep each variable or fix it to a constant); it commutes with `∑`/`∏`
        (`map_sum`, `map_prod`) and is degree-non-increasing (`totalDegree_aeval_le_of_deg_le_one`), so it carries the
        normal form to another normal form with the *same* budget — the SPDP bound is preserved.
  `restrictBdry` / `spdpRank_restrictBdry_sumProd_le` — the concrete sub-cube boundary
        `v ↦ if v ∈ visible then X v else C (assign v)` and its normal-form bound.

**Honest scope.**  This covers the BT `∑∏` inner layer and shows admissible boundaries keep it in the product-derivative
space.  It does **not** cover full `ACC⁰`/`ACC⁰[p]`: the symmetric/`MOD` composition `P` in `f = P(∑∏)` lifts the bottom
degree to `t = polylog`, and `finrank(restrictTotalDegree κt)` then overtakes `C(k,κ)²` at the `κ` where it bites (the
C-arc barrier).  Whether known `ACC⁰[p]` machinery (Razborov–Smolensky) gives a controlled-blowup normal form of this
shape is the separate open question — *not* claimed here.

### C9 — approximation-aware: agreement on the cube, and why `spdpRank` is the wrong measure

`ComputationalDepthSPDPApprox.lean` (namespace `SPDPApprox`).  Razborov–Smolensky delivers *agreement on a large
fraction of the Boolean cube*, not a polynomial identity.  The honest consequences:
  `spdpRank_normalForm_add_error_le` (positive) — splitting off an ACC normal form `h = ∑∏Q` localises the residual:
        `spdpRank κ 0 f ≤ s·(#{J:|J|≤κ})·finrank(restrictTotalDegree κt) + spdpRank κ 0 (f−h)` (subadditivity + C8).
  `spdpRank_not_cubeInvariant` (obstruction) — `0` and `X₀²−X₀` agree on the entire cube yet
        `spdpRank 0 0 0 = 0 < 1 ≤ spdpRank 0 0 (X₀²−X₀)` (`spdpRank_zero`, `one_le_spdpRank_of_ne_zero`,
        `sq_sub_ne_zero`).  So a cube-vanishing error carries arbitrary SPDP rank.

Conclusion: an RS-style approximation pins `f` down only on the cube, and the error `e = f−h` (living in the ideal
`(Xᵢ²−Xᵢ)`) can vanish on the whole cube while carrying arbitrary `spdpRank` — so agreement does **not** bound
`spdpRank(f)`.  This is precisely why the polynomial method uses a **cube-invariant** measure — the multilinear
representative / low-degree approximant dimension (this repo's `NFrameComplexity` / `sqfSpan`, effective-dimension
deficit) — not raw shifted-partial rank.  The honest bridge from `∑∏` normal forms to `ACC⁰[p]` runs through that
cube-invariant layer — built in C10.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.

### C10 — the cube-invariant bridge: `∑∏` normal forms have low N-Frame complexity

`ComputationalDepthNFrameProductBridge.lean` (namespace `NFrameACC0`) closes the loop C9 opened: the `∑∏` upper-bound
machinery feeds the repo's **cube-invariant** `NFrameComplexity` (minimal multilinear-representation degree), the measure
the RS lower bound (`parity_function_lower_bound`, effective-dim deficit) is stated against.
  `boolFn p` — the Boolean cube-function `x ↦ eval (x as 0/1) p`.
  `boolFn_mem_sqfSpan` — on the cube `Xᵢ²=Xᵢ`, so a total-degree-`≤D` polynomial's cube-function is a combination of
        squarefree monomials of degree `≤D`: `boolFn p ∈ span (sqfGens F n D)` (each monomial `∏Xᵢ^{dᵢ}` collapses to the
        squarefree `∏_{i∈supp d}Xᵢ`, degree `|supp d| ≤ deg d`).
  `nframeComplexity_boolFn_le` — hence `NFrameComplexity F (boolFn p) ≤ totalDegree p`.
  `nframeComplexity_boolFn_sumProd_le` — **the bridge**: a shallow `∑_{i<s}∏_{j<m} Q_{ij}` (`deg Q_{ij} ≤ t`) has
        `NFrameComplexity F (boolFn (∑∏Q)) ≤ m·t` — a *cube-invariant* smallness statement, unlike `spdpRank`.

So the C8 normal form has **low N-Frame complexity** on the cube.  Combined with a hard function's *high* N-Frame
complexity (the repo's RS layer), this is the honest, cube-correct separation route: my `∑∏` upper-bound arc now feeds
the existing RS lower-bound layer *through the right (cube-invariant) measure*.  Closed in C11.  Not `NEXP ⊄ ACC⁰`, not
`P ≠ NP`.

### C11 — separation closed: `MOD_q` is not a shallow `∑∏` on the cube

`ComputationalDepthNFrameSeparation.lean` (namespace `NFrameACC0`) meets the two cube-invariant sides:
* **Low (C10)** `nframeComplexity_boolFn_sumProd_le` — shallow `∑∏` ⟹ `NFrameComplexity (boolFn ∑∏Q) ≤ m·t`.
* **High (repo)** `nframeComplexity_omegaFn_univ_ge` — `MOD_q` (`omegaFn ω univ`, `ω` primitive `q`-th root over `F`) has
  `NFrameComplexity ≥ n − n/2 = ⌈n/2⌉`.
Combined:
  `hard_not_shallow_sumProd` — any `h` with `m·t < NFrameComplexity F h` satisfies `h ≠ boolFn (∑_{i<s} ∏_{j<m} Q_{ij})`.
  `modq_not_shallow_sumProd` — for `m·t < ⌈n/2⌉`, `MOD_q` is **not** computed on the cube by any shallow `∑∏` of
        degree-`≤t` factors.

The two-sided N-Frame skeleton is closed for the `∑∏` (Beigel–Tarui inner-layer) model, using only the *cube-invariant*
measure C9 identified as the right one.  Honest scope: `MOD_q` over `char ≠ q` (Smolensky regime); separation is against
*exact* cube-computation by shallow `∑∏`, `m·t < ⌈n/2⌉`.  The full BT shape (with the `SYM`/composite-`MOD` outer layer)
is handled in C12.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.

### C12 — the low side extended to full ACC⁰: the SYM / composite-MOD outer layer

`ComputationalDepthNFrameSymLayer.lean` (namespace `NFrameACC0`).  Beigel–Tarui: every `ACC⁰` function has the shape
`f = P(∑_{i<s}∏_{j<m} Q_{ij})` — a symmetric/composite-`MOD` outer gate arithmetised as a *univariate* `P` over `F`, over
the `∑∏` inner layer.  The low side extends to this full shape:
  `totalDegree_polyAeval_le` — `totalDegree(P(h)) ≤ deg P · totalDegree h`.
  `nframeComplexity_boolFn_symSumProd_le` — **extended low side**: `NFrameComplexity (boolFn (P(∑∏Q))) ≤ deg P · m · t`.
  `symSumProd_degree_lb_of_modq` — **the barrier quantified**: if `MOD_q = P(∑∏Q)` on the cube then `deg P · m · t ≥ ⌈n/2⌉`.

This *covers full `ACC⁰`* structurally (every ACC⁰ function is some `P(∑∏)`), but the bound carries the factor `deg P` =
the arithmetised outer-gate degree.  For `AC⁰[p]` a `MOD_p` gate is degree `1` over `F_p` (bound bites); for genuine
composite `MOD_m` the arithmetisation has large (quasi-poly) degree, so `deg P · m · t` is too weak to beat a hard
function's linear N-Frame complexity.  `symSumProd_degree_lb_of_modq` pins this: representing `MOD_q` as `SYM∘∑∏` forces
`deg P · m · t ≥ ⌈n/2⌉` — the composite-MOD cost is *exactly* the `deg P` factor.  So the low side does extend to full
`ACC⁰`, but not to a *small* bound — because `MOD_q ∈ ACC⁰` has high N-Frame complexity (C11).  This is the quantitative
anatomy of the composite-MOD barrier, not a crossing of it.  `deg P` itself is bounded in C13.  Not `NEXP ⊄ ACC⁰`, not
`P ≠ NP`.

### C13 — bounding `deg P` for the composite-MOD gate

`ComputationalDepthNFrameSymDegree.lean` (namespace `NFrameACC0`).  A composite-`MOD` gate is *symmetric* — a function of
the *sum* of the `s` products it reads, so `g : {0,…,s} → F`.  Over a field where the `s+1` nodes `0,…,s` are distinct
(`char 0` or `char > s`), Lagrange interpolation bounds the arithmetisation degree by the fan-in:
  `natDegree_symGateArith_le` — `deg (symGateArith g) ≤ N` (`symGateArith g = Lagrange.interpolate` on nodes `0,…,N`).
  `eval_symGateArith` — the arithmetisation agrees with the gate on `{0,…,N}`.
  `natDegree_modmGate_arith_le` — the concrete `MOD_m` gate: `deg ≤ N`.
  `modq_BTsize_lb` — feeding `deg P ≤ s` into C12: if `MOD_q = P(∑∏Q)` with `P` a symmetric gate of fan-in `≤ s`, then
        `s · m · t ≥ ⌈n/2⌉` — a size lower bound in the raw circuit parameters (`s` products, `m` factors, degree `t`).

**The composite-MOD subtlety, kept honest.**  `deg P ≤ s` needs the `s+1` nodes distinct (`char > s`).  Over `F_p` with
`p ≤ s` they wrap, and every function `F_p → F_p` is degree `≤ p−1` — but a genuine composite `MOD_m` (`m` coprime to
`p`) is then *not* a function of `∑ mod p`, so no low-degree `P(∑∏)` over `F_p` represents it.  That missing
arithmetisation *is* the composite-MOD barrier; C13 bounds `deg P` exactly in the regime where the gate is a low-degree
symmetric polynomial (`char > s`).  The small-characteristic composite case is handled in C14.  Not `NEXP ⊄ ACC⁰`, not
`P ≠ NP`.

### C14 — the small-characteristic composite-MOD case: the arithmetisation does not exist

`ComputationalDepthNFrameCompositeMOD.lean` (namespace `NFrameACC0`).  In the remaining regime — `char = ℓ ≤ s`,
composite `MOD_m` — the honest resolution is a **non-existence** theorem.  Over characteristic `ℓ`, the `F`-sum of `c`
Boolean products is `(c : F) = c mod ℓ`: it only tracks the count mod `ℓ`, while `MOD_m` needs it mod `m`.
  `modmGate_not_evalPoly_of_char` — if `(ℓ : F) = 0` and `m ∤ ℓ`, there is **no** univariate `P` with
        `[c ≡ 0 mod m] = eval (c : F) P` for all counts `c` (counts `0` and `ℓ` collide in `F` but differ under `MOD_m`).
  `modmGate_not_evalPoly_of_ringChar` — same via `ringChar F`.

So over `F_ℓ`, a composite `MOD_m` (`m ∤ ℓ`) has **no** `P(∑∏)` arithmetisation — not merely high-degree, it does not
exist.  With C13 this splits the outer layer completely: `char > fan-in ⟹ deg P ≤ s` (method works, `modq_BTsize_lb`);
`char ≤ fan-in`, composite `MOD_m` ⟹ no `P` (method over `F_ℓ` provably fails).  The escape (C11's root-of-unity
`omegaFn = ω^{∑}`, tracking the count mod `q` without casting into `F_ℓ`) works for **prime-power** modulus only; a
genuine multi-prime composite `m` needs one root of unity per prime-power factor and the combined object keeps high
N-Frame complexity — the standing `MOD_6`-type barrier, analysed in C15.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.

### C15 — the multi-prime composite barrier: the char-matching modulus is a blind spot

`ComputationalDepthNFrameTwoFields.lean` (namespace `NFrameACC0`).  A genuine multi-prime `m = p₁ᵉ¹⋯` (`MOD_6`) needs one
root of unity per prime-power factor and the single-field method fails.  The structural reason — formalised — is the
**two-fields blind spot**: over a field of characteristic `ℓ`, the modulus *matching* the characteristic is **low**
N-Frame complexity, while a coprime modulus is high.
  `charModFn` — `MOD_ℓ`, the Boolean `[∑ xᵢ ≡ 0 in F]`.
  `charModFn_eq_boolFn` — Fermat: on the cube `[∑ = 0 in F] = 1 − (∑Xᵢ)^{|F|−1}` (degree `|F|−1`).
  `nframeComplexity_charModFn_le` — hence `NFrameComplexity (MOD_ℓ) ≤ |F| − 1` (LOW).
  `two_fields_blindspot` — over `F`, `NFrameComplexity (MOD_ℓ) < NFrameComplexity (MOD_q)` (coprime `MOD_q`, C11) once
        `|F| − 1 < ⌈n/2⌉`.

So for a `MOD_6` circuit (`MOD_2` and `MOD_3` gates): over `F_2` the `MOD_2` gates are low-degree (invisible to the `F_2`
argument) while `MOD_3` is high; over `F_3`, the reverse.  **No single field makes all moduli of a multi-prime circuit
hard** — each field has a blind spot at its own characteristic.  That is exactly why the single-field polynomial method
cannot prove multi-prime composite `MOD` lower bounds, and why `MOD_6` is open.  C15 formalises the obstruction (the
char-matching modulus is a genuine low-complexity blind spot, from Fermat), not a crossing.  The multi-field route is
analysed in C16.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.

### C16 — the multi-field / CRT route: obstruction, not a crossing (open problem)

`ComputationalDepthNFrameMultiFieldObstruction.lean` (namespace `NFrameACC0`).  **Crossing the multi-prime barrier is
the open problem** (`MOD_6`/`ACC⁰[6]`); no known polynomial (single- or multi-field) argument does it, and this file
does **not** claim one — it isolates why the natural multi-field route fails.

The multi-field/CRT response to C14–C15: combine characteristics.  By CRT `MOD_6 = ([·≡0 mod 2],[·≡0 mod 3])`
arithmetises over the *product ring* `ZMod 6 ≅ F_2 × F_3` — recovering the arithmetisation C14 lacked over each single
field.  But the N-Frame lower bound requires a **field** (`NFrameComplexity` is a `Module.finrank` of a span — linear
independence over a field), and the CRT object is not one:
  `zmod6_not_isField` — `¬ IsField (ZMod 6)` (`2·3 = 0`, `2,3 ≠ 0`: zero divisors).
  `zmod_not_isField_of_zero_divisors` — the general reason: the CRT product ring always has zero divisors.

So the route trades gaps: **`F_ℓ` gives the field but not the arithmetisation (C14); `ZMod 6` gives the arithmetisation
but not the field (C16).** Neither supports both the arithmetisation *and* the field-based dimension lower bound at once
— the precise technical heart of why the polynomial method does not prove multi-prime composite `MOD` lower bounds.
Crossing it genuinely needs a technique that is *not* a field-linear-algebra dimension count on one characteristic —
Williams' algorithmic `NEXP ⊄ ACC⁰` route, or something new.  Not built here; not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.

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

---

## Part D — the algorithmic pivot (past the `MOD_6` wall)

The polynomial-method arc (C1–C16) reached the real `MOD_6` wall: no single field makes every modulus of a multi-prime
circuit hard (C15), and the CRT product ring where the arithmetisation exists is not a field (C16).  **Williams'
algorithmic route bypasses this** — it needs a *nontrivial SAT algorithm* for `ACC⁰`, not a single hard field.
`ComputationalDepthNFrameFastSAT.lean` (namespace `NFrameFastSAT`) pivots N-Frame from a *degree* certificate to a
*compression / algorithmic* certificate, feeding the repo's Williams meta-theorem:
  `NFrameProgram` / `FastSATModel` — a compact N-Frame DAG/DP representation deciding SAT by count-cell search, within a
        `2^{n−budget}` budget (fast counting, not low degree).
  `fastSATModel_savings` — proved: the model delivers Williams savings `2^budget·work ≤ 2^n`.
  `nframe_fastSAT_gives_separation` — proved glue (`[propext]` only, no `sorryAx`): an N-Frame fast-SAT model for `ACC⁰`
        + the two named classical sockets (`EasyWitnessCollapse`, `NondetTimeHierarchy`, Williams 2011) ⇒ `NEXP ⊄ ACC⁰`.
        **Conditional** on the fast-SAT model and the sockets — a schema, not an unconditional separation.
  `toyModel` / `toy_speedup` — non-vacuity: the interface is inhabitable.

**The `SYM∘AND` rung (real instance)** — `ComputationalDepthNFrameFastSATSymAnd.lean`.  The toy is replaced by a real
proved circuit class: the `SYM∘AND` bounded-degree family (`SymAndCircuit n D`: `m` injective monomial-`AND` gates of
degree `≤D` under a symmetric top).
  `symAnd_fastSATModel` — proved `FastSATModel` for `SymAndCircuit`, in the regime where the quasipolynomial gate count
        fits the budget `2^{n−k}`.  `correct` is `observed_sat_iff` (the count-cell search decides SAT *exactly*, not
        just the work count); `work_le` is `fastSatWork_le_of_degree` ∘ the fit hypothesis.
  `symAnd_nframe_fastSAT_savings` / `symAnd_nframe_fastSATSpeedup` — the savings `2^k·fastSatWork m ≤ 2^n` and the
        speedup Prop, *through the interface*, for the real family.
  Ladder: `toy → `**`SYM∘AND`**` → BT normal form → ACC⁰ → Williams fires`.  This is the bounded-degree rung — genuinely
        proved (correctness + quasipoly cell count + savings), now faithfully inhabiting the interface.  Next rungs: the
        BT `P(∑∏)` normal form (explicit parameter blowup), then recursive depth / composite-`MOD`.

**The BT normal-form rung (general `SYM∘AND`)** — `ComputationalDepthNFrameFastSATBT.lean`.  Generalises from
monomial-`AND` to the full BT shape: an arbitrary `SYM∘AND` circuit bounded by a size budget.
  `BTCircuit n size` — `m ≤ size` arbitrary Boolean sub-gates under a symmetric top `h` (the full BT layer).
  `bt_fastSATModel` — proved `FastSATModel` for `BTCircuit`, budget `k`, when `size + 1 ≤ 2^{n−k}`; correctness
        (`observed_sat_iff`) and count-cell work hold for *any* sub-gates.  `bt_nframe_fastSAT_savings` /
        `bt_nframe_fastSATSpeedup` follow.
  `SymAndCircuit.toBT` / `btSatOf_toBT` — the previous rung embeds: a degree-`≤D` monomial-`AND` circuit is a `BTCircuit`
        of size `∑_{i≤D}C(n,i)`, SAT-preserving.
  `symAnd_fastSATSpeedup_quasipoly` — **explicit parameter blowup**: budget as the BT quasipolynomial
        `(D+1)·2^{D·⌈log n⌉}+1 ≤ 2^{n−k}` — `D` polylog ⇒ `2^{o(n)}` ⇒ `k = Ω(n)` (the Williams margin).
  Next rung: compile arbitrary constant-depth `ACC⁰` (composite `MOD`, depth `>1`) *into* this BT normal form with
        quasipolynomial size — the classical YBT theorem, the hard structural step (open socket).

**The YBT-compiler interface (last rung, stated precisely)** — `ComputationalDepthNFrameYBTCompiler.lean`.
  `YBTCompiler n Circuit evalC` — the interface: `exact : evalC C = symEval (gates C) (top C)` (compiles to *exact*
        `SYM∘AND`) with `size_fit : size C + 1 ≤ 2^{n−budget}` (size within the fast-SAT budget).  Instantiating it for a
        circuit class *is* providing that class's Yao–Beigel–Tarui normal form.
  `ybtCompiler_fastSATModel` — **the bridge (proved)**: a `YBTCompiler` yields a `FastSATModel` (`correct` from
        `observed_sat_iff`, `work_le` from `size_fit`); `ybtCompiler_fastSATSpeedup` gives the speedup Prop.  Everything
        downstream fires — so the whole ladder is proved *conditional on the compiler*.
  `btYBTCompiler` — non-vacuity: the BT rung is trivially a `YBTCompiler` (already `SYM∘AND`).
  **Open, stated exactly**: a `YBTCompiler (ACC0Circuit n) eval` for arbitrary `ACC⁰` (composite `MOD`, depth `>1`) is
        the classical YBT theorem with quasipoly size (the corpus's `HasExactSymAndForm` / `MixedACCDepthReductionSocket`)
        — dischargeable for depth-`2` / prime-power `MOD`, open for general composite.  The composite-`MOD` barrier is now
        localised to *one* structure instance; the fast-SAT machinery is proved.

This bypasses the `MOD_6` wall because the claim is *algorithmic* (fast #SAT via a compact representation), not
"`MOD_6` is hard over a field" — so the C15/C16 obstruction does not apply.  Honest scope: the deep content
(easy-witness/IKW collapse, nondeterministic time hierarchy) are named classical sockets, **not** proved here; building
an actual nontrivial N-Frame fast-SAT model for arbitrary `ACC⁰` is the open algorithmic target the interface is meant
to be instantiated with.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
