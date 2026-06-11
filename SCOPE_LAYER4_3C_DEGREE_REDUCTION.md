# Scope §3-C — the `q`-ary degree reduction (the genuine open core of Layer 4)

This note exists because `SCOPE_LAYER4_MODq_GENERALIZATION.md` §3 flagged the degree-reduction step as
the one part of `MOD_q ∉ AC⁰[p]` that does **not** transfer from the PARITY proof, and the discipline is:
**decide the argument before coding; do not fake the bridge.** Bricks (1) base-change
(`ComputationalDepthLayer4BaseChange`) and (2) `q`-th roots (`ComputationalDepthLayer4RootOfUnity`) are
done and sorry-free; this note is about the part they feed into.

## What Layer 3 actually used (and why it is `q = 2`-only)

Layer 3's collapse (`pm_monomial_reduction` → `every_function_repr` → `dim_bound_on_G`) rests on **one
algebraic fact**: on the `±1` cube the encoding satisfies the **involution** `yᵢ² = 1`
(`pmOne_mul_self`). That, and only that, gives the halving
\[
  \chi_S \;=\; \chi_{\mathrm{univ}} \cdot \chi_{S^c}\qquad(\text{since } yᵢ²=1),
\]
so a high-degree monomial (`|S| > n/2`) becomes `χ_univ` times a **low-degree** complementary monomial
(`|Sᶜ| < n/2`). One low-degree object (`χ_univ`, supplied by the parity circuit's approximant) then
drags the whole function space down to degree `≤ n/2 + Δ`.

**This is intrinsically `q = 2`.** The involution `y² = 1` is exactly "`y` is a square root of `1`", and
`{+1, −1}` are the **2nd** roots of unity. For `q > 2`:

* a Boolean coordinate encoded as `ζ^{xᵢ}` takes only the two values `{1, ζ}`, and
  `(ζ^{xᵢ})² = ζ^{2xᵢ} ∈ {1, ζ²}` is a **third** value — there is **no Boolean involution**;
* the `{0,1}` cube itself has `xᵢ² = xᵢ` (idempotent, *not* an involution), so
  `e_univ · e_{Sᶜ} = e_univ` **absorbs** instead of halving.

So the literal Layer-3 halving has **no `q > 2` analogue**, and reusing `pmSpan_eq_top` /
`pm_monomial_reduction` for general `q` would be a category error. The replacement is genuine new
mathematics (Smolensky 1987, the general-`q` case), **not** a re-instantiation.

## What is reusable verbatim (confirmed)

* **Dimension half.** `dim_bound_on_G`'s skeleton — `finrank (↥G → K) = |G|` (`Module.finrank_pi`, any
  field `K`), the low-degree monomial count, `centralBinom_sq_le`, `lowDegMonomials_card_band_margin` —
  is field-independent. Re-stated over `K = F_{p^{q-1}}` it gives, **unchanged**:
  *if every function on `G` is degree `≤ n/2+Δ`, then `|G| ≤ #{deg ≤ n/2+Δ monomials} < (3/4)·2ⁿ`.*
* **`squarefreeSpan_eq_top`** (the `{0,1}` monomials span `↥cube → K`): field-general (uses only
  `x²=x` + indicators). The general-`q` reduction will use *this* basis, not the `±1` one.
* **Field + root** (brick 2) and **base change** (brick 1): the `F_p` approximant lives over
  `F_{p^{q-1}}` with `ζ` available.

So the **only** missing implication is the analogue of `every_function_repr`:

> **(★)** *Given a degree-`Δ` approximant (over `F_{p^{q-1}}`) for `MOD_q` on a large `G`, every function
> `↥G → F_{p^{q-1}}` agrees on `G` with a polynomial of degree `≤ n/2 + O(Δ)`.*

Everything else on the dimension side already exists or transfers.

## Candidate routes for (★) — with honest status

**Route A — faithful Smolensky general-`q`.** Smolensky (1987) proves (★) without an involution. The
mechanism is *not* monomial-halving; it is a direct count using the `q`-th-root structure: the approximant
makes the weight character `ζ^{#ones}` low-degree on `G`, and a dimension/Schwartz–Zippel argument over
`F_{p^{q-1}}` bounds the functions realisable. **Status: this is the real content and I do not have its
exact reduction identity crisp enough to formalise from memory.** It must be reconstructed carefully from
the source (Smolensky '87; Arora–Barak ch. 14) *before* any Lean code — writing a plausible-looking but
unchecked `have` for the reduction identity would be exactly the kind of fake the discipline forbids.
*This is the honest blocker; treat it as a multi-lemma sub-development, not a single brick.*

**Route B — reduce `MOD_q` to PARITY on a sub-cube.** *Unsound in general.* `MOD_q` does not restrict to
`MOD_2` on any natural sub-structure for `q > 2`; flagged here only to mark it as a trap so it is not
attempted.

**Route C — go through OR / symmetric-function machinery.** Some expositions route the general bound
through "approximate-degree of symmetric functions". Plausible but heavier; deferred unless Route A's
identity proves hard to mechanise.

## Decision

1. **Do not** attempt a capstone or an `every_function_repr`-analogue until Route A's exact reduction
   identity is written down on paper and checked. The combinatorial/field/agreement scaffolding (bricks
   1–2, the reusable dimension half) is ready and waiting; the bottleneck is precisely (★).
2. **Next safe, genuine bricks** that advance Route A without committing to the unproven identity:
   * **(C1) ✓ DONE** (`ComputationalDepthLayer4DimGeneral.sqfSpan_eq_top`) — the squarefree monomials span
     `(Fin n → Bool) → K` over an arbitrary field `K` (verbatim mirror of Layer 3, sorry-free).
   * **(C2) ✓ DONE** (`ComputationalDepthLayer4ModqChar.weightChar_eq_one_iff`) — `weightChar ζ x = 1 ⇔
     q ∣ #ones` for a primitive `q`-th root, connecting the character to the literal `MOD_q` predicate.
   * **(C3) ✓ DONE** (`ComputationalDepthLayer4DimGeneral.dim_contradiction_general`) — the dimension half
     over `K` **as a conditional on (★)**: from `hstar` (= every function on `G` is a `K`-combination of
     low-degree squarefree monomials restricted to `G`, i.e. **(★)** as span membership) + the band margin
     + `|G| ≥ (3/4)·2ⁿ`, derive `False`. `(★)` is an explicit named hypothesis, isolating exactly the open
     content (mirroring how Layer 3 isolated its inputs). Also `dim_bound_general`,
     `finrank_functions_on_G_general`.
3. **Only remaining: (★) itself** — discharge `hstar` over `K = F_{p^{q-1}}` via Route A's reduction
   identity. This is the genuine open mathematics; everything it feeds into is now built and waiting.

## Discipline restated

* (★) is the genuine theorem; it is **not** assumed silently anywhere — it appears (if at all) as an
  explicit, named hypothesis of a conditional statement, never as an unproved `have`.
* No custom axioms; everything sorry-free; Layer 3 untouched.
* Build + `#print axioms` + push per brick.
