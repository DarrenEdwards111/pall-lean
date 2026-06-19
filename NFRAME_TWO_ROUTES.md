# N-Frame: the two routes to `ACC⁰` separation — anatomy and frontier

This note synthesizes the N-Frame account of the `ACC⁰` separation problem into **two routes**, distinguished by the
*characteristic* of the observer, and pins the genuinely-open frontier.  Everything referenced is machine-checked in
`PallLean/Paper93/DeepMath/PathB/` (entries 280–300); the deep classical ingredients are honestly socketed.

> **Scope.**  Nothing here proves `NEXP ⊄ ACC⁰` or `P ≠ NP`.  The Williams route formalizes a *proven* theorem
> (Williams 2011); the polynomial/native route is *blocked* (proved); the open frontier is named, not closed.

---

## 1. The Universal Native Characteristic Obstruction (entry 300)

**Theorem (`universal_native_characteristic_obstruction`, `…ACC0UniversalCharObstruction`).**
For coprime moduli `p, q`, no nontrivial commutative ring `R` is native to both: `(p : R) = 0` and `(q : R) = 0` force
`(1 : R) = 0`.  Concretely `(2 : R) = 0 ∧ (3 : R) = 0 ⇒ (1 : R) = 0`, by `1 = 3 − 2`.

**What it blocks.**  The Razborov–Smolensky polynomial method represents `MOD_p` at low degree *only* in a ring where
`p = 0` (the Fermat indicator `1 − x^{p−1}` computes `[count ≢ 0]` only when `y^{p−1} = 1` for `y ≠ 0`, i.e.
characteristic `p`).  A *native single-ring polynomial method* for a composite modulus `m = p·q` must therefore put both
`p = 0` and `q = 0` in one ring — which the obstruction shows is trivial.  So:

> **The Universal Native Characteristic Obstruction blocks every native single-ring polynomial method for a composite
> modulus.**

It subsumes, in one statement, the earlier no-gos: no common field (280, `no_common_char`); the product ring `ZMod 6`
is not a field and Fermat fails there (282); the tensor `F₂ ⊗ F₃ = 0` collapses.  All are instances of `1 = 3 − 2 = 0`.

---

## 2. N-Frame interpretation

In N-Frame terms, **`MOD₂` and `MOD₃` require incompatible native observer frames.**  Making `MOD_p` transparent to a
low-degree (polynomial) observer means working in the frame where `p` collapses to `0` — the characteristic-`p` frame,
in which the Fermat indicator reads the count.  `MOD₂` is transparent only in the char-2 frame, `MOD₃` only in char-3.

A **single nontrivial algebraic frame cannot make both transparent**: a frame native to both characteristics is forced
to `1 = 0` — it collapses to the trivial frame, in which nothing is observable.  This is the frame-level content of the
Universal Native Characteristic Obstruction.

**Characteristic-0 counting escapes** because it does *not* require native collapse.  The integer-count observer lives
in `ℤ` (characteristic 0): *neither* `2` nor `3` is `0` there.  It reads each residue through a quotient map
`ℤ → ZMod m` instead of demanding `p = 0` in its own frame.  Carrying every characteristic at once via quotients — not
collapsing any — it sidesteps the obstruction entirely (entry 290).  The price is that it abandons native low-degree
representation: counting is not a low-degree polynomial observer, it is an integer-state observer.

> **Slogan.**  Native polynomial transparency demands `p = 0` and so commits to one characteristic; integer counting
> demands no collapse and so carries all.  The composite separation lives in the gap between these.

---

## 3. The two routes, cleanly separated

| | **Native / polynomial route** | **Counting / Williams route** |
|---|---|---|
| Observer | low-degree polynomial over a field | integer gate-count over `ℤ` |
| Transparency of `MOD_p` | needs characteristic `p` (`p = 0`) | quotient `ℤ → ZMod p`, no collapse |
| Composite `MOD` | **blocked** (entry 300: no ring is native to coprime `p, q`) | **escapes** (entry 290: char 0 carries all) |
| Entries | **280–300** | **290–299, 319** |
| Status | *anatomized and blocked* (genuinely open whether a *non-native* representation exists) | *being formalized*; `NEXP ⊄ ACC⁰` is a proven theorem (Williams 2011), alive |

**Update (entry 319, `…ACC0CountingObserverWilliams`, PROVED):** the counting/Williams route is now a *single bridge
theorem*, not "Williams special case" language.  Its four ingredients are explicit N-Frame data —
`CharacteristicZeroCountingObserver` (the integer count `∑ⱼ [g j x] : ℕ`, no `p = 0`, not subject to the native
obstruction), `CRTResidueReadout` (`MOD_M` read via `c % M`, every `M`, not a native polynomial), `FastSATCompression`
(`< 2ⁿ` count cells, the Williams speedup object), `LazyHierarchyContradiction` (the complement-safe lazy diagonal) —
and `nframe_counting_branch_eq_williams` proves `NFrameCountingBranch ↔ WilliamsFastSatRoute`: the counting branch **is**
the Williams route, deriving `¬ (NEXP ⊆ ACC⁰)` through the named sockets (`nframe_counting_branch_derives_separation`).
This is *precisely* the route that is **not** the native polynomial branch the composite barrier blocks — the integer
count carries every characteristic, so it is never characteristic-blocked.

* **280–300 — native/polynomial route: anatomized and blocked.**  Every natural attack proved to fail (separated
  layers 280, staged observers 281, product-ring carry 282), the composite target frozen as `CarryRefinementCrossing`
  (283), the characteristic-coupled invariant built (288), no reduction to the single-prime no-go (289), and the
  universal root proved (300).  The native polynomial method cannot do composite `MOD`.
* **290–299 — counting/Williams route: being formalized and still alive.**  Char-0 escape (290), fast-SAT
  characteristic-universality (291), YBT existence + size (292), cost-bridge (293), NTIME-hierarchy diagonalization
  (294, lazy escape), Williams-as-N-Frame (295), universal-sim overhead-1 (296), decode-from-input uniformity (297),
  clocking to the bigger bound (298), bounded-acceptance decidability / boundary complement (299).  Remaining: the
  lazy-diagonal decider assembly, then the IKW / NW classical sockets — all proven-classical formalization.

---

## 4. The open frontier — non-native representations

The Universal Native Characteristic Obstruction blocks *native* (Fermat, `p = 0`) polynomial methods.  It does **not**
exclude a *non-native* representation.  So the genuinely-open question is:

> **Open.**  Does there exist a low-degree / low-complexity *non-native* representation of `MOD₆` that avoids requiring
> both `2 = 0` and `3 = 0`?

Candidate structures to test (each its own sub-question; none resolved):

1. **Characteristic-0 polynomials** (`ℤ` / `ℚ`).  `MOD_p` over `ℝ`/`ℚ` is *high* degree (parity needs degree `n`), so
   low-degree fails — this is *why* native methods use finite fields.  Plausibly a dead end for low-degree.
2. **CRT / product observers** (`ZMod 2 × ZMod 3`).  Hosts both gates by projection, but the approximation factors
   componentwise and each component sees the *other* prime's gate at high degree (the cross-modulus blow-up, 282).
3. **Semiring / non-ring structures.**  ~~Drop subtraction (the obstruction used `1 = 3 − 2`); whether a semiring can
   host both transparently is untested.~~  **ELIMINATED (entry 312, `…ACC0SemiringObstruction`):** the obstruction
   holds in any `AddCommMonoidWithOne` with *no* subtraction — `3 = 2 + 1`, so `2 = 0 ⟹ 3 = 1`, hence `3 = 0 ⟹ 1 = 0`.
   No native additive structure (semiring, tropical/idempotent, …) escapes.
4. **Probabilistic / approximate polynomials.**  Razborov–Smolensky already uses approximation over one field; a
   *cross-characteristic* approximate representation is the natural next object.
5. **Staged / layered observers that never flatten.**  Compute `MOD₂` and `MOD₃` in separate stages and combine without
   collapsing to one field (entry 281 blocked the *bounded-depth* flattening; a non-flattening composition is open).

> The composite barrier is now *beautifully pinned*: native polynomial methods are blocked at the single algebraic root
> `1 = 3 − 2 = 0`; the counting route escapes by abandoning native collapse; and any new polynomial-method separation
> must produce a non-native representation from the list above (each plausibly `ACC⁰[m]`-hard).

**Update (entry 317, `…ACC0CompositeCandidateUnification`, PROVED):** none of the surviving candidates is an
*independent* escape.  (i) The native algebraic obstruction (280/300/312) *requires* `2 = 0 ∧ 3 = 0`; this fails over a
nontrivial field (`ℚ`, `exists_nontrivial_field_two_three_neZero`), so the algebraic no-go is simply *silent* on the
non-native candidates — not killed by it, but gaining nothing from it.  (ii) The **dimension barrier is
characteristic-independent**: the degree-`≤ D` submodule is a *proper* subspace (`finrank = lowDegreeDim n D < 2ⁿ`) over
**every** field, char-0 `ℚ` included (`lowDegreeSubmodule_ne_top`, `charZero_no_low_degree`) — so candidate 1 (char-0)
gains nothing dimensionally, and candidates 2/4/5, over their ambient single field, face the identical proper-subspace
bound.  Hence every surviving candidate reduces, over its field, to the *same* single open analytic socket
`PolynomialMethodApproximation` (the Razborov–Smolensky core): the choice of ambient field/structure is **not** where a
separation can come from.  The composite barrier is genuinely *one* open problem, not a family of routes.

---

## 5. Where effort goes next

The composite barrier is pinned; the stronger immediate path is **completing the Williams-route formalization** (the
counting route, which formalizes a proven theorem to a full machine-checked arc): assemble the lazy-diagonal decider
bookkeeping, then isolate IKW / NW as the remaining classical sockets.  The non-native open question (§4) is genuine
research, plausibly as hard as `ACC⁰[m]` itself, and is recorded here as the frontier rather than an immediate build
target.
