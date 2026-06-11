# Scope — Layer 4: general MOD_q lower bound (MOD_q ∉ AC⁰[p] for p ≠ q)

**Status of Layer 3 (done):** `PARITY = MOD₂ ∉ AC⁰[p]` for odd `p`, fully assembled and sorry-free
(`ComputationalDepthLayer3Smolensky.lean`: `parity_function_lower_bound`,
`parity_size_lower_bound_explicit`, `parity_circuit_false`, `smolensky_contradiction`,
`chi_univ_repr`, `pmSpan_eq_top`, `centralBinom_sq_le`, `lowDegMonomials_card_band_margin`).

**Layer 4 goal:** for distinct primes `p ≠ q`, `MOD_q` is not computable by polynomial-size
constant-depth `AC⁰[p]` circuits.

**The one structural reason Layer 3 is special.** The 2nd roots of unity `{+1, -1}` live in `F_p` for
*every* `p`, so PARITY's whole argument ran **directly over `F_p`**. The `q`-th roots of unity for
`q > 2` live in `F_p` only when `q ∣ p-1`; in general they live in the extension
`F_{p^k}`, `k = ord_q(p)` (the multiplicative order of `p` mod `q`). **So Layer 4 must move to the
extension field `F_{p^k}`** — this is the first genuine difference, and it cascades.

---

## 1. Which parts of Layer 3 generalize?

| Layer-3 component | Generalizes? | Notes |
|---|---|---|
| **Combinatorial dimension count** (`lowDegMonomials_card`, `_halfway`, `_le_two_pow`) | ✓ **unchanged** | pure ℕ / `Finset` combinatorics, field-independent |
| **Central-binomial √n bound** (`centralBinom_sq_le`) | ✓ **unchanged** | pure ℕ; reusable verbatim |
| **Band margin** (`lowDegMonomials_card_band_margin`, `_halfway_margin`) | ✓ **unchanged** | pure ℕ; reusable verbatim |
| **Size-bound arithmetic** (`parity_circuit_size_lower_bound`, `_depth_le`, `_explicit`) | ✓ **structure reusable** | `omega`/contrapositive over ℕ; the *shape* transfers, restated for the new contradiction |
| **`finrank (↥G → K) = |G|`** (`finrank_functions_on_G`) | ✓ **any field** `K` | `Module.finrank_pi`; just instantiate `K = F_{p^k}` |
| **Degree side** (`toApprox`/`toAgree_totalDegree_le`, `genOrApprox`, `ApproxDegreeData`) | ◑ **F_p-specific, but transfers** | AC⁰[p] gates are approximated over `F_p` (Fermat `a^{p-1}`, mod-`p` gates). The degree bound `((p-1)t)^depth` is unchanged. **New small brick:** base-change an `F_p` polynomial to `F_{p^k}` (ring hom `MvPolynomial _ (ZMod p) → MvPolynomial _ (GaloisField p k)`) preserving `totalDegree` and `eval`. |
| **Agreement side** (`composed_error_le`, `exists_large_agreement_set`) | ◑ **transfers via base-change** | agreement is Boolean-cube error counting (ℕ), independent of the field beyond `F_p`; after base-change the same approximant agrees over `F_{p^k}`. The `(3/4)` fraction may need to become `(1 - 1/(2q))`-style depending on the dimension step. |
| **`squarefreeSpan_eq_top`** ({0,1} monomials span `↥cube → K`) | ✓ **any field** | uses only `x² = x` on the cube + the indicator basis; field-general (currently stated for `ZMod p`, re-state over `K`) |

## 2. Which parts are parity-specific (must be replaced)?

| Layer-3 component | Why parity-specific | MOD_q replacement |
|---|---|---|
| **`pmOne : Bool → ZMod p`** (`if b then -1 else 1`) | `±1` = 2nd roots of unity | `ζ`-encoding `b ↦ ζ^b` (`b ↦ if b then ζ else 1`), `ζ` a primitive `q`-th root in `F_{p^k}` |
| **`χ_univ = ∏ pmOne(xᵢ) = (-1)^{#ones}`** | encodes weight **mod 2** | `∏ ζ^{xᵢ} = ζ^{#ones}` encodes weight **mod q** |
| **`pmOne_mul_self` (`y² = 1`)** + **`pm_monomial_halving`** (`χ_S = χ_univ·χ_{Sᶜ}`) + **`pm_monomial_reduction`** (degree-halving) | the `y²=1` **involution** is the heart of the degree-halving; it is **exactly q=2** | **No naive analogue.** `ζ^q = 1` but a Boolean `xᵢ` gives `ζ^{xᵢ} ∈ {1, ζ}` with `(ζ^{xᵢ})² ≠ 1` for `q > 2`. The general-`q` degree reduction is a **different argument** (see §3) — **must not be faked.** |
| **±1 multilinear basis** (`pmSpan_eq_top`, `pmMonomial`, `pm_monomial_mul`, `pmEvalMonomial`) | built on `pmOne`/`y²=1` | over `F_{p^k}` the `{0,1}` squarefree basis (`squarefreeSpan_eq_top`) already spans; the `ζ`-monomials are an *alternative* basis whose role in the reduction is the open part |
| **`chi_univ_repr`** (the parity bridge: circuit ⇒ low-degree `χ_univ`) | maps the parity circuit's `F_p` approximant to a low-degree `(-1)^{#ones}` | analogue: `MOD_q` circuit's `F_{p^k}` approximant ⇒ low-degree `ζ^{#ones}` — **but this is exactly the step where the q>2 difficulty lives** (§3) |

## 3. The genuine algebraic gap (do **not** fake)

PARITY's degree collapse rested on the **involution** `y² = 1` of the `±1` cube: every monomial
`χ_S` rewrites as `χ_univ · χ_{Sᶜ}`, so a single low-degree object (`χ_univ`) collapses the whole
function space to degree `≤ n/2 + Δ`. For `q > 2` there is **no Boolean involution**: `ζ^{xᵢ} ∈ {1, ζ}`
and `(ζ^{xᵢ})²` is a *third* value. The standard general-`q` Smolensky argument therefore replaces the
halving with a **different dimension count over `F_{p^k}`**, and the exact mechanism is the part Layer 4
must actually do (and the part most at risk of hand-waving). The honest open questions:

* **(A) Extension field.** Need `F_{p^k}` with `k = ord_q(p)` and a primitive `q`-th root `ζ`.
  *Mathlib status:* `GaloisField p k` exists (`Mathlib.FieldTheory.Finite.GaloisField`, `card = p^k`);
  `IsPrimitiveRoot` / `exists_primitiveRoot` / `card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot` exist;
  finite-field units are cyclic. **Existence of an order-`q` element when `q ∣ p^k − 1`** (the
  `k = ord_q(p)` fact, `q ∣ p^{ord_q(p)} − 1`) should be derivable from `IsCyclic` + `orderOf`; needs an
  explicit small lemma. *Likely available; isolate `q ∣ p^{ord_q(p)} − 1` as a named brick.*
* **(B) Base-change `F_p → F_{p^k}`.** `MvPolynomial.map (algebraMap (ZMod p) (GaloisField p k))`
  preserves `totalDegree` (`≤`) and commutes with `eval` along the embedding. *Mathlib has `MvPolynomial.map`,
  `totalDegree_map_le`, `eval₂`/`map` eval lemmas — a clean small brick.*
* **(C) The degree-reduction replacement.** This is the real mathematical content. Candidate routes,
  to be decided **before** coding:
  1. *q-ary multilinear reduction* over `F_{p^k}`: every function `↥G → F_{p^k}` is degree `≤ n/2 + O(Δ)`,
     proved without an involution. (Smolensky's original counts the dimension of the space of functions
     realised by low-degree polys directly, using that `MOD_q` low-degree ⇒ `ζ^{#ones}` low-degree on `G`.)
  2. *Reduce to PARITY-style on a substructure* — generally **not** sound for `q > 2`; flagged as a trap.
  **Decision deferred to a dedicated scope note; no capstone until (C) has a real proof.**

## 4. Cleanest first brick (safe, foundational)

The `ζ`-weight encoder — the exact `q`-ary generalisation of `prod_pmOne` — is **ring-general,
correct, and harmless**:

> `weightChar R ζ x := ∏ i, (1 + (ζ - 1) · (if xᵢ then 1 else 0))`  satisfies
> `weightChar R ζ x = ζ ^ (#{i : xᵢ})` (the Hamming weight; `mod q` once `ζ^q = 1`).

Specialising `ζ = -1 : ZMod p` recovers `prod_pmOne` (`= (-1)^{#ones}`). This is the first file
(`ComputationalDepthLayer4ModqChar.lean`): the encoder + the product identity + the parity-specialisation
sanity check + (next) the existence of `ζ` in `GaloisField p k`. **No field-specific or unproved content.**

## 5. Minimal Layer 4 theorem statement (target, not yet proved)

Mirroring `parity_function_lower_bound`, the eventual capstone:

> For distinct primes `p ≠ q` (`p` the circuit modulus), `k = ord_q(p)`, working over `K = F_{p^k}` with
> a primitive `q`-th root `ζ`: any `AC⁰[p]` circuit of depth `≤ d` on `N` variables that **computes
> `MOD_q`** (`Cir.eval x = decide (q ∣ #{i : xᵢ})`) has `size ≥ 2^{Ω(N^{1/(2d)})}`.

Stated, like Layer 3, as a clean `Nat` inequality (`size > p^t/4` on a window), parametrised by the time
horizon `t`, with the genuinely-MOD_q-specific input (§3 (C)) isolated as an explicit hypothesis until it
is proved — **never assumed silently, never faked.**

---

## Discipline (carried from Layer 3)

* All new work **sorry-free**; verify with `#print axioms` (grep `sorryAx`) per brick.
* **Do not weaken Layer 3.** Layer 4 only *adds* files; it never edits Layer 3 capstones.
* **No custom axioms.** Clean axioms `[propext, Classical.choice, Quot.sound]` only.
* If a needed algebraic fact (§3) is unavailable in Mathlib, **isolate it in a scope note before
  formalizing** — do not inline an unproved `have`.
* Small lemmas, buildable commits; `lake build` + push after each.
