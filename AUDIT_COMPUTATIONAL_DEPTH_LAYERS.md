# Audit — Computational-Depth Layers (`AC⁰[p]`, general circuits, frontier infrastructure)

A self-contained audit of the **clean** computational-depth development: 37 modules under
`PallLean/Paper93/DeepMath/PathB/`, all sorry-free with standard axioms only
(`[propext, Classical.choice, Quot.sound]`; some are axiom-free), entirely independent of the unrelated
`PallLean.Step4Compiler` P-vs-NP experiment.

The development spans three honest regimes:
* **Layers 3–7** — explicit lower bounds against `AC⁰[p]` (PARITY, `MOD_q`): a restricted model, easy
  functions.
* **Layer 8** — general (unrestricted-depth) circuits: the classical Shannon counting bound
  (exponential, nonconstructive) and an explicit linear bound.
* **Layer 9** — open-frontier *infrastructure*: `P/poly`, the Karp–Lipton collapse core, a hard language
  outside `P/poly`, and the natural-proofs barrier — each with every open/cryptographic step isolated as an
  explicit hypothesis.

**No part claims `P ≠ NP`, `NP ⊄ P/poly`, or any explicit super-polynomial general-circuit bound.** Those
remain open and barrier-blocked; see `SCOPE_LAYER8_GENERAL_CIRCUITS.md` and
`SCOPE_LAYER8_EXPLICIT_LOWER_BOUND_FRONTIER.md`.

**Verify:** `./scripts/build_clean_layers.sh` builds exactly these modules and asserts every capstone
below is sorry-free.

---

## Capstone theorems (exact statements + axiom certificates)

All names are under namespace `PallLean.Paper93.DeepMath.PathB`.

### Layer 3 — PARITY ∉ `AC⁰[p]` (per-length, nonuniform)

`Layer3.parity_function_lower_bound` — `ComputationalDepthLayer3Smolensky.lean`
```
(p) [Fact p.Prime] {m d} (hp2 : (2:ZMod p) ≠ 0) (Cir : BoolCircuitSyntax (2*m+1))
(hd : Cir.depth ≤ d) (t) (ht1 : 1 ≤ t)
(hparity : ∀ x, Cir.eval x = decide (Odd (univ.filter (x ·)).card))
(hmod : ∀ q r cs, modGate q r cs ∈ subcircuits Cir → q = p)
(hm : 8 * (((p-1)*t)^d)^2 ≤ m)
⊢ p^t < 4 * (subcircuits Cir).toFinset.card
```
*Any one `AC⁰[p]` circuit computing parity on `2m+1` bits, of depth `≤ d`, has size `> p^t/4` in the
band-margin regime.*  Axioms: `[propext, Classical.choice, Quot.sound]`.

### Layer 4 — general `MOD_q` ∉ `AC⁰[p]` (`p ≠ q`, per-length / family)

`Layer4.mod_q_indicators_false` — `…Layer4Capstone.lean`: for distinct primes `p ≠ q`, over
`K = F_{p^{q-1}}`, no family of `q` circuits on `2m+1` inputs can compute the residue indicators
`[#ones ≡ j (mod q)]`, be `AC⁰[p]`, within the size/depth/band-margin window.

`Layer4.mod_q_family_false` — `…Layer4PadSubcircuits.lean`: same separation phrased from a literal
`MOD_q ∈ AC⁰[p]` family `D_0,…,D_{q-1}` (via the `padTrue` construction).

`Layer4.qary_contradiction` — `…Layer4Bridge.lean`: the assembled general-`q` analogue of
`smolensky_contradiction`.

All three: `[propext, Classical.choice, Quot.sound]`.

### Layer 7 — circuit-family language separations (nonuniform; honest level-2)

`Layer7.parity_not_in_nonuniform_AC0p` — `…Layer7ParityFamily.lean`
```
(p) [Fact p.Prime] (hp2 : (2:ZMod p) ≠ 0) (F : AC0pFamily p) (hpoly : IsPolyBounded F.sizeBound)
⊢ ¬ F.Computes parityLang
```
`Layer7.modq_not_in_nonuniform_AC0p` — `…Layer7ModqFamily.lean`
```
(p q) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p) (F : AC0pFamily p) (hpoly : IsPolyBounded F.sizeBound)
⊢ ¬ F.Computes (modqLang q)
```
*No constant-depth, polynomially-size-bounded `AC⁰[p]` circuit family computes the PARITY / `MOD_q`
language.*  Both: `[propext, Classical.choice, Quot.sound]`.

**Honest framing (Layers 3–7):** these are **nonuniform circuit-family** lower bounds for **explicit, easy
(P-computable)** languages.  They are **NOT** `P ≠ NP`, **NOT** `NP ⊄ AC⁰[p]` in any deep sense, and **NOT**
statements about hard `NP` functions.  See `SCOPE_LAYER7_OPEN_FRONTIER.md` and
`SCOPE_LAYER7_COMPLEXITY_CLASS_BRIDGE.md`.

### Layer 8 — general (unrestricted-depth) circuit lower bounds

`Layer8.Circuit` / `eval` / `size` / `SIZE` — `…Layer8GeneralCircuit.lean`: the general fan-in-2 Boolean
circuit model underlying `P/poly` (finite gate set ⇒ size-bounded circuits are countable).

`Layer8.shannon_counting_bound` — `…Layer8ShannonCount.lean`: `(n+6)^s < 2^{2ⁿ} ⇒ ∃ f, f ∉ SIZE n s`.
The single-exponential circuit count proved via preorder serialization + unique readability
(`Layer8.toTokens_inj`) + a padded-array injection (`card {c // c.size ≤ s} ≤ (n+6)^s`).

`Layer8.exists_function_needing_exp_size` — `…Layer8ShannonExplicit.lean`
```
(n) ⊢ ∃ f : (Fin n → Bool) → Bool, ∀ c : Circuit n, Computes c f → 2^n / (n+6) - 1 < c.size
```
*Shannon's theorem, explicit-threshold form: some function needs general-circuit size `≈ 2ⁿ/n`.*
**Nonconstructive** (names no explicit function).

`Layer8.andAll_needs_linear_size` — `…Layer8LinearBound.lean`
```
(n) (c : Circuit n) (hc : Computes c (andAll n)) ⊢ n ≤ c.size
```
*Explicit linear bound: the `n`-bit AND needs size `≥ n` (every relevant variable must occur as a leaf).*
**Explicit but only linear.**

All four: `[propext, Classical.choice, Quot.sound]`.

### Layer 9 — open-frontier infrastructure (conditional / nonconstructive)

`Layer9.Ppoly` — `…Layer9KarpLipton.lean`: `P/poly` over poly-size general-circuit families.

`Layer9.karpLipton_collapse` — `…Layer9KarpLipton.lean`: the **axiom-free** logical core of Karp–Lipton —
given an advice-extraction hypothesis `hadv`, the `Π₂`-form `∀y ∃z R x y z` equals the `Σ₂`-form
`∃g ∀y R x y (w g x y)`.  The complexity content (`NP ⊆ P/poly` ⇒ `hadv`) is the fenced hypothesis.
(Depends on **no axioms**.)

`Layer9.exists_lang_not_in_Ppoly` — `…Layer9PpolyLowerBound.lean`: `∃ L, ¬ Ppoly L` — some language is
outside `P/poly` (family-level Shannon; **nonconstructive**, not about `NP`).

`Layer9.razborov_rudich_barrier` / `no_natural_property_if_secure_prf` — `…Layer9NaturalProofs.lean`: the
natural-proofs barrier — a *useful* + *large* property cannot coexist with a secure PRF in the class (the
PRF security is the fenced cryptographic hypothesis).  A theorem *about the barrier*, not a lower bound.

`Ppoly`, `exists_lang_not_in_Ppoly`, `razborov_rudich_barrier`: `[propext, Classical.choice, Quot.sound]`.

**Honest framing (Layers 8–9):** Layer 8's strong bound is *nonconstructive*; its explicit bound is only
*linear*.  Layer 9 is *infrastructure + conditionals*, with `NP ⊆ P/poly` / SAT self-reducibility / PRF
security all isolated as explicit hypotheses.  **None of this is `NP ⊄ P/poly` or `P ≠ NP`**; the
explicit super-polynomial frontier is open and barrier-blocked.

---

## Module inventory (37 clean modules)

* **Circuit model:** `ComputationalDepthRung4CircuitReal` (`BoolCircuitSyntax`, `eval`, `depth`, `size`,
  `IsAC0pSyntax`).
* **Layer 3 (`AC⁰[p]` approximation + RS + PARITY):** `…Layer3AC0pFoundations`, `…AC0pApprox`, `…AC0pPoly`,
  `…AC0pPolyFull`, `…AC0pPolyMod`, `…Agreement`, `…Averaging`, `…DegreeComposition`, `…DimensionCount`,
  `…Smolensky`.
* **Layer 4 (general `MOD_q`):** `…Layer4BaseChange`, `…ModqChar`, `…RootOfUnity`, `…DimGeneral`,
  `…QaryReduction`, `…QarySpan`, `…WeightRepr`, `…Approx`, `…Padding`, `…Assembly`, `…Intersection`,
  `…Bridge`, `…Capstone`, `…PadSubcircuits`.
* **Layer 7 (nonuniform families):** `…Layer7CircuitFamily`, `…Layer7ParityFamily`, `…Layer7ModqFamily`.
* **Layer 8 (general circuits):** `…Layer8GeneralCircuit`, `…Layer8Shannon`, `…Layer8ShannonCount`,
  `…Layer8ShannonExplicit`, `…Layer8LinearBound`.
* **Layer 9 (frontier infrastructure):** `…Layer9KarpLipton`, `…Layer9PpolyLowerBound`,
  `…Layer9NaturalProofs`.
* **Mathlib extraction:** `…ComputationalDepthMathlibCandidates`.

## Reusable / Mathlib-extraction candidates

* `Nat.centralBinom_sq_mul_le`, `Nat.exists_poly_lt_pow` — `…ComputationalDepthMathlibCandidates.lean`:
  the central-binomial `√n` bound and "exponential dominates polynomial", isolated with Mathlib-only
  imports (PR-ready).
* `Layer3.lowDegMonomials_card` / `…_band_margin` — low-degree monomial counts.
* `Layer4.exists_primitiveRoot_galoisField` — a primitive `q`-th root of unity in `GaloisField p (q-1)`.
* `Layer7.exists_poly_lt_pow` — exponential dominates polynomial over `ℕ` (`p ≥ 2`).
* `Layer8.toTokens_inj` — unique readability of preorder circuit serialization (`[propext]` only).
