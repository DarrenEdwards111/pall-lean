# Audit — Computational-Depth Layers (Razborov–Smolensky `AC⁰[p]` lower bounds)

A self-contained audit of the **clean** computational-depth development: 28 modules under
`PallLean/Paper93/DeepMath/PathB/`, all sorry-free with standard axioms only
(`[propext, Classical.choice, Quot.sound]`), entirely independent of the unrelated
`PallLean.Step4Compiler` P-vs-NP experiment.

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

**Honest framing (applies to all of the above):** these are **nonuniform circuit-family** lower bounds for
**explicit, easy (P-computable)** languages.  They are **NOT** `P ≠ NP`, **NOT** `NP ⊄ AC⁰[p]` in any deep
sense, and **NOT** statements about hard `NP` functions.  See `SCOPE_LAYER7_OPEN_FRONTIER.md` and
`SCOPE_LAYER7_COMPLEXITY_CLASS_BRIDGE.md` for the open/known boundary.

---

## Module inventory (28 clean modules)

* **Circuit model:** `ComputationalDepthRung4CircuitReal` (`BoolCircuitSyntax`, `eval`, `depth`, `size`,
  `IsAC0pSyntax`).
* **Layer 3 (`AC⁰[p]` approximation + RS + PARITY):** `…Layer3AC0pFoundations`, `…AC0pApprox`, `…AC0pPoly`,
  `…AC0pPolyFull`, `…AC0pPolyMod`, `…Agreement`, `…Averaging`, `…DegreeComposition`, `…DimensionCount`,
  `…Smolensky`.
* **Layer 4 (general `MOD_q`):** `…Layer4BaseChange`, `…ModqChar`, `…RootOfUnity`, `…DimGeneral`,
  `…QaryReduction`, `…QarySpan`, `…WeightRepr`, `…Approx`, `…Padding`, `…Assembly`, `…Intersection`,
  `…Bridge`, `…Capstone`, `…PadSubcircuits`.
* **Layer 7 (nonuniform families):** `…Layer7CircuitFamily`, `…Layer7ParityFamily`, `…Layer7ModqFamily`.

## Reusable / Mathlib-extraction candidates

* `Layer3.centralBinom_sq_le` — central-binomial `√n`-type bound used for the band margin.
* `Layer3.lowDegMonomials_card` / `…_band_margin` — low-degree monomial counts.
* `Layer4.exists_primitiveRoot_galoisField` — a primitive `q`-th root of unity in `GaloisField p (q-1)`.
* `Layer7.exists_poly_lt_pow` — exponential dominates polynomial over `ℕ` (`p ≥ 2`).
