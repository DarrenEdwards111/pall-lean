# Scope: Layer 3 — AC⁰[p] / Razborov–Smolensky (polynomial method)

**Status:** Layer 2 (parity ∉ AC⁰, general depth) is **closed and hardened** (see
`SCOPE_OPTIONB_DEPTH_D.md`; axiom tripwire `ComputationalDepthDepth3Route2AxiomAudit.lean`). This doc
scouts **Layer 3**: lower bounds against constant-depth circuits *with MOD-p gates* (`AC⁰[p]`), via the
**polynomial method** (Razborov 1987 / Smolensky 1987).

**Honest framing (hard constraint):** Layer 3 is the *next circuit-lower-bound layer*, strictly stronger
than AC⁰ and a step on the historical road toward P vs NP — but it is **far below P vs NP** and this doc
claims nothing more. We are **not** doing ACC⁰/TC⁰ here, and **not** building a capstone yet.

---

## 0. Inventory done first (the constraint) — what ALREADY exists

**The AC⁰[p] circuit model is already in the repo — reuse it, do not redefine.**

- `BoolCircuitSyntax n` — `PallLean/Paper93/DeepMath/PathB/ComputationalDepthRung4CircuitReal.lean`:
  `const | input | not | andGate | orGate | modGate (p r : ℕ) (Cs : List _)`.
  - `eval : BoolCircuitSyntax n → (Fin n → Bool) → Bool` — `modGate p r Cs` outputs
    `decide ((#true children) % p = r % p)`.
  - `depth`, `size`, `Computes C F`, and the predicates `IsAC0Syntax` (no MOD) and
    **`IsAC0pSyntax (p) `** (MOD gates only of the fixed modulus `p`).
- Target-side: `trueCount x = #{i | x i}` and `parity x = decide (Odd (trueCount x))` —
  `ComputationalDepthDepth3Parity.lean` (full sensitivity + `parity_needs_full_depth` proved).
- Mathlib algebra (all present, verified in deps):
  `ZMod p` (CommRing; `Field` under `Fact p.Prime`), `ZMod.pow_card : x^p = x`,
  `ZMod.pow_card_sub_one_eq_one` (Fermat), `MvPolynomial σ R`, `MvPolynomial.eval`, `aeval`,
  `totalDegree`, `degreeOf`, `totalDegree_add`, `totalDegree_mul`, `frobenius`.
- Repo polynomial helpers: `LowDegAnnihilation.lean` (iterated `pderiv` kills low total degree),
  `ProductDeriv.lean`, `MultilinearSPDP.lean`.
- **ABSENT (this is the frontier):** any polynomial *approximation/representation* of Boolean
  functions over `ZMod p`, any degree lower bound, any Razborov–Smolensky argument.

---

## 1. Exact circuit model for AC⁰[p]

**Reuse `BoolCircuitSyntax` + `IsAC0pSyntax p`.** It already has real MOD gates with the right semantics
(`# true children ≡ r mod p`), Boolean eval, depth, size. The Layer-2 `Layered`/`ACircuit`/`Circ` types
are AND/OR-only (no MOD) — they are the AC⁰ substrate and are **not** used as the AC⁰[p] model.

- Work with `p` **prime** throughout (so `ZMod p` is a field); carry `[Fact p.Prime]`.
- A "depth-`d`, size-`s` AC⁰[p] circuit" = `C : BoolCircuitSyntax n` with `IsAC0pSyntax p C`,
  `C.depth ≤ d`, `C.size ≤ s`. (Size, not just depth, is the resource the polynomial method bounds.)

## 2. First target function / lower bound

**Target: `MOD_q` for a prime `q ≠ p`.** The canonical Razborov–Smolensky result is
**`MOD_q ∉ AC⁰[p]`** (small size) for distinct primes `p ≠ q`; the cleanest concrete instance is

> **`MOD₃ ∉ AC⁰[2]`** — `MOD₃` (is the Hamming weight ≡ 0 mod 3?) needs exponential-size depth-`d`
> circuits over `{¬, ∧, ∨, MOD₂}`.

**Do NOT target parity for AC⁰[2]:** parity *is* a MOD₂ gate, so it is trivially in AC⁰[2] — wrong target.
(Parity ∉ AC⁰[p] for *odd* p is the other valid instance, but `MOD_q vs AC⁰[p]`, `q ≠ p` both prime, is
the clean general statement; start with `MOD₃` vs `AC⁰[2]`.)

New target definition needed: a `MOD_q` Boolean function (generalising `parity = MOD₂`-oddness) — see §4.

## 3. Algebraic machinery already available (Mathlib + repo)

| need | available | where |
|---|---|---|
| field `𝔽_p` | `ZMod p` + `[Fact p.Prime]` ⇒ `Field` | Mathlib |
| `x^p = x` (Frobenius) | `ZMod.pow_card` | Mathlib |
| Fermat little | `ZMod.pow_card_sub_one_eq_one` | Mathlib |
| multivariate polys | `MvPolynomial (Fin n) (ZMod p)` | Mathlib |
| eval / total degree | `MvPolynomial.eval`, `totalDegree`, `degreeOf` | Mathlib |
| degree under +,× | `totalDegree_add`, `totalDegree_mul` | Mathlib |
| low-degree annihilation | `foldl_pderiv_monomial_zero` | repo `LowDegAnnihilation.lean` |
| Hamming weight | `trueCount` | repo `…Depth3Parity.lean` |

All the field/polynomial primitives are present; **nothing in Mathlib needs to be re-derived.** The gap
is purely the *complexity-theoretic* layer on top (representation + degree argument + counting).

## 4. New definitions needed (the frontier)

In dependency order (none built yet beyond the first foundation brick):
1. `boolToZMod {p} : Bool → ZMod p` (`false ↦ 0`, `true ↦ 1`); idempotent (`x² = x`). **[first brick]**
2. `MOD_q` target: `modCountFn (q r : ℕ) : (Fin n → Bool) → Bool := fun x => decide (trueCount x % q = r)`
   (so `parity = modCountFn 2 1`). **[first brick]**
3. **Polynomial representation of a circuit:** `repr : BoolCircuitSyntax n → MvPolynomial (Fin n) (ZMod p)`
   computing the same Boolean function on `{0,1}`-inputs, with a *total-degree* account per gate.
4. **Probabilistic / approximate polynomial** for AND/OR/MOD gates: each gate of fan-in `m` has a degree
   `O((p-1)·⌈log(1/ε)⌉)` polynomial agreeing on ≥ `1-ε` of inputs (the Razborov approximator).
5. **Composition bound:** a depth-`d`, size-`s` circuit ⇒ a single polynomial of degree
   `(O(√n · log s))^d`-ish agreeing on a `1 - sε` fraction.
6. **The counting/contradiction:** if `MOD_q` had such a low-degree approximant over `𝔽_p`, the space
   of functions on the agreement set would be too small (Smolensky's dimension argument) — contradiction.

## 5. Which Layer 2 components are reusable

- **Reusable:** the **proof discipline + axiom-audit pattern** (clean `[propext, Classical.choice,
  Quot.sound]`, no `sorry`, no `native_decide`, no custom axioms; the tripwire-file idiom); `trueCount`
  (Hamming weight, shared target primitive); the *habit* of representation-invariant counting (the
  polynomial method **is** a representation/counting argument — the [155b] "prove injectivity, don't
  assert it" instinct transfers directly to the degree/dimension bookkeeping).
- **NOT reusable as the engine:** the **switching lemma / random restrictions** — structurally dead
  against MOD gates (a restriction can't kill a MOD-p gate; the whole Layer-2 engine is the wrong tool).
  The `Layered` tower datatype and its collapse rounds do **not** carry over (no MOD gates, and the
  proof is restriction-based).
- **Open question (don't assume):** whether any tower-invariant-threading *style* helps the degree
  composition. Likely the polynomial method is flatter (one global polynomial), so probably no.

## 6. The first safe brick (this session)

**Definitions + one tiny `ZMod p` fact only — no capstone, no lower bound.**
`ComputationalDepthLayer3AC0pFoundations.lean`:
- `boolToZMod {p} : Bool → ZMod p`; `boolToZMod_mem` (`= 0 ∨ = 1`); `boolToZMod_sq` (`x² = x`, the
  idempotence that makes `{0,1}` the domain of the representation).
- `modCountFn (q r) : (Fin n → Bool) → Bool` and `parity_eq_modCountFn` (`parity = modCountFn 2 1`) —
  ties the new MOD-q target to the existing, already-proven `parity`/`trueCount` API.

These are harmless foundations (no claim, no assumption); they pin the embedding and the target so the
representation work in §4.3+ has a clean base. Commit only this + this scope doc.

---

*Roadmap, not a result. Layer 3 = AC⁰[p], a higher circuit-lower-bound layer — not P vs NP, not ACC⁰/TC⁰.*
