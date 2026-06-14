import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactQuasipolyModTop

/-!
# The smallest anti-product trick: a symmetric top avoids the `2^k` composition blow-up

The fragment ladder ended at the product wall: `…ACC0ExactQuasipolyDepth3` showed an *arbitrary* top over `k` middle
`MOD_M ∘ AND_w` gates composes exactly but at the **product** cost `2^k` (the top reads the full `k`-bit middle-output
vector).  Wall 1 was localized to exactly this: *exact composition works, but exact observer state multiplies across
wide layers; YBT's content is avoiding that product blow-up.*

This file exhibits the smallest case where the product is genuinely **avoided** — the anti-product mechanism in its
purest form.  If the top gate is itself **symmetric** (a count/`MOD`/threshold over the `k` middle gates, not an
arbitrary Boolean function), it reads only the **count** of accepting middle gates — `k+1` states — not the `2^k`
output vector.  So two symmetric layers — an outer `SYM` over `k` inner `MOD_M ∘ AND_w` gates (themselves
`SYM ∘ AND`) — compose with only `k+1` observer states, **linear**, not the product `2^k`/`M^k`.

```
arbitrary top ∘ (MOD_M ∘ AND_w)^k :   2^k cells   (…ACC0ExactQuasipolyDepth3, the product wall)
SYM      top ∘ (MOD_M ∘ AND_w)^k :   k+1 cells   (this file, the anti-product)
```

## What is proved (clean axioms, no `sorry`)

* `middleGate` — the `k` middle `MOD_M ∘ AND_w` gates (bounded-fan-in bottom, exact CRT-decoded modular top).
* `antiproduct_count_card_le` — a symmetric top over the `k` middle gates is observed in `≤ k+1` cells (the count of
  accepting middle gates), **not** `2^k` — the product collapses to linear.
* `antiproduct_sym_modAnd_searchable` — **both**: every middle bottom layer is quasipolynomial, *and* the
  depth-3 circuit with a *symmetric* top is SAT-searchable in `≤ k+1` cells once `k+1 < 2^n` — the product blow-up
  avoided.

## Honest scope — why this real trick is still not YBT

The anti-product is genuine: a symmetric top sees only the count, so `k+1`, not `2^k`.  But it does **not** solve the
general problem, for three precise reasons:

1. **Pre-grouping.**  It needs the circuit already presented as a *single* symmetric layer over `k` nice middle
   gates.  Reducing an arbitrary `ACC⁰` circuit to that shape is the open problem, not this lemma.
2. **No iteration.**  The count of accepting middle gates is symmetric in the *middle outputs*, not in the *inputs* or
   the bottom `AND`s.  So it cannot be applied recursively to flatten arbitrary depth into one count — each new
   symmetric layer is over the previous layer's outputs, and the layers do not merge.
3. **The bottom is still the wall.**  The `k+1` count observer says nothing about the bottom; the bottom `AND` degree
   must still stay polylog for the bottom monomial count to be quasipolynomial.  That clause is Wall 1.

In short: this *is* the YBT `SYM` top being tractable (already in `…ACC0SymmetricObserver`: a symmetric function is
observed by the count, `m+1` not `2^m`), made concrete one layer up.  It avoids the product at **one** symmetric layer;
the YBT *content* — reducing arbitrary `ACC⁰` to one `SYM ∘ AND` of quasipolynomial width with the bottom degree
polylog — remains the front half, **Wall 1**.  Still the cell/observer model; `< 2^n` cells is not a uniform algorithm
(Wall 2).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AntiProductSym

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT

variable {n m k : ℕ}

/-- The `k` middle `MOD_M ∘ AND_w` gates: middle gate `i` is the exact count-CRT decision over its bounded-fan-in
bottom monomials `mono i`. -/
def middleGate (qs : List ℕ) (mono : Fin k → Fin m → Finset (Fin n)) (t : Fin k → ℕ) :
    Fin k → (Fin n → Bool) → Bool :=
  fun i x => modCountDecision qs (t i) (fun j x => monoAND (mono i j) x) x

/-- **A symmetric top over the `k` middle gates is observed in `≤ k+1` cells, not `2^k` (proved).**  The symmetric top
reads only the *count* of accepting middle gates — the product `2^k` of `…ACC0ExactQuasipolyDepth3` collapses to
linear `k+1`. -/
theorem antiproduct_count_card_le (qs : List ℕ) (mono : Fin k → Fin m → Finset (Fin n))
    (t : Fin k → ℕ) :
    (Finset.univ.image (gateCount (middleGate qs mono t))).card ≤ k + 1 :=
  sym_count_card_le (middleGate qs mono t)

/-- **The anti-product, both at once (proved).**  A depth-3 circuit with a *symmetric* top `h` over `k` middle
`MOD_M ∘ AND_w` gates (distinct bounded-fan-in bottom monomials): every middle bottom layer is quasipolynomial
(`m ≤ ∑_{d≤w} C(n,d)`), **and** the whole circuit is SAT-searchable in `≤ k+1` cells once `k+1 < 2^n` — the symmetric
top avoids the `2^k` product blow-up of `…ACC0ExactQuasipolyDepth3`. -/
theorem antiproduct_sym_modAnd_searchable {w : ℕ} (mono : Fin k → Fin m → Finset (Fin n))
    (hinj : ∀ i, Function.Injective (mono i)) (hdeg : ∀ i j, (mono i j).card ≤ w)
    (qs : List ℕ) (t : Fin k → ℕ) (h : ℕ → Bool) (hregime : k + 1 < 2 ^ n) :
    (∀ _ : Fin k, m ≤ ∑ d ∈ Finset.range (w + 1), n.choose d)
      ∧ (Finset.univ.image (gateCount (middleGate qs mono t))).card ≤ k + 1
      ∧ (Satisfiable (symEval (middleGate qs mono t) h) ↔
            ∃ c ∈ Finset.univ.image (gateCount (middleGate qs mono t)), h c = true)
        ∧ (Finset.univ.image (gateCount (middleGate qs mono t))).card < 2 ^ n :=
  ⟨fun i => monomial_count_le (mono i) (hinj i) (hdeg i),
    antiproduct_count_card_le qs mono t,
    sym_searchable (middleGate qs mono t) h hregime⟩

end PallLean.Paper93.DeepMath.PathB.ACC0AntiProductSym

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AntiProductSym.antiproduct_count_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AntiProductSym.antiproduct_sym_modAnd_searchable
