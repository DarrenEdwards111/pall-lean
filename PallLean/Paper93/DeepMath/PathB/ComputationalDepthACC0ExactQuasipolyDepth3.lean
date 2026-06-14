import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactQuasipolyModTop
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ExactCompose

/-!
# One composition step deeper: depth-3 over bounded-fan-in `MOD_M ∘ AND_w` gates

Entry `…ACC0ExactQuasipolyModTop` showed a single `MOD_M ∘ AND_w` gate is exact and quasipolynomial, and localized
Wall 1 to the *bottom* (degree control), not the symmetric top.  This file tests the **"across depth" clause** of
Wall 1 directly: does exactness survive *one composition step* — a top gate over `k` of those depth-2
`MOD_M ∘ AND_w` gates — and at what cost?

The answer is **yes, exactly — at the fan-in product cost `2^k`**:

* each middle gate `MOD_M ∘ AND_w` is *exactly* the count-CRT decision (`…ACC0IntegerPolynomialCRT`), no
  approximation, with a quasipolynomial bottom (`m ≤ ∑_{i≤w} C(n,i)`);
* the depth-3 circuit `top ∘ (MOD_M ∘ AND_w)^k` is observed *exactly* by the `k`-bit output vector of the middle
  gates (`exact_depth_composes`), so SAT searches `≤ 2^k` cells — exact, any top gate.

This is the **exact composition** law made concrete one layer up: composition survives with no approximation, but the
cost is the **product** `2^k` (exponential in the top fan-in `k`).  It stays quasipolynomial only while `k = polylog`.
This is exactly the structural reason the general construction breaks: as the top fan-in grows (unbounded fan-in) or
the depth grows (each "cell count" itself becomes a product over the layer below), the exact boundary multiplies out
to exponential — the front half, **Wall 1**.

## What is proved (clean axioms, no `sorry`)

* `depth3_middle_exact` — each middle `MOD_M ∘ AND_w` gate is decoded *exactly* by its count-residue vector (CRT, no
  approximation).
* `depth3_modAnd_compose_searchable` — **both**: every middle bottom layer is quasipolynomial (`m ≤ ∑_{i≤w} C(n,i)`),
  *and* the depth-3 circuit `top ∘ (MOD_M ∘ AND_w)^k` is SAT-searchable in `< 2^n` cells once `2^k < 2^n`, with
  every layer exact.

## Honest scope — the cost is the product, and that is the wall

Exactness *does* survive the extra composition step — that is the content here.  But the cell count is the **product**
`2^k`: quasipolynomial only for `k = polylog`, exponential for unbounded top fan-in.  And this used the middle gates
as opaque output bits; pushing the *exact intermediate residues* up instead multiplies the per-gate `M` cells to
`M^k` — same product blow-up.  The general Yao–Beigel–Tarui normal form needs an *arbitrary* `ACC⁰` bottom across
*arbitrary* depth, where this product is genuinely exponential — the front half, **Wall 1**
(`MixedACCDepthReductionSocket` / `HasExactSymAndForm`).  Still the cell/observer model; `< 2^n` cells is not a
uniform algorithm (Wall 2).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth3

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT
open PallLean.Paper93.DeepMath.PathB.ACC0ExactCompose

variable {n m : ℕ}

/-- **Each middle `MOD_M ∘ AND_w` gate is decoded exactly by its count-residue vector (proved).**  The middle layer
introduces no approximation: CRT factors each gate through the residues mod the prime factors of `M`. -/
theorem depth3_middle_exact (mono : Fin m → Finset (Fin n)) (qs : List ℕ)
    (co : qs.Pairwise Nat.Coprime) (t : ℕ) :
    ∃ G : ((i : Fin qs.length) → ZMod (qs.get i)) → Bool,
      ∀ x, modCountDecision qs t (fun j x => monoAND (mono j) x) x
        = G (countResVec qs (fun j x => monoAND (mono j) x) x) :=
  modCount_factors_through_resVec qs co t (fun j x => monoAND (mono j) x)

/-- **Depth-3 exact composition over bounded-fan-in `MOD_M ∘ AND_w` gates (proved).**  For any top gate over `k`
middle `MOD_M ∘ AND_w` gates (distinct bottom monomials of fan-in `≤ w`): every middle bottom layer is
quasipolynomial (`m ≤ ∑_{i≤w} C(n,i)`), **and** the depth-3 circuit is SAT-searchable in `< 2^n` cells once
`2^k < 2^n` — observed *exactly* by the `k`-bit middle-output vector.  Composition survives exactly, at the product
cost `2^k`. -/
theorem depth3_modAnd_compose_searchable {k w : ℕ} (mono : Fin k → Fin m → Finset (Fin n))
    (hinj : ∀ i, Function.Injective (mono i)) (hdeg : ∀ i j, (mono i j).card ≤ w)
    (qs : List ℕ) (t : Fin k → ℕ) (top : (Fin k → Bool) → Bool) (hregime : 2 ^ k < 2 ^ n) :
    (∀ _ : Fin k, m ≤ ∑ d ∈ Finset.range (w + 1), n.choose d)
      ∧ ∃ g : (Fin k → Bool) → Bool,
          (Satisfiable
              (fun x => top (fun i =>
                modCountDecision qs (t i) (fun j x => monoAND (mono i j) x) x)) ↔
            ∃ s ∈ Finset.univ.image (fun x => fun i =>
                modCountDecision qs (t i) (fun j x => monoAND (mono i j) x) x), g s = true)
          ∧ (Finset.univ.image (fun x => fun i =>
              modCountDecision qs (t i) (fun j x => monoAND (mono i j) x) x)).card < 2 ^ n :=
  ⟨fun i => monomial_count_le (mono i) (hinj i) (hdeg i),
    exact_depth_composes
      (fun (i : Fin k) (x : Fin n → Bool) =>
        modCountDecision qs (t i) (fun j x => monoAND (mono i j) x) x) top hregime⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth3

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth3.depth3_middle_exact
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth3.depth3_modAnd_compose_searchable
