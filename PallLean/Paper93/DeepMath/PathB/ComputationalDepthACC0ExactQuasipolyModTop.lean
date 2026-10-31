import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IntegerPolynomialCRT
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# How far the exact-quasipoly fragment extends: a single `MOD` top over bounded-fan-in `AND`s

The toy `…ACC0ExactQuasipolyDepth2` showed a depth-2 `OR ∘ AND_w` DNF is *exact and quasipolynomial at once*.  This
file pushes the same fragment one step toward the real Yao–Beigel–Tarui normal form by replacing the `OR` top with a
`MOD_M` top — i.e. a genuine `SYM ∘ AND_w` whose symmetric top is a modular count gate:

```
MOD_M ∘ AND_w :   x ↦ [ #{ j : (AND of mono j)(x) } ≡ t   (mod M) ],     |mono j| ≤ w,   M = ∏ q_i  (pairwise coprime).
```

Both layers stay **exact** — no Razborov–Smolensky approximation anywhere:

* the **bottom** `AND_w` layer is exact and quasipolynomial, exactly as before: a bottom `AND` of fan-in `≤ w`
  (`monoAND`) **is** the degree-`≤w` monomial, and distinct such gates number `≤ ∑_{i≤w} C(n,i)` (`n^{O(w)}`);
* the **top** `MOD_M` gate is decoded *exactly* by the Chinese Remainder Theorem on the integer count polynomial
  `gateCount` (`…ACC0IntegerPolynomialCRT`): it factors through the count's residue vector mod the prime factors of
  `M`, of cardinality `M`.  `MOD` is *exactly symmetric* — it needs no approximation, unlike a low-degree polynomial
  over a single field.

So the exact-quasipoly fragment **does** extend to a single `MOD` top: the whole `MOD_M ∘ AND_w` circuit is exactly
representable, with the bottom layer quasipolynomial and the top costing only `M` residue cells (independent of the
bottom count — the modular top *compresses* the count to `M` classes).

## What is proved (clean axioms, no `sorry`)

* `modAnd_bottom_count_le` — the bottom layer is quasipolynomial: `m ≤ ∑_{i≤w} C(n,i)`.
* `modAnd_exact_observed` — the `MOD_M ∘ AND_w` circuit is decoded **exactly** by the count-residue vector (CRT, no
  approximation).
* `modAnd_exact_quasipoly_searchable` — **both**: bottom quasipolynomial *and* (once `M = qs.prod < 2^n`) the circuit
  is SAT-searchable in `< 2^n` residue cells, with everything exact.
* `mod6_and_exact_quasipoly_searchable` — the concrete `M = 6 = 2·3` top.

## Honest scope — exactly where it stops

This extends the *exact-and-quasipolynomial* fragment to **one** `MOD` layer over a **bounded-fan-in** bottom — still
depth 2.  It does **not** reach the general Yao–Beigel–Tarui normal form: that needs the bottom to be an *arbitrary*
`ACC⁰` subcircuit (unbounded fan-in / the `MOD` layer interleaved / arbitrary depth), where exactness forces
exponential size — the front half, **Wall 1** (`MixedACCDepthReductionSocket` / `HasExactSymAndForm`).  The `MOD` top
being exact buys nothing there: it is the *bottom* `AND_w → exact low-degree polynomial across depth` that breaks.
Still the cell/observer model; `< 2^n` cells is not a uniform algorithm (Wall 2).  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyModTop

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0IntegerPolynomialCRT

variable {n m : ℕ}

/-- **The bottom `AND_w` layer is quasipolynomial (proved).**  Distinct bottom `AND` gates of fan-in `≤ w` number at
most `∑_{i≤w} C(n,i)` (`n^{O(w)}`, quasipoly for `w = polylog n`). -/
theorem modAnd_bottom_count_le {w : ℕ} (mono : Fin m → Finset (Fin n))
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ w) :
    m ≤ ∑ i ∈ Finset.range (w + 1), n.choose i :=
  monomial_count_le mono hinj hdeg

/-- **The `MOD_M ∘ AND_w` circuit is decoded *exactly* by the count-residue vector (proved).**  The top `MOD_M` gate
needs no approximation: CRT on the integer count `gateCount` factors the decision through the residues mod the prime
factors of `M`. -/
theorem modAnd_exact_observed (mono : Fin m → Finset (Fin n)) (qs : List ℕ)
    (co : qs.Pairwise Nat.Coprime) (t : ℕ) :
    ∃ G : ((i : Fin qs.length) → ZMod (qs.get i)) → Bool,
      ∀ x, modCountDecision qs t (fun j x => monoAND (mono j) x) x
        = G (countResVec qs (fun j x => monoAND (mono j) x) x) :=
  modCount_factors_through_resVec qs co t (fun j x => monoAND (mono j) x)

/-- **Exact *and* quasipolynomial, with one `MOD` top (proved).**  For a depth-2 `MOD_M ∘ AND_w` circuit — distinct
bottom monomials of fan-in `≤ w`, top `MOD_M` with `M = qs.prod` over pairwise-coprime `qs` — the bottom layer is
quasipolynomial (`m ≤ ∑_{i≤w} C(n,i)`) **and** the whole circuit is *exactly* decoded by the count-residue vector,
SAT-searchable in `< 2^n` cells once `M = qs.prod < 2^n`.  No approximation in either layer. -/
theorem modAnd_exact_quasipoly_searchable {w : ℕ} (mono : Fin m → Finset (Fin n))
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ w)
    (qs : List ℕ) (co : qs.Pairwise Nat.Coprime) (hpos : ∀ i : Fin qs.length, 0 < qs.get i)
    (t : ℕ) (hregime : qs.prod < 2 ^ n) :
    m ≤ ∑ i ∈ Finset.range (w + 1), n.choose i
      ∧ ∃ G : ((i : Fin qs.length) → ZMod (qs.get i)) → Bool,
          (Satisfiable (modCountDecision qs t (fun j x => monoAND (mono j) x)) ↔
              ∃ v ∈ Finset.univ.image (countResVec qs (fun j x => monoAND (mono j) x)), G v = true)
            ∧ (Finset.univ.image (countResVec qs (fun j x => monoAND (mono j) x))).card < 2 ^ n :=
  ⟨modAnd_bottom_count_le mono hinj hdeg,
    count_crt_sat_speedup qs co hpos t (fun j x => monoAND (mono j) x) hregime⟩

/-- **The concrete `M = 6 = 2·3` top (proved).**  A `MOD_6` gate over distinct fan-in-`≤w` `AND`s: quasipoly bottom,
exact CRT-decoded top, SAT-searchable in `≤ 6` residue cells. -/
theorem mod6_and_exact_quasipoly_searchable {w : ℕ} (mono : Fin m → Finset (Fin n))
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ w) (t : ℕ) (hregime : 6 < 2 ^ n) :
    m ≤ ∑ i ∈ Finset.range (w + 1), n.choose i
      ∧ ∃ G : ((i : Fin ([2, 3] : List ℕ).length) → ZMod (([2, 3] : List ℕ).get i)) → Bool,
          (Satisfiable (modCountDecision [2, 3] t (fun j x => monoAND (mono j) x)) ↔
              ∃ v ∈ Finset.univ.image (countResVec [2, 3] (fun j x => monoAND (mono j) x)), G v = true)
            ∧ (Finset.univ.image (countResVec [2, 3] (fun j x => monoAND (mono j) x))).card < 2 ^ n := by
  refine modAnd_exact_quasipoly_searchable mono hinj hdeg [2, 3] (by decide) (by decide) t ?_
  rw [show ([2, 3] : List ℕ).prod = 6 from by decide]
  exact hregime

end PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyModTop

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyModTop.modAnd_bottom_count_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyModTop.modAnd_exact_observed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyModTop.modAnd_exact_quasipoly_searchable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyModTop.mod6_and_exact_quasipoly_searchable
