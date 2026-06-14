import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymmetricExact
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd

/-!
# A toy *exact-and-quasipolynomial* `SYM∘AND` — the one fragment that beats the wall

Wall 1 (`WHAT_IS_PROVED.md`) is the tension that, for general `ACC⁰`, an *exact* `SYM∘AND` forces *exponential* size
(`exact_depth_composes`: `2^k`) while *quasipolynomial* size needs the *approximate* Razborov–Smolensky polynomial.
The two cannot be had at once in general — that is the Beigel–Tarui analytic core.

This file exhibits the **one restricted fragment where exact *and* quasipolynomial hold simultaneously**: a depth-2
`OR ∘ AND_w` circuit — a DNF whose bottom `AND` gates have **bounded fan-in `≤ w`** and are **distinct**.  The reason
the wall lifts here is structural and exact, not approximate:

* a bottom `AND` of fan-in `≤ w` (`monoAND S`, `|S| ≤ w`) **is** the degree-`≤w` monomial — a *genuine* `AND` gate,
  no approximation; bounded fan-in keeps the degree bounded **exactly**;
* there are only `∑_{i≤w} C(n,i)` distinct degree-`≤w` monomials, so the bottom layer has **quasipolynomially many**
  gates (`n^{O(w)}`, quasipoly for `w = polylog n`);
* the top `OR` is **exactly** the symmetric count gate `[count ≥ 1]` (`or_exact_sym`, no approximation).

So `OR ∘ AND_w` is an *exact* `SYM∘AND` of *quasipolynomial* size — both at once.  The general wall is precisely the
loss of any one of these three: *unbounded* fan-in `AND` (degree = fan-in, up to `n`), the `MOD` layer (needs the RS
approximation to get low degree), or *arbitrary depth* (degree multiplies across layers).

## What is proved (clean axioms, no `sorry`)

* `dnf_exact_symAnd` — the depth-2 DNF `OR_j (AND of mono j)` **equals exactly** `symEval (monoAND ∘ mono) [1 ≤ ·]`
  (`or_exact_sym`, EXACT).
* `dnf_bottom_count_le` — distinct bottom monomials of fan-in `≤ w` number `≤ ∑_{i≤w} C(n,i)` (quasipoly).
* `dnf_exact_quasipoly_searchable` — **both at once**: the DNF is *exactly* a `SYM∘AND`, *and* (once the quasipoly
  bottom-gate count `+1 < 2^n`) is SAT-searchable in `< 2^n` cells.

## Honest scope

This is genuinely *exact and quasipolynomial together* — the property the general `ACC⁰` wall (Wall 1) cannot
deliver — but **only** for the restricted depth-2 bounded-fan-in `DNF` fragment.  It does **not** extend to unbounded
fan-in, to the `MOD` layer, or across general depth: those are exactly where exactness forces exponential size (the
front half of Beigel–Tarui, `MixedACCDepthReductionSocket` / `HasExactSymAndForm`).  It is still the cell/observer
model; a `< 2^n` cell count is not a uniform algorithm (Wall 2).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth2

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricExact
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd

variable {n m : ℕ}

/-- **The depth-2 DNF equals an *exact* `SYM∘AND` (proved).**  An `OR` over `m` monomial-`AND` bottom gates is
*exactly* the symmetric count gate `[count ≥ 1]` over them — no approximation. -/
theorem dnf_exact_symAnd (mono : Fin m → Finset (Fin n)) :
    (fun x => decide (∃ j, monoAND (mono j) x = true))
      = symEval (fun j x => monoAND (mono j) x) (fun k => decide (1 ≤ k)) :=
  or_exact_sym (fun j x => monoAND (mono j) x)

/-- **The bottom layer is quasipolynomial (proved).**  Distinct bottom `AND` gates of fan-in `≤ w` number at most
`∑_{i≤w} C(n,i)` — the count of degree-`≤w` monomials (`n^{O(w)}`, quasipoly for `w = polylog n`). -/
theorem dnf_bottom_count_le {w : ℕ} (mono : Fin m → Finset (Fin n))
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ w) :
    m ≤ ∑ i ∈ Finset.range (w + 1), n.choose i :=
  monomial_count_le mono hinj hdeg

/-- **Exact *and* quasipolynomial, simultaneously (proved).**  A depth-2 DNF whose bottom `AND` gates have fan-in
`≤ w` and are distinct is **exactly** a `SYM∘AND` (no approximation), **and** — once the quasipolynomial bottom-gate
count satisfies `(∑_{i≤w} C(n,i)) + 1 < 2^n` — is SAT-searchable in `< 2^n` cells.  This is the property the general
`ACC⁰` wall cannot have at once; here bounded fan-in `w` supplies it exactly. -/
theorem dnf_exact_quasipoly_searchable {w : ℕ} (mono : Fin m → Finset (Fin n))
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ w)
    (hregime : (∑ i ∈ Finset.range (w + 1), n.choose i) + 1 < 2 ^ n) :
    (fun x => decide (∃ j, monoAND (mono j) x = true))
        = symEval (fun j x => monoAND (mono j) x) (fun k => decide (1 ≤ k))
      ∧ (Satisfiable (fun x => decide (∃ j, monoAND (mono j) x = true)) ↔
            ∃ c ∈ Finset.univ.image (gateCount (fun j x => monoAND (mono j) x)), decide (1 ≤ c) = true)
        ∧ (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card < 2 ^ n := by
  have hm : m + 1 < 2 ^ n :=
    lt_of_le_of_lt (Nat.add_le_add_right (dnf_bottom_count_le mono hinj hdeg) 1) hregime
  exact ⟨dnf_exact_symAnd mono, or_exact_searchable (fun j x => monoAND (mono j) x) hm⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth2

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth2.dnf_exact_symAnd
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth2.dnf_bottom_count_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactQuasipolyDepth2.dnf_exact_quasipoly_searchable
