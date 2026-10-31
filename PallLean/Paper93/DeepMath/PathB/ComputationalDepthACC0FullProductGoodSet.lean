import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SmolenskyDegreeHalving

/-!
# The prime-case wiring lemma — replacing the full product by the approximator on the good set

Roadmap step 1.  Entry 276 proved the degree-halving substitution `∏_{i∈S} yᵢ = (∏ᵢ yᵢ)·(∏_{i∈Sᶜ} yᵢ)`.  Its residual
socket `FullProductLowDegreeOnGoodSet` needs: *on the good set, the full product `∏ᵢ yᵢ` (the hard symmetric
`MOD`/parity function) equals the degree-`D` approximator `P`*.  This file is the clean bridge connecting entry 276 to
the proven approximation machinery (boosting, entry 267; `Approximable`, the committed arc): it shows that **the
agreement hypothesis `P = ∏ᵢ yᵢ` on the good set is exactly what lets the full product be replaced by `P` inside the
degree-halving argument**.

**The wiring (proved).**  For inputs `x` in the good set `G`, if the approximator agrees with the full product
(`P x = ∏ᵢ yencₓ i`), then by the substitution identity (entry 276) the high-degree monomial collapses:

> `∏_{i∈S} yencₓ i = P x · ∏_{i∈Sᶜ} yencₓ i`   for `x ∈ G`.

So on `G`, a degree-`|S|` monomial equals (approximator, degree `D`) × (complement monomial, degree `|Sᶜ| < n/2` when
`|S| > n/2`) — degree `≤ D + n/2`.  The agreement hypothesis is precisely the output of the approximation machinery (the
`AC⁰[p]` approximator agreeing with the symmetric target off a small bad set, the good set being its complement).

## What is proved (clean axioms, no `sorry`)

* **`fullProduct_replace_on_goodSet`** (PROVED) — the wiring: given `P x = ∏ᵢ yencₓ i` on `G`, then
  `∏_{i∈S} yencₓ i = P x · ∏_{i∈Sᶜ} yencₓ i` on `G` (substitute the agreement into entry-276's
  `smolensky_substitution`).
* **`monomial_eq_approx_times_lowComplement`** (PROVED) — the degree-halving packaged: on `G` the high-degree monomial
  (`|S| > n/2`) equals `P x ·` (complement monomial) *and* the complement has `2·|Sᶜ| < n` factors (entry 276) — i.e.
  approximator × sub-half-degree complement.

## The remaining socket

* **`ApproximatorDegreeBound`** — `P` has degree `≤ D`, so `P x · ∏_{i∈Sᶜ} yencₓ i` (a degree-`D` polynomial times a
  degree-`|Sᶜ|` monomial) has degree `≤ D + |Sᶜ| ≤ D + n/2`, i.e. the good-set point functions lie in
  `lowDegreeSubmodule n (D + n/2)` — discharging `SmolenskyDegreeHalving` (entry 275/276).  This is polynomial-degree
  bookkeeping (degree of a product); the agreement input itself is now wired.

## Honest scope

This proves the wiring lemma — given the approximator agrees with the full product on the good set, the full product is
replaced by the approximator inside the degree-halving (the high-degree monomial becomes approximator × sub-half-degree
complement).  The agreement hypothesis is exactly what the proven approximation machinery (boosting 267 / `Approximable`)
supplies; the remaining `ApproximatorDegreeBound` is product-degree bookkeeping.  Prime case = textbook Smolensky;
**composite modulus is untouched** (the open `CarryRefinementCrossing` wall, entry 238).  This is **not** `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullProductGoodSet

open PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyDegreeHalving (smolensky_substitution compl_card_lt_half)

/-- **The wiring lemma (PROVED).**  If the approximator `P` agrees with the full product `∏ᵢ yencₓ i` on the good set
`G`, then on `G` a monomial over `S` collapses to the approximator times the complement monomial:
`∏_{i∈S} yencₓ i = P x · ∏_{i∈Sᶜ} yencₓ i`.  (Evaluate entry-276's substitution at `x` and replace `∏ᵢ yencₓ i` by
`P x` using the agreement.)  This replaces the hard full product by the degree-`D` approximator inside the degree-halving
argument — the bridge from entry 276 to the approximation machinery. -/
theorem fullProduct_replace_on_goodSet {F : Type} [CommRing F] {n : ℕ} {X : Type}
    (yenc : X → Fin n → F) (hy : ∀ x i, (yenc x i) ^ 2 = 1)
    (P : X → F) (G : Finset X) (S : Finset (Fin n))
    (hP : ∀ x ∈ G, P x = ∏ i, yenc x i) :
    ∀ x ∈ G, (∏ i ∈ S, yenc x i) = P x * (∏ i ∈ Sᶜ, yenc x i) := by
  intro x hx
  rw [hP x hx]
  exact smolensky_substitution (yenc x) (fun i => hy x i) S

/-- **The degree-halving packaged (PROVED).**  For a high-degree set `|S| > n/2`, on the good set the monomial equals the
approximator times the complement monomial, and the complement has `2·|Sᶜ| < n` factors (entry 276): a degree-`|S|`
monomial becomes (approximator, degree `D`) × (sub-half-degree complement).  With `ApproximatorDegreeBound` (degree of a
product) this gives degree `≤ D + n/2` — `SmolenskyDegreeHalving`. -/
theorem monomial_eq_approx_times_lowComplement {F : Type} [CommRing F] {n : ℕ} {X : Type}
    (yenc : X → Fin n → F) (hy : ∀ x i, (yenc x i) ^ 2 = 1)
    (P : X → F) (G : Finset X) (S : Finset (Fin n))
    (hP : ∀ x ∈ G, P x = ∏ i, yenc x i) (hS : n < 2 * S.card) :
    (∀ x ∈ G, (∏ i ∈ S, yenc x i) = P x * (∏ i ∈ Sᶜ, yenc x i)) ∧ 2 * Sᶜ.card < n :=
  ⟨fullProduct_replace_on_goodSet yenc hy P G S hP, compl_card_lt_half S hS⟩

/-- **The product-degree socket (polynomial bookkeeping, NOT proved here).**  The approximator `P` has degree `≤ D`, so
`P x · ∏_{i∈Sᶜ} yencₓ i` (degree-`D` polynomial × degree-`|Sᶜ|` monomial) has degree `≤ D + |Sᶜ| ≤ D + n/2`.  Hence the
good-set point functions lie in `lowDegreeSubmodule n (D + n/2)`, discharging `SmolenskyDegreeHalving` (entry 275/276).
Polynomial-degree bookkeeping; the agreement input is now wired (`fullProduct_replace_on_goodSet`). -/
def ApproximatorDegreeBound (ProductDegreeLe : Prop) : Prop :=
  ProductDegreeLe

/-!
**The bridge.**  The degree-halving residual `FullProductLowDegreeOnGoodSet` (entry 276) is now connected to the
approximation machinery: `fullProduct_replace_on_goodSet` proves that *the agreement of the approximator with the full
product on the good set* (the output of boosting/`Approximable`) is exactly what replaces the hard full product by the
degree-`D` approximator inside the degree-halving — a high-degree monomial becomes approximator × sub-half-degree
complement on `G`.  The only residue is `ApproximatorDegreeBound` (product-degree bookkeeping).  Combined with entry-276's
substitution and entry-275's pigeonhole, this is the prime-case Smolensky closure — *composite modulus stays the open
`CarryRefinementCrossing` wall* (entry 238).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullProductGoodSet

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullProductGoodSet.fullProduct_replace_on_goodSet
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullProductGoodSet.monomial_eq_approx_times_lowComplement
