import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SmolenskyPigeonhole

/-!
# The Smolensky degree-halving — the prime-case substitution identity (textbook Smolensky)

Entry 275 reduced the wall to the single socket `SmolenskyDegreeHalving` (the Razborov–Smolensky representation lemma).
This file attacks its **prime case only**, scoped explicitly to *textbook* Smolensky — *composite modulus is untouched*
(that is the `CarryRefinementCrossing` wall, entry 238).

**The algebraic core of degree-halving (proved).**  Over the `{±1}` encoding — values `y : Fin n → F` with `yᵢ² = 1`
(the `p`-odd Smolensky setting, where `±1` are distinct) — a monomial over a set `S` satisfies the **substitution
identity**

> `∏_{i∈S} yᵢ = (∏_{i} yᵢ) · (∏_{i∈Sᶜ} yᵢ)`,

because `(∏_{Sᶜ} yᵢ)² = ∏_{Sᶜ} yᵢ² = 1`.  When `|S| > n/2`, the complement `Sᶜ` has `< n/2` factors
(`compl_card_lt_half`).  So a *high-degree* monomial equals the *full* product times a *low-degree* (`< n/2`) complement
— and replacing the full product `∏ᵢ yᵢ` by the degree-`D` approximator on the good set (the circuit/`MOD_q`-specific
input, socketed) halves every monomial's degree to `≤ n/2 + D`.

## What is proved (clean axioms, no `sorry`)

* **`smolensky_substitution`** (PROVED) — the degree-halving substitution: for `yᵢ² = 1`,
  `∏_{i∈S} yᵢ = (∏ᵢ yᵢ) · (∏_{i∈Sᶜ} yᵢ)` (`Finset.prod_mul_prod_compl` + `(∏_{Sᶜ} yᵢ)² = 1`).
* **`compl_card`** (PROVED) — `|Sᶜ| = n − |S|` (`Finset.card_compl`).
* **`compl_card_lt_half`** (PROVED) — if `n < 2·|S|` (i.e. `|S| > n/2`) then `2·|Sᶜ| < n` (the complement is below the
  half-degree threshold).
* **`monomial_halving`** (PROVED) — the combined step: for `|S| > n/2`, the monomial `∏_{i∈S} yᵢ` equals
  `(∏ᵢ yᵢ) · (∏_{i∈Sᶜ} yᵢ)` with `2·|Sᶜ| < n` — high-degree monomial = full product × sub-half-degree complement.

## The remaining socket (the circuit/`MOD_q`-specific input)

* **`FullProductLowDegreeOnGoodSet`** — on the good set `G`, the full product `∏ᵢ yᵢ` (the symmetric `MOD`-type function)
  equals a degree-`D` polynomial (the `AC⁰[p]` approximator).  Combined with `monomial_halving`, every monomial — hence
  every function — on `G` has degree `≤ n/2 + D`, which is `SmolenskyDegreeHalving` (entry 275).  The prime-case
  approximator input; *composite* modulus is the open `CarryRefinementCrossing` wall (entry 238).

## Honest scope

This proves the *algebraic core* of the prime-case Smolensky degree-halving — the `{±1}` substitution identity and the
complement-counting that make a high-degree monomial collapse to (full product) × (sub-half-degree complement).  The
remaining input — replacing the full product by the degree-`D` approximator on the good set
(`FullProductLowDegreeOnGoodSet`) — is the circuit-specific socket; supplying it (prime case) discharges
`SmolenskyDegreeHalving` (entry 275) and, with the proved pigeonhole, the prime-`MOD` lower bound.  **Composite modulus
is untouched** — the open `ACC⁰[composite]` wall.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyDegreeHalving

/-- **The Smolensky degree-halving substitution (PROVED).**  Over the `{±1}` encoding (`yᵢ² = 1`), a monomial over `S`
equals the full product times the complement monomial: `∏_{i∈S} yᵢ = (∏ᵢ yᵢ) · (∏_{i∈Sᶜ} yᵢ)`.  (The full product is
`∏_S · ∏_{Sᶜ}`, and `(∏_{Sᶜ})² = ∏_{Sᶜ} yᵢ² = 1`, so the right side collapses to `∏_S`.)  This is the algebraic core of
degree-halving: it trades a degree-`|S|` monomial for the full product times a degree-`|Sᶜ|` complement. -/
theorem smolensky_substitution {F : Type} [CommRing F] {n : ℕ} (y : Fin n → F)
    (hy : ∀ i, y i ^ 2 = 1) (S : Finset (Fin n)) :
    (∏ i ∈ S, y i) = (∏ i, y i) * (∏ i ∈ Sᶜ, y i) := by
  have hall : (∏ i, y i) = (∏ i ∈ S, y i) * (∏ i ∈ Sᶜ, y i) :=
    (Finset.prod_mul_prod_compl S y).symm
  have hsq : (∏ i ∈ Sᶜ, y i) * (∏ i ∈ Sᶜ, y i) = 1 :=
    (Finset.prod_mul_distrib).symm.trans
      (Finset.prod_eq_one (fun i _ => (pow_two (y i)).symm.trans (hy i)))
  linear_combination (-(∏ i ∈ Sᶜ, y i)) * hall - (∏ i ∈ S, y i) * hsq

/-- **The complement cardinality (PROVED).**  `|Sᶜ| = n − |S|`. -/
theorem compl_card {n : ℕ} (S : Finset (Fin n)) : Sᶜ.card = n - S.card := by
  rw [Finset.card_compl, Fintype.card_fin]

/-- **The complement is below half-degree (PROVED).**  If `|S| > n/2` (`n < 2·|S|`), then `2·|Sᶜ| < n`: the complement
monomial has degree below the half-threshold. -/
theorem compl_card_lt_half {n : ℕ} (S : Finset (Fin n)) (h : n < 2 * S.card) :
    2 * Sᶜ.card < n := by
  have hcard := compl_card S
  have hle : S.card ≤ n := by
    have hsu := Finset.card_le_univ S
    rwa [Fintype.card_fin] at hsu
  omega

/-- **The monomial halving step (PROVED).**  For a high-degree set `|S| > n/2`, the monomial `∏_{i∈S} yᵢ` equals the full
product times a complement monomial whose degree is below the half-threshold (`2·|Sᶜ| < n`).  Replacing the full product
by the degree-`D` approximator on the good set then gives degree `≤ n/2 + D` — the degree-halving. -/
theorem monomial_halving {F : Type} [CommRing F] {n : ℕ} (y : Fin n → F)
    (hy : ∀ i, y i ^ 2 = 1) (S : Finset (Fin n)) (h : n < 2 * S.card) :
    (∏ i ∈ S, y i) = (∏ i, y i) * (∏ i ∈ Sᶜ, y i) ∧ 2 * Sᶜ.card < n :=
  ⟨smolensky_substitution y hy S, compl_card_lt_half S h⟩

/-- **The good-set full-product socket (the circuit/`MOD_q`-specific input, NOT proved).**  On the good set `G`, the full
product `∏ᵢ yᵢ` (the symmetric `MOD`-type function the circuit computes) equals a degree-`D` polynomial — the `AC⁰[p]`
approximator.  Combined with `monomial_halving`, this halves every monomial's degree to `≤ n/2 + D` on `G`, discharging
`SmolenskyDegreeHalving` (entry 275).  Prime case = textbook Smolensky; *composite* modulus is the open
`CarryRefinementCrossing` wall (entry 238). -/
def FullProductLowDegreeOnGoodSet (FullProductIsDegreeD : Prop) : Prop :=
  FullProductIsDegreeD

/-!
**The prime-case attack.**  The algebraic core of Smolensky's degree-halving is proved: over the `{±1}` encoding, a
high-degree monomial `∏_{i∈S} yᵢ` (`|S| > n/2`) equals the full product `∏ᵢ yᵢ` times a complement monomial of degree
`< n/2` (`monomial_halving`, via `smolensky_substitution` + `compl_card_lt_half`).  The one remaining input is
`FullProductLowDegreeOnGoodSet` — replacing the full product by the degree-`D` `AC⁰[p]` approximator on the good set —
after which every monomial on `G` has degree `≤ n/2 + D`, i.e. `SmolenskyDegreeHalving` (entry 275), and with the proved
pigeonhole (275) the prime-`MOD` lower bound follows.  **Composite modulus is untouched** — the open
`CarryRefinementCrossing` wall (entry 238).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyDegreeHalving

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyDegreeHalving.smolensky_substitution
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyDegreeHalving.compl_card_lt_half
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmolenskyDegreeHalving.monomial_halving
