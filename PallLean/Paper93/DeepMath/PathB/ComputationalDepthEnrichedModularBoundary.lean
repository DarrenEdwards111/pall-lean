import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverACC0Frontier

/-!
# Enriched modular observer boundary, and an honest test of the ACC⁰ bridge half

`SCOPE_ACC0_OBSERVER_FRONTIER.md` §3 asks for an *enriched modular observer boundary* and a test of the
**bridge half**: does it model ACC⁰ circuits as low-boundary observers?  This file defines the boundary the
scope note proposes and tests it — and the test returns a precise, honest verdict (not the hoped-for clean
"AND/OR/NOT preserve low boundary", which is *false* for exact degree).

## Definition (per the scope note)

For a family `M` of moduli and a per-modulus feature dimension `prof : ℕ → ℕ` (the dimension of a function's
low-degree features over modulus `m`), the **enriched modular boundary** is

  `enrichedBoundary M prof = ∑_{m ∈ M} prof m`.

## What the structural lemmas give (proved)

* `enrichedBoundary_mono`, `enrichedBoundary_add` — monotone, and additive when profiles add (the shape AND/OR
  composition takes: exact multilinear degree of `f·g` adds).
* `enrichedBoundary_le_card_mul` — **the bridge, conditionally**: if *every* component is low (`prof m ≤ b`),
  the enriched boundary is `≤ |M|·b`.  So the enrichment composes across moduli with the dimension summing.
* `enrichedBoundary_ge_component` — **the obstruction**: the sum is `≥` *any single* component.  So if a
  function has even one *high* component, its enriched boundary is high.

## The honest verdict of the bridge test

The structural composition is fine, but the *semantic* inputs defeat the exact bridge:

* **A single `MOD_p` gate is NOT low across components.**  `MOD_p` is degree `≤ p−1` over `F_p` (low in its
  matching component) but **full degree** over `F_q` for `q ≠ p`.  By `enrichedBoundary_ge_component`, the
  sum then inherits that high `F_q` term — so `MOD_p` has *high* exact enriched boundary.  The naive sum does
  not make mixed-modulus gates low.
* **`AND` blows up exact degree.**  `AND` of `n` inputs has exact multilinear degree `n` over *every* field
  (the top monomial), so `enrichedBoundary_add` drives it to `≈ |M|·n` — not low.

So **the exact enriched boundary does NOT model ACC⁰ as low-boundary.**  This is the same wall RS hit for a
single field: the *exact* low-degree boundary fails under composition, and RS fixed it with **approximate
(probabilistic) polynomials**.  The honest conclusion: the enrichment is the right fix for the *moduli* (the
`∑` over `M`), but the boundary must be the **approximate** per-modulus degree, not the exact one — and a low
*approximate* enriched bridge for ACC⁰ over mixed moduli is the open frontier.  The exact version is either
high (obstruction) or, if one bounds it crudely, vacuous.

## What is proved (clean axioms, no `sorry`)

The structural lemmas above, plus `enrichedBoundary_two_moduli_obstruction` — a concrete witness that a gate
low in one modulus but high in another has high enriched boundary.  Nothing here claims a low *approximate*
enriched bridge (the open part); the file's value is pinning down precisely that **exact enrichment fails and
approximation is mandatory**, feeding `ObserverACC0.acc0_separation_of_boundary` with the right boundary
notion to aim for.
-/

namespace PallLean.Paper93.DeepMath.PathB.EnrichedModular

open scoped BigOperators

/-- **Enriched modular observer boundary**: the sum, over a family `M` of moduli, of the feature dimension
`prof m` of the function over each modulus. -/
def enrichedBoundary (M : Finset ℕ) (prof : ℕ → ℕ) : ℕ := ∑ m ∈ M, prof m

/-- Monotone in the per-modulus profile. -/
theorem enrichedBoundary_mono (M : Finset ℕ) {prof prof' : ℕ → ℕ}
    (h : ∀ m ∈ M, prof m ≤ prof' m) : enrichedBoundary M prof ≤ enrichedBoundary M prof' :=
  Finset.sum_le_sum h

/-- **Additive under profile addition** — the shape AND/OR composition takes (`deg (f·g) ≤ deg f + deg g`,
so exact-degree profiles add). -/
theorem enrichedBoundary_add (M : Finset ℕ) (prof prof' : ℕ → ℕ) :
    enrichedBoundary M (fun m => prof m + prof' m)
      = enrichedBoundary M prof + enrichedBoundary M prof' := by
  simp only [enrichedBoundary, Finset.sum_add_distrib]

/-- **The bridge, conditionally.**  If every component is low (`prof m ≤ b`), the enriched boundary is
`≤ |M|·b`.  The enrichment composes across moduli with the dimensions summing. -/
theorem enrichedBoundary_le_card_mul (M : Finset ℕ) {prof : ℕ → ℕ} {b : ℕ}
    (h : ∀ m ∈ M, prof m ≤ b) : enrichedBoundary M prof ≤ M.card * b := by
  calc enrichedBoundary M prof ≤ ∑ _m ∈ M, b := Finset.sum_le_sum h
    _ = M.card * b := by rw [Finset.sum_const, smul_eq_mul]

/-- **The obstruction direction.**  The enriched boundary is at least *any single* component: one high
component forces the whole sum high. -/
theorem enrichedBoundary_ge_component (M : Finset ℕ) (prof : ℕ → ℕ) {m₀ : ℕ} (hm₀ : m₀ ∈ M) :
    prof m₀ ≤ enrichedBoundary M prof :=
  Finset.single_le_sum (f := prof) (fun _ _ => Nat.zero_le _) hm₀

/-- A profile supported on a single modulus `m₀` has enriched boundary equal to that one component (the
"captured in its matching component" case — valid only when the function is genuinely low in *all other*
components, which fails for mixed-modulus gates). -/
theorem enrichedBoundary_single (M : Finset ℕ) {prof : ℕ → ℕ} {m₀ : ℕ} (hm₀ : m₀ ∈ M)
    (hsupp : ∀ m ∈ M, m ≠ m₀ → prof m = 0) :
    enrichedBoundary M prof = prof m₀ :=
  Finset.sum_eq_single_of_mem m₀ hm₀ (fun m hm hne => hsupp m hm hne)

/-- **Concrete obstruction (the bridge test verdict).**  Take two moduli `M = {p, q}` and a gate (e.g.
`MOD_p`) that is low over its matching modulus `p` (`prof p = lo`) but high over `q` (`prof q = hi`, the
full-degree blow-up of `MOD_p` over `F_q`).  Then its enriched boundary is `≥ hi` — **high**.  A single
mixed-modulus gate already defeats the *exact* enriched bridge; approximation is required. -/
theorem enrichedBoundary_two_moduli_obstruction {p q lo hi : ℕ} (hpq : p ≠ q)
    (prof : ℕ → ℕ) (hp : prof p = lo) (hq : prof q = hi) :
    hi ≤ enrichedBoundary {p, q} prof := by
  have hmem : q ∈ ({p, q} : Finset ℕ) := by simp
  calc hi = prof q := hq.symm
    _ ≤ enrichedBoundary {p, q} prof := enrichedBoundary_ge_component {p, q} prof hmem

end PallLean.Paper93.DeepMath.PathB.EnrichedModular

#print axioms PallLean.Paper93.DeepMath.PathB.EnrichedModular.enrichedBoundary_le_card_mul
#print axioms PallLean.Paper93.DeepMath.PathB.EnrichedModular.enrichedBoundary_two_moduli_obstruction
