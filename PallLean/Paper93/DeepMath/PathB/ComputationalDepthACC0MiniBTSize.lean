import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MiniBTTwoCount

/-!
# The mini-Beigel–Tarui collapse, with size — the multiplicative blow-up made explicit (PROVED)

`ACC0MiniBTTwoCount` proves the two-count layer-merge collapse *exactly* (`miniBT_two_count_collapse`)
but **size-blind** (the `SYM∘AND` it returns has no tracked gate count).  The file's prose identifies
the real wall — the merge's **multiplicative** size blow-up compounding to a tower over depth.  This
file turns that into a **theorem**: a size-tracking collapse, and the quantitative blow-up.

  `miniBT_collapse_size` — a joint two-count rep over layers of sizes `sz₁, sz₂` collapses to a
  *single*-count `SYM∘AND` over a merged layer of **exactly `sz₁·(sz₂+1) + sz₂`** gates (mixed-radix
  encoding).

  `merge_size_ge_mul` — that merged size is `≥ sz₁·sz₂`: the blow-up is **multiplicative**, so iterating
  the merge over circuit depth compounds into a tower — precisely why the *exact* encoding cannot stay
  quasipolynomial, and the genuine Beigel–Tarui theorem instead uses probabilistic polynomials.

## What is proved (clean axioms, no `sorry`)

* `HasSymAndRepSize` / `HasBinarySymRepSize` — size-indexed SYM∘AND / joint-two-count predicates.
* `miniBT_collapse_size` — the exact size-tracking two-count collapse, merged size `sz₁·(sz₂+1)+sz₂`.
* `merge_size_ge_mul` — the merge size is `≥ sz₁·sz₂` (the multiplicative blow-up).

## Honest scope

The collapse is exact and now its size is explicit and multiplicative.  The open content is unchanged:
keeping the size *quasipolynomial across `ω(1)` depth* — the exact merge towers, so the genuine
quasipoly `SYM∘AND` representation needs the probabilistic-polynomial machinery (the open
`composite_BT_degree`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MiniBTSize

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount

variable {n : ℕ}

/-- **Size-indexed `SYM∘AND` representation**: `F` is a symmetric function of the count over a bottom
layer of exactly `sz` `AND` gates. -/
def HasSymAndRepSize (F : (Fin n → Bool) → Bool) (sz : ℕ) : Prop :=
  ∃ (supp : Fin sz → Finset (Fin n)) (sym : ℕ → Bool), ∀ x, F x = sym (satCount supp x)

/-- **Size-indexed joint two-count representation**: `F` is a joint function of the counts over two
bottom layers of sizes `sz₁, sz₂`. -/
def HasBinarySymRepSize (F : (Fin n → Bool) → Bool) (sz1 sz2 : ℕ) : Prop :=
  ∃ (s1 : Fin sz1 → Finset (Fin n)) (s2 : Fin sz2 → Finset (Fin n)) (j : ℕ → ℕ → Bool),
    ∀ x, F x = j (satCount s1 x) (satCount s2 x)

/-- **The size-tracking two-count collapse (proved).**  A joint two-count representation over layers of
sizes `sz₁, sz₂` collapses to a single-count `SYM∘AND` over a merged layer of exactly
`sz₁·(sz₂+1) + sz₂` gates, via the mixed-radix encoding `c⋆ = (sz₂+1)·c₁ + c₂` on the layer
`(s₁ replicated sz₂+1 times) ++ s₂`. -/
theorem miniBT_collapse_size {F : (Fin n → Bool) → Bool} {sz1 sz2 : ℕ}
    (h : HasBinarySymRepSize F sz1 sz2) :
    HasSymAndRepSize F (sz1 * (sz2 + 1) + sz2) := by
  obtain ⟨s1, s2, j, hF⟩ := h
  let se : (Fin sz1 × Fin (sz2 + 1)) ⊕ Fin sz2 → Finset (Fin n) :=
    Sum.elim (fun p => s1 p.1) s2
  have hcard : Fintype.card ((Fin sz1 × Fin (sz2 + 1)) ⊕ Fin sz2) = sz1 * (sz2 + 1) + sz2 := by
    simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  let e : Fin (sz1 * (sz2 + 1) + sz2) ≃ ((Fin sz1 × Fin (sz2 + 1)) ⊕ Fin sz2) :=
    (Fintype.equivFinOfCardEq hcard).symm
  have hcount : ∀ x, satCountF se x = (sz2 + 1) * satCountF s1 x + satCountF s2 x := by
    intro x
    show satCountF (Sum.elim (fun p : Fin sz1 × Fin (sz2 + 1) => s1 p.1) s2) x = _
    rw [satCountF_sumElim, satCountF_replicate]
  have hc2 : ∀ x, satCountF s2 x < sz2 + 1 := by
    intro x
    have := satCountF_le_card s2 x
    rw [Fintype.card_fin] at this
    omega
  refine ⟨fun jx => se (e jx), fun s => j (s / (sz2 + 1)) (s % (sz2 + 1)), fun x => ?_⟩
  have hsc : satCount (fun jx => se (e jx)) x = satCountF se x := by
    rw [satCount_eq_satCountF]
    exact Equiv.sum_comp e (fun i => if monoAND (se i) x = true then 1 else 0)
  rw [hF x, satCount_eq_satCountF s1 x, satCount_eq_satCountF s2 x, hsc, hcount x]
  dsimp only
  rw [Nat.mul_add_div (show 0 < sz2 + 1 by omega), Nat.mul_add_mod_self_left,
    Nat.div_eq_of_lt (hc2 x), Nat.mod_eq_of_lt (hc2 x), add_zero]

/-- **The merge size is multiplicative (proved): `sz₁·(sz₂+1) + sz₂ ≥ sz₁·sz₂`.**  Each exact two-count
merge is at least the *product* of the two layer sizes — so iterating over circuit depth compounds into
a tower, which is exactly why the exact mixed-radix encoding cannot remain quasipolynomial. -/
theorem merge_size_ge_mul (sz1 sz2 : ℕ) : sz1 * sz2 ≤ sz1 * (sz2 + 1) + sz2 := by
  have : sz1 * sz2 ≤ sz1 * (sz2 + 1) := Nat.mul_le_mul_left sz1 (by omega)
  omega

/-!
**Size-tracking collapse proved.**  The exact two-count merge produces a single-count `SYM∘AND` of
*exactly* `sz₁·(sz₂+1)+sz₂ ≥ sz₁·sz₂` gates — the multiplicative blow-up, now a theorem.  Iterated over
`ω(1)` depth this towers, so the *exact* route cannot keep quasipolynomial size; the genuine
quasipoly `SYM∘AND` needs probabilistic polynomials (`composite_BT_degree`, open).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MiniBTSize

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MiniBTSize.miniBT_collapse_size
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MiniBTSize.merge_size_ge_mul
