import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimeMODMvPoly

/-!
# Brick D — quasipolynomial monomial count for `SYM∘AND` packaging (proved)

The `SYM∘AND` form of Yao–Beigel–Tarui writes a degree-`≤ D` polynomial as a symmetric function over its monomials, each a
multilinear `AND` of `≤ D` variables.  The crucial quantitative fact — the one that makes the form *quasipolynomial* — is
that there are at most `(n+1)^D` such monomials (subsets of `Fin n` of size `≤ D`): for `D = polylog`, `(n+1)^D =
2^{polylog · log n}` is quasipolynomial, `< 2^n`.

This file proves exactly that count, via a surjection from `Fin D → Option (Fin n)` (list a subset's `≤ D` elements, pad
with `none`) onto the degree-`≤ D` monomials.

## What is proved (clean axioms, no `sorry`)

* **`degLeMonomials n D`** — the degree-`≤ D` multilinear monomials = subsets of `Fin n` of size `≤ D` (each an `AND` of
  `≤ D` variables).
* **`degLeMonomials_card_le`** (PROVED) — `(degLeMonomials n D).card ≤ (n+1)^D`: the quasipolynomial monomial bound.

## Honest scope

This is the **monomial-count** core of `SYM∘AND` packaging (the quasipoly size).  It does **not** assemble the full
symmetric-count `SYM∘AND` form, the prime-power (`e≥2`) Toda lifting, nor degree-additive depth composition — i.e. general
YBT / `composite_BT_degree` remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MonomialCount

open Finset

/-- **The degree-`≤ D` multilinear monomials:** subsets of `Fin n` of size `≤ D` (each an `AND` of `≤ D` variables). -/
def degLeMonomials (n D : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter (fun S => S.card ≤ D)

/-- **The quasipolynomial monomial bound (PROVED): `≤ (n+1)^D` degree-`≤ D` monomials.** -/
theorem degLeMonomials_card_le (n D : ℕ) : (degLeMonomials n D).card ≤ (n + 1) ^ D := by
  have hsrc : (Finset.univ : Finset (Fin D → Option (Fin n))).card = (n + 1) ^ D := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_fin]
  rw [← hsrc]
  refine Finset.card_le_card_of_surjOn
    (fun t => Finset.univ.filter (fun i => ∃ k, t k = some i)) ?_
  intro S hS
  simp only [degLeMonomials, coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hS
  refine ⟨fun k => S.toList[(k : ℕ)]?, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    exact Finset.mem_toList.mp (List.mem_of_getElem? hk)
  · intro hi
    obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp (Finset.mem_toList.mpr hi)
    have hlen : idx < S.toList.length := (List.getElem?_eq_some_iff.mp hidx).1
    have hidxD : idx < D := by rw [Finset.length_toList] at hlen; omega
    exact ⟨⟨idx, hidxD⟩, hidx⟩

/-!
**The quasipolynomial monomial count, proved.**  A degree-`≤ D` polynomial has `≤ (n+1)^D` monomials (`AND`-terms) —
quasipolynomial for `D = polylog`, the size guarantee of the `SYM∘AND` form.  Next: assemble the symmetric-count form, and
the prime-power lifting + degree composition — the remaining content of general YBT.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MonomialCount

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MonomialCount.degLeMonomials_card_le
