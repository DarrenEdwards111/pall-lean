import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SingleSubsetF2

/-!
# Independence — the intersection of cylinder bad-events factorizes (the last probabilistic ingredient)

Entry 268 discharged the per-clause `1/2` (`SingleSubsetAgreement`).  The only ingredient still socketed for the
single-gate low-degree approximation (entry 267) is `IndependentIntersectionBound`: that the *joint* failure of the `k`
boosted clauses is `≤ 2^{-k}`.  This file proves it in the honest model where independence actually holds — the
**product space of the `k` independent random draws**.

**The model.**  The `k` clause indicators use `k` *independent* random subsets, so the boosting randomness space is the
product `∀ j, Y j` (`Y j` = the choices for the `j`-th draw).  The bad event of clause `j` is a **cylinder**: it depends
only on the `j`-th coordinate, `bad j = {y : y j ∈ B j}`.  The joint bad event `⋂ⱼ bad j = {y : ∀ j, y j ∈ B j}` is then
the product box `Fintype.piFinset B`, whose cardinality **factorizes**: `|⋂ⱼ bad j| = ∏ⱼ |B j|`.  With each clause bad
on at most half its draws (`2·|B j| ≤ |Y j|`, the per-clause `1/2` of entry 268), this gives `2^k·|⋂ⱼ bad j| ≤ ∏ⱼ |Y j|
= |total|` — joint failure `≤ 2^{-k}`.

## What is proved (clean axioms, no `sorry`)

* **`jointBad_card`** (PROVED) — the independence factorization: `|{y : ∀ j, y j ∈ B j}| = ∏ⱼ |B j|`
  (`Fintype.card_piFinset`).
* **`independent_intersection_bound`** (PROVED) — if each clause is bad on at most half its draws
  (`2·|B j| ≤ |Y j|`), then `2^k · |jointBad| ≤ ∏ⱼ |Y j|` (`Finset.prod_le_prod` + `Finset.prod_mul_distrib`).
* **`joint_error_le`** (PROVED) — equivalently `2^k · |jointBad| ≤ |∀ j, Y j|` (`Fintype.card_pi`): the joint failure
  is `≤ 2^{-k}` of the whole randomness space.  **`IndependentIntersectionBound` is discharged in the product model.**

## Honest scope

This proves the independence factorization and the `2^{-k}` joint-failure bound in the product-of-independent-draws
model — the only ingredient entry 267 still socketed.  Composed with the proved per-clause `1/2` (entry 268, supplying
`2·|B j| ≤ |Y j|`) and the proved boosting (entry 267, `bad(boost) ⊆ ⋂ⱼ bad j`), it gives a single-gate degree-`k(p-1)`
approximation with error `≤ 2^{-k}`.  What remains is the *structural* lifting single-gate → circuit → observer (the
`PolynomialMethodApproximation` glue).  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0Independence

variable {k : ℕ} (Y : Fin k → Type) [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]

/-- **The independence factorization (PROVED).**  The joint bad event `{y : ∀ j, y j ∈ B j}` (the intersection of the
`k` cylinder bad-events) is the product box `Fintype.piFinset B`, whose cardinality factorizes as `∏ⱼ |B j|` — the
cardinality form of independence. -/
theorem jointBad_card (B : ∀ j, Finset (Y j)) :
    (Fintype.piFinset B).card = ∏ j, (B j).card :=
  Fintype.card_piFinset B

/-- **The independence intersection bound (PROVED).**  If each clause is bad on at most half its draws
(`2·|B j| ≤ |Y j|`), then `2^k · |jointBad| ≤ ∏ⱼ |Y j|`: the joint failure shrinks by a factor `2^k`.  (Pull `2^k`
inside the product as `∏ⱼ 2` and compare factorwise.) -/
theorem independent_intersection_bound (B : ∀ j, Finset (Y j))
    (h : ∀ j, 2 * (B j).card ≤ Fintype.card (Y j)) :
    2 ^ k * (Fintype.piFinset B).card ≤ ∏ j, Fintype.card (Y j) := by
  rw [Fintype.card_piFinset]
  have h2 : (2 : ℕ) ^ k = ∏ _j : Fin k, 2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => h j)

/-- **Joint failure `≤ 2^{-k}` (PROVED).**  Equivalently `2^k · |jointBad| ≤ |∀ j, Y j|`: the `k` independent clauses
fail simultaneously on at most a `2^{-k}` fraction of the randomness space.  **This discharges
`IndependentIntersectionBound` (entry 267) in the product-of-independent-draws model.** -/
theorem joint_error_le (B : ∀ j, Finset (Y j))
    (h : ∀ j, 2 * (B j).card ≤ Fintype.card (Y j)) :
    2 ^ k * (Fintype.piFinset B).card ≤ Fintype.card (∀ j, Y j) := by
  rw [Fintype.card_pi]
  exact independent_intersection_bound Y B h

/-!
**The rung.**  The independence factorization (`jointBad_card`: `|⋂ⱼ bad j| = ∏ⱼ |B j|`) and the `2^{-k}` joint-failure
bound (`joint_error_le`: `2^k·|jointBad| ≤ |total|`) are proved in the product-of-independent-draws model — the honest
model where the `k` random subsets are independent.  This discharges the last probabilistic ingredient entry 267 left
(`IndependentIntersectionBound`).  Composed with the proved per-clause `1/2` (entry 268, which supplies
`2·|B j| ≤ |Y j|`) and the proved boosting error-set intersection (entry 267, `bad(boost) ⊆ ⋂ⱼ bad j`), the single-gate
degree-`k(p-1)`, error-`2^{-k}` approximation is assembled.  The only remaining open piece is the *structural* lifting
single-gate → circuit → observer (`PolynomialMethodApproximation`).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Independence

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Independence.jointBad_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Independence.independent_intersection_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Independence.joint_error_le
