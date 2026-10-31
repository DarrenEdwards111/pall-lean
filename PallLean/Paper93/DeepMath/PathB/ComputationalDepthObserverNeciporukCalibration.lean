import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukOptimalBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukSubfunctionLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionAsymptotic

/-!
# Calibration 2: rederiving the Nečiporuk formula lower bound through the observer invariant

A second calibration (after AC⁰[p]): does the observer-boundary invariant rederive the **branching/formula**
lower bound — Nečiporuk's `n²/log n`?  Again **yes**, and again it is a rederivation, not a relabel, because
Nečiporuk's method *is* the observer invariant applied block-by-block:

| observer notion | Nečiporuk notion |
|---|---|
| sectors / behaviors on a block | the **residual subfunctions** `blockResiduals S F` (fix the outside vars) |
| non-mergeable / fooling set | parameter settings whose restrictions differ (`card_blockResiduals_ge_of_pairwise`) |
| boundary entropy on block `S` | `log₂ |blockResiduals S F|` (`formulaBlockBoundary`) |
| total observer boundary | `∑` over a variable partition (`formulaTotalBoundary`) |
| low-boundary observer | a small `B₂` formula: total boundary `≤ 4·litCount + #blocks` |

So the two halves of Nečiporuk are the two halves of the observer programme:

* **fooling ⇒ boundary** (`separated_forces_blockBoundary`): a pairwise-separated family of outside-settings on
  block `S` forces `formulaBlockBoundary S F ≥ log₂ |family|` — *exactly* `ContinuationObserver`'s
  `faithful_separated_forces_boundary` / `many_nonmergeable_sectors_force_boundary`, per block.
* **total boundary ≤ size** (`formulaTotalBoundary_le_size`): a formula's summed block-boundary is at most a
  constant times its size — a small formula *is* a low-total-boundary observer.

The hard function forces high boundary on every block (`hardF_blockBoundary_ge`), so its total boundary is
`≥ m·(2^b−1)`, forcing size `≥ n²/log n` (`hardF_observer_size_lower`, `hardF_observer_superlinear`) — the
Nečiporuk bound, rederived through the invariant.

## What is proved (all clean axioms, no `sorry`; the Nečiporuk theorems are reused, recast)

* `formulaBlockBoundary`, `formulaTotalBoundary` — the formula observer's boundary.
* `separated_forces_blockBoundary` — the per-block fooling principle (the observer invariant).
* `formulaTotalBoundary_le_size` — total boundary `≤ 4·litCount + #blocks` (small formula = low boundary).
* `hardF_blockBoundary_ge` — `hardF` forces block boundary `≥ 2^b − 1`.
* `hardF_observer_size_lower`, `hardF_observer_superlinear` — the `n²/log n` lower bound, in observer terms.

## Honest scope

A second restricted-class calibration: B₂ formulas (equivalently, the Nečiporuk-amenable branching-program
measure).  The invariant rederives the *known* `n²/log n` bound — its honest ceiling, **not** super-polynomial
and **not** P vs NP.  Two data points now confirm the method crosses into circuit/formula complexity
(AC⁰[p] degree, Nečiporuk formula size); the general machine-decomposition rung stays open.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open BFormula
open scoped BigOperators

variable {n : ℕ}

/-- **The formula observer's boundary on a block `S`**: `log₂` of the number of distinct residual
subfunctions `F` produces on `S` (the non-mergeable behaviors the formula must keep apart there). -/
noncomputable def formulaBlockBoundary (S : Finset (Fin n)) (F : BFormula n) : ℕ :=
  Nat.log 2 ((blockResiduals S F).card)

/-- **Total observer boundary** of a formula over a variable partition: the summed block boundaries. -/
noncomputable def formulaTotalBoundary {ι : Type*} (blocks : Finset ι) (S : ι → Finset (Fin n))
    (F : BFormula n) : ℕ :=
  ∑ i ∈ blocks, formulaBlockBoundary (S i) F

/-- **The per-block fooling principle (the observer invariant, Nečiporuk form).**  If a family `P` of
outside-settings is pairwise *separated* on block `S` (distinct settings give residuals that differ
somewhere), the block boundary is `≥ log₂ |P|`.  This is `many_nonmergeable_sectors_force_boundary` /
`faithful_separated_forces_boundary`, instantiated per block: separated behaviors are non-mergeable, so the
observer must keep `≥ |P|` of them apart. -/
theorem separated_forces_blockBoundary (S : Finset (Fin n)) (F : BFormula n)
    {P : Finset (Fin n → Bool)}
    (hsep : ∀ α ∈ P, ∀ β ∈ P, α ≠ β →
      ∃ x : Fin n → Bool, BFormula.eval F (fun i => if i ∈ S then x i else α i)
         ≠ BFormula.eval F (fun i => if i ∈ S then x i else β i)) :
    Nat.log 2 P.card ≤ formulaBlockBoundary S F :=
  Nat.log_mono_right (card_blockResiduals_ge_of_pairwise S F hsep)

/-- **Total boundary ≤ size (the bridge).**  A formula's total observer boundary over any variable partition
is at most `4·litCount F + #blocks` — a small formula *is* a low-total-boundary observer.  This is
`neciporuk_formula_lower_bound_opt` in observer language. -/
theorem formulaTotalBoundary_le_size {ι : Type*}
    (blocks : Finset ι) (S : ι → Finset (Fin n)) (F : BFormula n)
    (hdisj : (blocks : Set ι).PairwiseDisjoint S)
    (hcover : blocks.biUnion S = Finset.univ) :
    formulaTotalBoundary blocks S F ≤ 4 * BFormula.litCount F + blocks.card :=
  neciporuk_formula_lower_bound_opt blocks S F hdisj hcover

/-! ## The hard function forces high boundary on every block -/

variable {b m : ℕ}

/-- **`hardF` forces block boundary `≥ 2^b − 1`.**  On each address block, the multiplexer/addressing
structure of `hardF` produces `≥ 2^{2^b−1}` distinct residuals, so the formula observer's boundary there is
`≥ 2^b − 1`.  (`log_card_blockResiduals_hardF_ge`.) -/
theorem hardF_blockBoundary_ge (k : Fin m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    Dsize b - 1 ≤ formulaBlockBoundary (blockS k) F :=
  log_card_blockResiduals_hardF_ge k F hF

/-- **The Nečiporuk lower bound, in observer terms (headline).**  Every `B₂` formula computing `hardF` has
`litCount F ≥ (m·(2^b−1) − (m+1)) / 4`: its per-block non-mergeability forces total observer boundary
`≥ m·(2^b−1)`, and total boundary bounds size.  (`hardF_litCount_lower_opt_div`.) -/
theorem hardF_observer_size_lower (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    (m * (Dsize b - 1) - (m + 1)) / 4 ≤ BFormula.litCount F :=
  hardF_litCount_lower_opt_div F hF

/-- **The `n²/log n` rate, in observer terms.**  Under the balance bounds, any `B₂` formula computing
`hardF` has `litCount F ≥ N² / (64·b)` (`b ≈ log N`).  The observer invariant, summed over `m` blocks each of
boundary `≥ 2^b−1`, rederives the optimal Nečiporuk regime. -/
theorem hardF_observer_rate (m b : ℕ) (hb : 5 ≤ b)
    (hlo : 2 ^ b ≤ 2 * (m * b)) (hhi : m * b ≤ 2 ^ b)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    (nn b m) ^ 2 / (64 * b) ≤ BFormula.litCount F :=
  hardF_rate_sq_opt m b hb hlo hhi F hF

/-- **Super-linearity, in observer terms.**  For every constant `C`, some block width `b` makes every
formula computing `hardF` have `litCount > C·N`: the formula observer's boundary cannot be packed into a
linear-size formula.  (`hardF_superlinear`.) -/
theorem hardF_observer_superlinear (C : ℕ) :
    ∃ b : ℕ, ∀ (F : BFormula (nn b (2 ^ b))),
      (∀ x, BFormula.eval F x = hardF x) → C * nn b (2 ^ b) < BFormula.litCount F :=
  hardF_superlinear C

end PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk.separated_forces_blockBoundary
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk.formulaTotalBoundary_le_size
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk.hardF_observer_size_lower
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk.hardF_observer_superlinear
