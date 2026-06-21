import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitReprP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearize

/-!
# Brick (AC⁰[p] cash-out) — AC⁰[p] circuits use few `AND`-terms (proved)

The genuine cash-out of the proven bricks: combining the exact `AC⁰[p]` representation (`reprP`, Brick AC⁰[p] repr) with the
degree → `AND`-term bridge (`andTerms_card_le`, Brick multilinearize), every `AC⁰[p]` circuit's representing polynomial uses
at most `(n+1)^{reprDegP C}` distinct `AND`-terms.  For constant depth the degree `reprDegP C` is constant, so the count is
*polynomial* in `n` — and in particular `< 2^n` once `(n+1)^{reprDegP C} < 2^n`.

This is the size half of the Beigel–Tarui / Williams cash-out, *discharged with real math* for the `AC⁰[p]` class: the
circuit is computed by a polynomial whose `AND`-term count is the quantity the Route-B counting socket consumes.

## What is proved (clean axioms, no `sorry`)

* **`reprP_andTerms_card_le`** (PROVED) — `((reprP p C).support.image (·.support)).card ≤ (n+1)^{reprDegP p C}`.
* **`reprP_andTerms_lt`** (PROVED) — `(n+1)^{reprDegP p C} < 2^n → … card < 2^n` (the `< 2^n` cell bound).

## Honest scope

This is the `AC⁰[p]` **size** cash-out (`AND`-term count), combining two proved bricks.  It does **not** convert the
polynomial into the exact `SYM∘AND` form object, handle `MOD_q` (`q ≠ p`) / prime-power gates (the RS/A.3 obstruction), nor
supply the general `RSRep` / `counting` / `williams` / `hierarchy` of `mod6_composite_route_to_NEXP_not_ACC0` (those remain the
abstract conditional anatomy — `RSRep` is the open `composite_BT_degree`, P≠NP-strength).  General YBT and the full Williams
cash-out remain open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ReprPAndTerms

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (reprP reprDegP reprP_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearize (andTerms_card_le)

variable {n p : ℕ} [Fact p.Prime]

/-- **AC⁰[p] cash-out (PROVED): the representing polynomial uses `≤ (n+1)^{reprDegP C}` `AND`-terms.** -/
theorem reprP_andTerms_card_le (C : ACC0Circuit n) :
    ((reprP p C).support.image (fun e => e.support)).card ≤ (n + 1) ^ (reprDegP p C) :=
  andTerms_card_le (reprP p C) (reprDegP p C) (reprP_totalDegree_le C)

/-- **AC⁰[p] cash-out (PROVED): under the degree budget the `AND`-term count is `< 2^n` (the searchable cell bound).** -/
theorem reprP_andTerms_lt (C : ACC0Circuit n) (hbudget : (n + 1) ^ (reprDegP p C) < 2 ^ n) :
    ((reprP p C).support.image (fun e => e.support)).card < 2 ^ n :=
  lt_of_le_of_lt (reprP_andTerms_card_le C) hbudget

/-!
**The AC⁰[p] size cash-out, proved.**  Every `AC⁰[p]` circuit is a polynomial with `≤ (n+1)^{reprDegP C}` `AND`-terms —
polynomial for constant depth, `< 2^n` under the degree budget — exactly the size quantity the Williams/Route-B counting step
consumes, discharged with real math for `AC⁰[p]`.  Remaining (open, not faked): the `SYM∘AND` form object, `MOD_q`/prime-power
gates, and the general `RSRep`/`counting`/`williams`/`hierarchy` conditional.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ReprPAndTerms

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ReprPAndTerms.reprP_andTerms_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ReprPAndTerms.reprP_andTerms_lt
