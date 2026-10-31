import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AndGateApprox

/-!
# Boosting — driving `k` clause indicators to error `2^{-k}` (the error-reduction core of Razborov–Smolensky)

The second rung inside `PolynomialMethodApproximation` (entry 266 was the first).  A single Fermat clause indicator
(entry 266, `clauseIndicator`) approximates OR with *one-sided* error: it is always correct on the all-zero input, and
on a nonzero input it fires correctly for *at least half* of the random subsets `S`.  **Boosting** combines `k`
independent such indicators into one polynomial whose error set is the *intersection* of the individual error sets — so
with the per-clause `≥ 1/2` agreement and independence, the error drops to `2^{-k}`.

**The boosted polynomial.**  `boostPoly e x := 1 − ∏ⱼ (1 − eⱼ x)`.  For Boolean-valued `eⱼ ∈ {0,1}` this is the **OR**
of the `eⱼ` (it is `1` iff some `eⱼ` fires, `0` iff all are `0`), of degree `∑ⱼ deg(eⱼ) = k·(p-1)` when each `eⱼ` is a
clause indicator.

**The error reduction (the genuinely-provable algebra).**  If each `eⱼ` is a one-sided approximator of a Boolean target
`tgt` with error set `bad j`, then `boostPoly e` agrees with `tgt` on *every* input outside the **intersection**
`⋂ⱼ bad j` (`boost_correct_off_iInter`).  So `bad(boost) ⊆ ⋂ⱼ bad j` — this is exactly the boosting step.  The
quantitative `|⋂ⱼ bad j| ≤ ∏ⱼ |bad j| / 2^{n(k-1)}` (independence) and the per-clause `|bad j| ≤ 2ⁿ/2` are the named
probabilistic sockets.

## What is proved (clean axioms, no `sorry`)

* **`boostPoly e x := 1 − ∏ⱼ (1 − eⱼ x)`** — the boosted (OR-of-approximators) polynomial.
* **`boostPoly_eq_one`** (PROVED) — if some `eⱼ x = 1` then `boostPoly e x = 1`.
* **`boostPoly_eq_zero`** (PROVED) — if all `eⱼ x = 0` then `boostPoly e x = 0`.
* **`boost_correct`** (PROVED) — `boostPoly e x = tgt x` whenever the good event holds (`tgt x = 0`, where one-sidedness
  forces all `eⱼ = 0`; or `tgt x = 1` with some `eⱼ` firing).
* **`boost_correct_off_iInter`** (PROVED) — `boostPoly e` agrees with `tgt` on every `x` outside the *intersection* of
  the error sets (`∃ j, x ∉ bad j`): **`bad(boost) ⊆ ⋂ⱼ bad j`**, the error-reduction core.

## The open probabilistic ingredients (named sockets)

* **`SingleSubsetAgreement`** — the per-clause primitive: at least half the subsets `S` make the clause indicator fire
  correctly on a nonzero input (`#{S : ∑_{i∈S} xᵢ ≠ 0} ≥ 2ⁿ/2`).  The probabilistic `≥ 1/2`.
* **`IndependentIntersectionBound`** — the independence product: `|⋂ⱼ bad j| ≤ ∏ⱼ |bad j| / 2^{n(k-1)}`.

Composed: `SingleSubsetAgreement` (`|bad j| ≤ 2ⁿ/2`) + `IndependentIntersectionBound` + the proved boosting
(`bad(boost) ⊆ ⋂`) give `|bad(boost)| ≤ 2ⁿ·2^{-k}` — a degree-`k(p-1)` approximation with error `2^{-k}`, the single-gate
target of `RandomizedLowDegreeApproximation` (entry 266).

## Honest scope

The boosting *algebra* — the OR-of-approximators polynomial and the error-set intersection `bad(boost) ⊆ ⋂ⱼ bad j` —
is fully proved.  The two probabilistic ingredients (per-clause `≥ 1/2` agreement and independence of the random
subsets) are the named sockets; together with the proved boosting they yield error `2^{-k}`.  This does **not** prove
those probabilistic bounds, and is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0Boosting

variable {F : Type} [Field F]

/-- **The boosted polynomial** `1 − ∏ⱼ (1 − eⱼ x)` — the OR of the approximators `eⱼ` (degree `∑ⱼ deg eⱼ`). -/
def boostPoly {X : Type} {k : ℕ} (e : Fin k → (X → F)) (x : X) : F :=
  1 - ∏ j, (1 - e j x)

/-- **Boost fires if any approximator fires (PROVED).**  If some `eⱼ x = 1`, the `j`-th factor is `1 − 1 = 0`, so the
product is `0` and `boostPoly e x = 1`. -/
theorem boostPoly_eq_one {X : Type} {k : ℕ} (e : Fin k → (X → F)) (x : X) (h : ∃ j, e j x = 1) :
    boostPoly e x = 1 := by
  obtain ⟨j, hj⟩ := h
  unfold boostPoly
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, sub_self]), sub_zero]

/-- **Boost is silent if all approximators are silent (PROVED).**  If every `eⱼ x = 0`, every factor is `1 − 0 = 1`, so
the product is `1` and `boostPoly e x = 0`. -/
theorem boostPoly_eq_zero {X : Type} {k : ℕ} (e : Fin k → (X → F)) (x : X) (h : ∀ j, e j x = 0) :
    boostPoly e x = 0 := by
  unfold boostPoly
  rw [Finset.prod_eq_one (fun j _ => by rw [h j, sub_zero]), sub_self]

/-- **Boost agrees with the target under the good event (PROVED).**  For a Boolean target `tgt x ∈ {0,1}`: if `tgt x = 0`
then one-sidedness (`hone`) forces all `eⱼ x = 0`, so `boost = 0 = tgt`; if `tgt x = 1` then some `eⱼ` fires (`hsome`),
so `boost = 1 = tgt`. -/
theorem boost_correct {X : Type} {k : ℕ} (e : Fin k → (X → F)) (tgt : X → F) (x : X)
    (htgt : tgt x = 0 ∨ tgt x = 1)
    (hone : ∀ j, tgt x = 0 → e j x = 0)
    (hsome : tgt x = 1 → ∃ j, e j x = 1) :
    boostPoly e x = tgt x := by
  rcases htgt with h0 | h1
  · rw [h0]; exact boostPoly_eq_zero e x (fun j => hone j h0)
  · rw [h1]; exact boostPoly_eq_one e x (hsome h1)

/-- **Error reduction: `bad(boost) ⊆ ⋂ⱼ bad j` (PROVED).**  If each `eⱼ` is a one-sided approximator of the Boolean
target `tgt` with error set `bad j` (correct off `bad j`, silent when `tgt = 0`), then `boostPoly e` agrees with `tgt`
on every input `x` outside the *intersection* of the error sets (i.e. `x ∉ bad j` for some `j`).  This is the boosting
step: the combined error set is the intersection of the individual ones. -/
theorem boost_correct_off_iInter {X : Type} {k : ℕ} (e : Fin k → (X → F)) (tgt : X → F)
    (bad : Fin k → Finset X)
    (htgt : ∀ x, tgt x = 0 ∨ tgt x = 1)
    (hone : ∀ x j, tgt x = 0 → e j x = 0)
    (hcorrect : ∀ j, ∀ x ∉ bad j, e j x = tgt x)
    (x : X) (hx : ∃ j, x ∉ bad j) :
    boostPoly e x = tgt x := by
  apply boost_correct e tgt x (htgt x) (fun j => hone x j)
  intro h1
  obtain ⟨j, hj⟩ := hx
  refine ⟨j, ?_⟩
  rw [hcorrect j x hj]; exact h1

/-! ## The probabilistic ingredients (named sockets) -/

/-- **The per-clause agreement primitive (the probabilistic `≥ 1/2`, NOT proved here).**  On a nonzero input `x`, at
least half of the subsets `S ⊆ [n]` make the Fermat clause sum `∑_{i∈S} xᵢ` nonzero (so the clause indicator fires
correctly).  Over `F_2` this is *exactly* `1/2` by the parity-toggle involution; over `F_p` it is `≥ 1/2`.  The base
probabilistic primitive feeding the boosting. -/
def SingleSubsetAgreement (p n : ℕ) [Fact p.Prime] (x : Fin n → Bool) : Prop :=
  2 ^ n ≤ 2 * (Finset.univ.filter
    (fun S : Finset (Fin n) => (∑ i ∈ S, (if x i then (1 : ZMod p) else 0)) ≠ 0)).card

/-- **The independence product bound (NOT proved here).**  When the `k` error sets come from *independent* random
subsets, the intersection is small: `|⋂ⱼ bad j| ≤ (∏ⱼ |bad j|) / 2^{n(k-1)}`.  Combined with `|bad j| ≤ 2ⁿ/2`
(`SingleSubsetAgreement`) this gives `|⋂ⱼ bad j| ≤ 2ⁿ·2^{-k}`. -/
def IndependentIntersectionBound {X : Type} [Fintype X] {k : ℕ}
    (bad : Fin k → Finset X) (interCard : ℕ) : Prop :=
  2 ^ ((Fintype.card X) * (k - 1)) * interCard ≤ ∏ j, (bad j).card

/-!
**The rung.**  The boosting *algebra* is proved: `boostPoly` is the OR of the `k` approximators (`boostPoly_eq_one`,
`boostPoly_eq_zero`), it agrees with the target under the good event (`boost_correct`), and — the error-reduction core —
its error set is contained in the *intersection* of the individual error sets (`boost_correct_off_iInter`,
`bad(boost) ⊆ ⋂ⱼ bad j`).  The two probabilistic ingredients remain as named sockets: `SingleSubsetAgreement` (per-clause
`≥ 1/2`, provable over `F_2` by the parity-toggle involution) and `IndependentIntersectionBound` (independence of the
random subsets).  Composed, they drive the error to `2^{-k}` at degree `k·(p-1)` — the single-gate target of
`RandomizedLowDegreeApproximation` (entry 266).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Boosting

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Boosting.boostPoly_eq_one
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Boosting.boostPoly_eq_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Boosting.boost_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Boosting.boost_correct_off_iInter
