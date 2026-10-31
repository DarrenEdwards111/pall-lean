import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderNoHiding

/-!
# The Observer Residual Dimension Gap (Epistemic Holonomy Dimension) — invariant defined, gap⇒debt proved

This formalizes the dimension‑gap invariant: the rigorous form of "P observer in low‑dimensional space, NP
witness in high‑dimensional hypercube".  *Not physical dimension* — **effective boundary dimension** vs
**residual dimension**:

* **Observer dimension** `d_obs = B`: bits of boundary distinction a view holds (a view into `Fin (2^B)`).
* **Residual dimension** `d_res = r`: `log₂` of the number of distinct residual outcomes (a residual map
  surjecting onto `Fin (2^r)`).
* **Gap** `δ = d_res − d_obs = r − B`.

The provable content — exactly what the whole programme established, now in one geometric statement: **the
dimensional mismatch *is* the debt.**

## Proved (clean axioms, no `sorry`)

* `dimension_gap_forces_debt` — an observer of dimension `B` facing a residual of dimension `r` carries debt
  `≥ 2^r − 2^B`.  (= `surjective_residual_forces_debt`, re‑read as a dimension gap.)
* `positive_gap_forces_debt` — if `d_res > d_obs` (`r > B`) the observer carries **strictly positive** debt:
  it cannot faithfully hold a residual geometry of higher dimension than its boundary.

## The invariant and the P‑vs‑NP target (NAMED, open)

`DimensionGapHard d_res d_obs threshold`: at every `n`, the residual dimension exceeds the observer dimension
by at least `threshold n`.  The separation target is

```
DimensionGapHard  d_res_SAT  d_obs(any poly‑time observer)  (Ω(n))
```

— every polynomial‑time observer of SAT is lower‑dimensional than SAT's residual witness geometry by `Ω(n)`,
and the mismatch costs super‑polynomial action.

**Honest status.**  `dimension_gap_forces_debt` is proved and is the geometric core of everything: a low‑dim
observer of a high‑dim residual pays debt.  For the expander instances we *proved* `d_res = Ω(n)` (the
surjectivity results) and bounded‑boundary observers have `d_obs = B`, so the gap is real **there**.  But the
target — that the gap is `Ω(n)` for **every** polynomial‑time observer of SAT (the `min` over all observer
trajectories) — is **exactly `decision‑holonomy` / `AdaptiveResidualNonCollapse`**, re‑expressed in dimension
language.  It `= P ≠ NP`.  Defining the invariant does **not** prove it: it is the same open `min`‑over‑
trajectories quantifier, and the barriers (`hard_instance_has_correct_high_boundary_decider`: a full‑dimension
observer pays zero debt; `tseitin_unsat_of_odd_charge`: high `d_res` coexists with decision‑easiness) show why.
This file gives the invariant its rigorous definition and proves the half that is true; the separation remains
open.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverDimensionGap

open PallLean.Paper93.DeepMath.PathB.BoundaryDebt

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- **Dimension‑gap forces debt (proved).**  An observer of effective boundary dimension `B` (a view into
`Fin (2^B)`) facing a residual of dimension `r` (a residual map surjecting onto `Fin (2^r)`) carries
distinguishability debt `≥ 2^r − 2^B`.  The dimensional mismatch *is* the debt. -/
theorem dimension_gap_forces_debt {r B : ℕ} (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual) (view : C → Fin (2 ^ B)) :
    2 ^ r - 2 ^ B ≤ debtCount (residualFooling residual) view :=
  surjective_residual_forces_debt residual hsurj view

/-- **Positive gap ⇒ positive debt (proved).**  If the residual dimension strictly exceeds the observer
dimension (`d_res > d_obs`, i.e. `r > B`), the observer must carry strictly positive debt: it cannot faithfully
hold a residual geometry of higher dimension than its boundary. -/
theorem positive_gap_forces_debt {r B : ℕ} (hgap : B < r) (residual : C → Fin (2 ^ r))
    (hsurj : Function.Surjective residual) (view : C → Fin (2 ^ B)) :
    0 < debtCount (residualFooling residual) view := by
  have h := dimension_gap_forces_debt residual hsurj view
  have hlt : 2 ^ B < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) hgap
  omega

/-- **The dimension‑gap hardness target (NAMED, open).**  `DimensionGapHard d_res d_obs threshold` holds when,
at every size `n`, the residual dimension exceeds the observer dimension by at least `threshold n`.  The
P‑vs‑NP target is this with `d_res = d_res(SAT)`, `d_obs` the dimension of an arbitrary polynomial‑time
observer, and `threshold = Ω(n)`.  This *is* `decision‑holonomy` in dimension language: `= P ≠ NP`, **not
proved** — the `min` over all observer trajectories is the open quantifier. -/
def DimensionGapHard (dRes dObs threshold : ℕ → ℕ) : Prop :=
  ∀ n, threshold n ≤ dRes n - dObs n

end PallLean.Paper93.DeepMath.PathB.ObserverDimensionGap

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverDimensionGap.dimension_gap_forces_debt
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverDimensionGap.positive_gap_forces_debt
