import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverDimensionGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeBoundaryPrinciple

/-!
# The Dimension‑Gap Separation: the full proof plan as one conditional theorem, with Step 5 diagnosed

This assembles HAL's six‑step plan into a single checkable Lean object — and pins down, as a theorem, exactly
where it stops.

**The plan.**
* Step 1 (observer dimension `d_obs = B`) and Step 2 (residual dimension `d_res = r`): definitional; `…ObserverBoundary`, `…ExpanderNoHiding`.
* Step 3 (gap ⇒ debt) and Step 4 (debt ⇒ action): **proved** — `dimension_gap_forces_debt`
  (debt `≥ 2^{d_res} − 2^{d_obs}`) and `correct_needs_action` (action `≥` debt).  Together: a correct observer
  of a high‑`d_res` instance with low `d_obs` has action `≥ 2^{Ω(n)}`.
* Step 5 (poly‑time ⇒ low action): **the bridge** — and the wall.
* Step 6 (conclude): trivial given Steps 3–5.

**This file.**
* `dimension_gap_separation` — the assembly (Steps 3–6) as a *proved conditional*: `hgap` (Steps 3+4, an
  action lower bound for every correct SAT observer) `+` `hbridge` (Step 5) `+ poly < super‑poly` ⇒ no observer
  is both poly‑time and correct for SAT, i.e. the separation.  Only `hgap` and `hbridge` are non‑trivial.
* `step5_naive_bridge_false` — **Step 5's naive form is *false*, not merely open**: poly‑time does **not** imply
  low action, because a poly‑time observer may use high boundary (poly space), and action `= ∑ 2^{B_τ}` is then
  exponential.  Proved from `action_unbounded_by_time`.

## Honest diagnosis — where the plan stops, exactly

* **`hgap` for *all* observers of SAT** is the dimension‑gap target = `decision‑holonomy` = `P ≠ NP`.  We
  proved it for *low‑boundary* observers (the surjectivity/no‑hiding results), not all.
* **`hbridge` (Step 5) in its naive "poly‑time ⇒ low action" form is refuted** by `step5_naive_bridge_false`.
  A poly‑time decider can pay exponential action by using high boundary (the brute‑force / Gaussian‑elimination
  régime, `hard_instance_has_correct_high_boundary_decider`).  The only repair — "poly‑time cannot service
  *decision‑relevant* dimension‑gap debt" — re‑introduces the proof→decision distinction and **is**
  decision‑holonomy.

So the proof plan is valid as an *implication*, every step before 5 is real, and Step 5 is provably the wall:
its naive form is false and its repaired form equals the separation.  Constructing the plan does **not** prove
`P ≠ NP`; it makes the single open (and naively false) link unmistakable.
-/

namespace PallLean.Paper93.DeepMath.PathB.DimensionGapSeparation

open PallLean.Paper93.DeepMath.PathB.TimeBoundaryPrinciple

variable {Traj : Type*}

/-- **Dimension‑Gap Separation assembly (Steps 3–6, proved conditional).**  Given the dimension‑gap action
lower bound `hgap` (every correct SAT observer has action `≥ superThreshold` — Steps 3+4 lifted to all
observers) and the time→action bridge `hbridge` (every poly‑time observer has action `≤ polyBound` — Step 5),
with `polyBound < superThreshold`, **no observer is both poly‑time and correct for SAT** — the separation.
Both `hgap` (for *all* observers) and `hbridge` are the non‑trivial inputs. -/
theorem dimension_gap_separation (action : Traj → ℕ) (polyTime correctSAT : Traj → Prop)
    (polyBound superThreshold : ℕ)
    (hgap : ∀ t, correctSAT t → superThreshold ≤ action t)
    (hbridge : ∀ t, polyTime t → action t ≤ polyBound)
    (hsep : polyBound < superThreshold) :
    ∀ t, ¬ (polyTime t ∧ correctSAT t) := by
  rintro t ⟨hp, hc⟩
  have h1 := hgap t hc
  have h2 := hbridge t hp
  omega

/-- **Step 5's naive form is FALSE (proved).**  "poly‑time ⇒ low action" fails: for any time bound `T ≥ 1` and
any `A`, there is a `T`‑step (poly‑time) trajectory whose action exceeds `A`.  A poly‑time observer may use high
boundary (poly space), so its action `∑_{τ<T} 2^{B_τ}` is unbounded.  Hence `hbridge` cannot be discharged in
its naive form; the only repair is the decision‑relevant version, which is decision‑holonomy `= P ≠ NP`. -/
theorem step5_naive_bridge_false (T A : ℕ) (hT : 1 ≤ T) : ∃ B : ℕ → ℕ, A < action B T :=
  action_unbounded_by_time T A hT

end PallLean.Paper93.DeepMath.PathB.DimensionGapSeparation

#print axioms PallLean.Paper93.DeepMath.PathB.DimensionGapSeparation.dimension_gap_separation
#print axioms PallLean.Paper93.DeepMath.PathB.DimensionGapSeparation.step5_naive_bridge_false
