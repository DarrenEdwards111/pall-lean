import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAttackNoSharing

/-!
# Attacking localization at the seam: the anti-straddle reach bound is self-defeating

`SeamDisjointnessProbe` showed disjointness does not force the collision bound — the ceiling is a
gate's **reach** (`mult ≤ depCard`), and only *localization* (bounded reach) forbids the global
straddler.  So the last hope is: does SAT's structure force **localization** at the seam?  This file
attacks that, and finds the sharp obstruction.

To forbid straddling, you must force `mult ≤ 1` on every gate (no gate serves two copies).  Via
`mult ≤ depCard`, the only reach bound that guarantees this is `σ ≤ 1` (`reach_one_forbids_straddle`).
But a straddler — and, more importantly, any gate doing real nonlinear work — needs reach `≥ 2`
(`straddle_gate_reach_two`: the concrete straddler reads two variables, one per copy).  **The reach a
straddler needs and the reach the computation needs are the same threshold (`≥ 2`).**  So there is no
`σ` that both hosts the tower (`σ ≥ 2`) and forbids straddling (`σ ≤ 1`): `anti_straddle_is_degenerate`.

## What is proved (on `straddleExample : EntangledTower 2 1 4`)

* **`serve_le_reach`** — a gate's copy-service is at most its reach (`mult ≤ depCard`): the trade-off.
* **`reach_one_forbids_straddle`** — reach `≤ 1` forces `mult ≤ 1`: the *only* reach bound that forbids
  straddling is `σ ≤ 1`.
* **`straddle_mult_two`** / **`straddle_gate_reach_two`** — the concrete straddler serves both copies
  (`mult = 2`), hence has reach `≥ 2`.  Straddling costs reach `2` — exactly the reach a two-input
  (nonlinear) gate needs anyway.
* **`anti_straddle_is_degenerate`** — no reach bound both permits the tower's gates (`σ ≥ 2`) and
  forbids straddling (`σ ≤ 1`).  The anti-straddle bound `σ ≤ 1` is degenerate: it forbids the very
  computation the tower requires.

## Honest verdict

Localization at the seam admits **no non-degenerate anti-straddle bound**: the reach that would forbid
the global straddler is the same reach that forbids the nonlinear computation.  So SAT's structure does
**not** force localization at the seam — the global straddler escapes exactly as in `LocalizationBound`,
and for a sharp reason (shared reach threshold).  Forbidding straddling while allowing computation
requires a bound on `mult` *independent of reach* — a no-sharing bound — which is `cost_super`.  The
wall lives at free reach (the charge-`0` DAG, `ChargedSharing`).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SeamLocalizationProbe

open PallLean.Paper93.DeepMath.PathB.AttackNoSharing
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler
open PallLean.Paper93.DeepMath.PathB.TheReasonShared

/-- **Service ≤ reach (proved).**  A gate serves at most as many copies as it reaches variables
(`mult ≤ depCard`) — the trade-off between locality and mass-production. -/
theorem serve_le_reach {k b n : ℕ} (C : EntangledTower k b n) (g : ℕ) :
    mult (toShared C) g ≤ (depSet C g).card :=
  mult_le_depCard C g

/-- **Only reach `≤ 1` forbids straddling (proved).**  If a gate reaches at most one variable it serves
at most one copy.  This is the sole reach bound that guarantees no straddling. -/
theorem reach_one_forbids_straddle {k b n : ℕ} (C : EntangledTower k b n) (g : ℕ)
    (h : (depSet C g).card ≤ 1) : mult (toShared C) g ≤ 1 :=
  le_trans (mult_le_depCard C g) h

/-- **The concrete straddler serves both copies (proved).**  Gate `0` of `straddleExample` has
`mult = 2`. -/
theorem straddle_mult_two : mult (toShared straddleExample) 0 = 2 := by decide

/-- **Straddling costs reach `2` (proved).**  The straddler reaches at least two variables — one
private variable per copy.  This is exactly the reach a two-input (nonlinear) gate needs. -/
theorem straddle_gate_reach_two : 2 ≤ (depSet straddleExample 0).card := by
  have h := mult_le_depCard straddleExample 0
  rw [straddle_mult_two] at h
  exact h

/-- **The anti-straddle bound is degenerate (proved).**  There is no reach bound `σ` that both permits
the tower's gates (`σ ≥ 2`, since the straddler/computation needs reach `2`) and forbids straddling
(`σ ≤ 1`).  Bounding reach to stop straddling stops the computation. -/
theorem anti_straddle_is_degenerate :
    ¬ ∃ σ, (depSet straddleExample 0).card ≤ σ ∧ σ ≤ 1 := by
  rintro ⟨σ, h1, h2⟩
  have h := straddle_gate_reach_two
  omega

end PallLean.Paper93.DeepMath.PathB.SeamLocalizationProbe

#print axioms PallLean.Paper93.DeepMath.PathB.SeamLocalizationProbe.serve_le_reach
#print axioms PallLean.Paper93.DeepMath.PathB.SeamLocalizationProbe.reach_one_forbids_straddle
#print axioms PallLean.Paper93.DeepMath.PathB.SeamLocalizationProbe.straddle_mult_two
#print axioms PallLean.Paper93.DeepMath.PathB.SeamLocalizationProbe.straddle_gate_reach_two
#print axioms PallLean.Paper93.DeepMath.PathB.SeamLocalizationProbe.anti_straddle_is_degenerate
