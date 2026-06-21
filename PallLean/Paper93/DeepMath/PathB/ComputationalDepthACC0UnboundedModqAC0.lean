import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UnboundedModqUniform
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UnboundedModq

/-!
# Bridge (MOD_q ∉ AC⁰, real model, single function) — uniform no-go in unbounded fan-in (proved)

The single-`MOD_q` (residue-`0`) lower bound for plain unbounded-fan-in `AC⁰` (no `MOD` gates), in the genuine
`BoolCircuitSyntax` model.  Combining the `AC⁰[p]` single-`MOD_q` no-go (`modq_uniform_false_real`) with `AC⁰ ⊆ AC⁰[p]`
(`isAC0_isAC0p`): no uniform `AC⁰` family computes `MOD_q` (the residue-`0` indicator `[weight ≡ 0 mod q]`) within the RS
window (for `q ∤ p`, `p,q` prime).

This completes the single-function `MOD_q` picture in the real model — the no-MOD companion to `modq_uniform_false_real`,
and the single-residue companion to the family bound `modq_indicators_false_ac0`.

## What is proved (clean axioms, no `sorry`)

* **`modq_uniform_false_ac0_real`** (PROVED) — no uniform `AC⁰` family computes `MOD_q` (residue-`0`) in the RS window.

## Honest scope

The single-`MOD_q` residue-`0` no-go for unbounded-fan-in `AC⁰`.  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different,
P≠NP-strength theorem and remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModqAC0

open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)
open PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModqUniform (modq_uniform_false_real)
open PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModq (isAC0_isAC0p)

open Classical in
/-- **No uniform `AC⁰` family computes `MOD_q` (residue-`0`) in the real model (PROVED).**  A uniform `MOD`-free
(`IsAC0Syntax`) family computing `[weight ≡ 0 mod q]` at every arity, bounded depth/size, in the RS window, gives `False` —
via `AC⁰ ⊆ AC⁰[p]` and the `AC⁰[p]` single-`MOD_q` no-go. -/
theorem modq_uniform_false_ac0_real (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m t d : ℕ} (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t)
    (D : (N : ℕ) → BoolCircuitSyntax N)
    (hD : ∀ N, ∀ x : Fin N → Bool,
      (D N).eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = 0))
    (hDAC : ∀ N, (D N).IsAC0Syntax)
    (hDsize : ∀ N, 4 * q * ((subcircuits (D N)).toFinset.card + ((2 * m + 1) + q)) ≤ p ^ t)
    (hDdepth : ∀ N, (D N).depth ≤ d)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3) : False :=
  modq_uniform_false_real p q hpq ht1 hpt1 D hD (fun N => isAC0_isAC0p (D N) (hDAC N))
    hDsize hDdepth hwindow

/-!
**Single-`MOD_q` no-go for unbounded-fan-in `AC⁰`, proved.**  Via `AC⁰ ⊆ AC⁰[p]` (`isAC0_isAC0p`) + the `AC⁰[p]` single-`MOD_q`
no-go (`modq_uniform_false_real`).  Completes the real-model single-function `MOD_q` picture.  Remaining (open, not faked): the
Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModqAC0

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModqAC0.modq_uniform_false_ac0_real
