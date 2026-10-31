import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4PadSubcircuits

/-!
# Bridge (MOD_q ∉ AC⁰[p], real model, single function) — uniform residue-0 family no-go (proved)

The single-`MOD_q` (residue-`0`) lower bound in the genuine (unbounded-fan-in) `BoolCircuitSyntax` model, assembled from a
*uniform* `AC⁰[p]` family.  The repo's `Layer4.mod_q_family_false` already discharges the residue construction (it consumes
one residue-`0` circuit per shifted arity `(2m+1)+(q−j)` and derives `False`).  Here we present it in the natural form: if
`MOD_q` (the residue-`0` indicator `[weight ≡ 0 mod q]`) is computed by a *uniform* `AC⁰[p]` family — one circuit at every
arity, bounded depth and (padding-adjusted) size — then `False` (for `q ∤ p`, `p,q` prime, in the RS window).

This is the real-model analogue of the binary-model `modq_not_acc0p_uniform`, using the repo's clean `Layer4` padding +
agreement machinery rather than the `ACC0Circuit` `pinTrue` construction.

## What is proved (clean axioms, no `sorry`)

* **`modq_uniform_false_real`** (PROVED) — no uniform `AC⁰[p]` family computes `MOD_q` (residue-`0`) within the RS window.

## Honest scope

The single-`MOD_q` residue-`0` no-go for unbounded-fan-in `AC⁰[p]`, from a uniform family.  The **Williams cash-out**
(`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModqUniform

open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)
open PallLean.Paper93.DeepMath.PathB.Layer4 (mod_q_family_false)

open Classical in
/-- **No uniform `AC⁰[p]` family computes `MOD_q` (residue-`0`) in the real model (PROVED).**  Given a uniform family
`D : (N) → BoolCircuitSyntax N` computing `[weight ≡ 0 mod q]` at every arity, all `AC⁰[p]`, bounded depth `d` and
padding-adjusted size `≤ p^t/(4q)`, in the RS window `16((p−1)t)^d)² < 2m+3`, we get `False`.  The single-`MOD_q` lower bound
in unbounded fan-in, assembled via `Layer4.mod_q_family_false`. -/
theorem modq_uniform_false_real (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m t d : ℕ} (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t)
    (D : (N : ℕ) → BoolCircuitSyntax N)
    (hD : ∀ N, ∀ x : Fin N → Bool,
      (D N).eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = 0))
    (hDAC : ∀ N, BoolCircuitSyntax.IsAC0pSyntax p (D N))
    (hDsize : ∀ N, 4 * q * ((subcircuits (D N)).toFinset.card + ((2 * m + 1) + q)) ≤ p ^ t)
    (hDdepth : ∀ N, (D N).depth ≤ d)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3) : False :=
  mod_q_family_false p q hpq ht1 hpt1 (fun j => D ((2 * m + 1) + (q - j)))
    (fun _ _ => hD _) (fun _ _ => hDAC _) (fun _ _ => hDsize _) (fun _ _ => hDdepth _) hwindow

/-!
**Single-`MOD_q` no-go for unbounded-fan-in `AC⁰[p]`, proved.**  No uniform `AC⁰[p]` family computes `MOD_q` (residue-`0`)
within the RS window — the real-model analogue of `modq_not_acc0p_uniform`, via `Layer4.mod_q_family_false`.  Remaining (open,
not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModqUniform

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModqUniform.modq_uniform_false_real
