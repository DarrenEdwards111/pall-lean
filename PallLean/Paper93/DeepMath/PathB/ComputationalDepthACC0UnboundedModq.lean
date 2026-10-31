import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone

/-!
# Bridge (MOD_q ∉ AC⁰, real model) — the residue-family no-go in unbounded fan-in (proved)

The `q`-counting companion to `parity_superpoly_ac0`, in the genuine model.  `Layer4.mod_q_indicators_false` already shows
(in the unbounded-fan-in `BoolCircuitSyntax` model) that no `AC⁰[p]` family computes all `q` residue indicators
`[weight ≡ j mod q]` within the RS resource window.  Since `AC⁰ ⊆ AC⁰[p]` (`isAC0_isAC0p`: a `MOD`-free circuit is `AC⁰[p]`
for every `p`), the same no-go holds for plain unbounded-fan-in `AC⁰`: **no `AC⁰` family computes the `MOD_q` residue
indicators** (for `q ∤ p`, `p,q` prime, in the window).

## What is proved (clean axioms, no `sorry`)

* **`isAC0_isAC0p`** (PROVED) — `IsAC0Syntax C → IsAC0pSyntax p C` (a `MOD`-free circuit is `AC⁰[p]` for every `p`).
* **`modq_indicators_false_ac0`** (PROVED) — no unbounded-fan-in `AC⁰` family computes the `q` residue indicators in the RS
  window — i.e. `False`.

## Honest scope

This is the real (unbounded-fan-in) `MOD_q` residue-family no-go for `AC⁰`.  As in `Layer4`, it is the *family* statement; a
*single* `MOD_q ∉ AC⁰` for all `n` needs the residue-family construction (built for `ACC0Circuit` via `pinTrue`).  The
**Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains **open** / not faked.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModq

open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)

/-- **A `MOD`-free circuit is `AC⁰[p]` for every `p` (PROVED).**  `AC⁰ ⊆ AC⁰[p]` at the syntactic level. -/
theorem isAC0_isAC0p {n p : ℕ} :
    ∀ (C : BoolCircuitSyntax n), C.IsAC0Syntax → C.IsAC0pSyntax p
  | .const b, _ => by simp only [BoolCircuitSyntax.IsAC0pSyntax]
  | .input i, _ => by simp only [BoolCircuitSyntax.IsAC0pSyntax]
  | .not c, h => by
      simp only [BoolCircuitSyntax.IsAC0Syntax] at h
      simp only [BoolCircuitSyntax.IsAC0pSyntax]
      exact isAC0_isAC0p c h
  | .orGate cs, h => by
      simp only [BoolCircuitSyntax.IsAC0Syntax] at h
      simp only [BoolCircuitSyntax.IsAC0pSyntax]
      intro C hC; exact isAC0_isAC0p C (h C hC)
  | .andGate cs, h => by
      simp only [BoolCircuitSyntax.IsAC0Syntax] at h
      simp only [BoolCircuitSyntax.IsAC0pSyntax]
      intro C hC; exact isAC0_isAC0p C (h C hC)
  | .modGate q r cs, h => by simp only [BoolCircuitSyntax.IsAC0Syntax] at h

open Classical in
/-- **No unbounded-fan-in `AC⁰` family computes the `MOD_q` residue indicators (PROVED).**  For `p,q` prime, `q ∤ p`, no
`MOD`-free (`IsAC0Syntax`) family `C : ℕ → BoolCircuitSyntax (2m+1)` computes all `q` residue indicators `[weight ≡ j mod q]`
within the RS depth/size window — the real `MOD_q` residue-family no-go for `AC⁰`. -/
theorem modq_indicators_false_ac0 (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m t d : ℕ} (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t)
    (C : ℕ → BoolCircuitSyntax (2 * m + 1))
    (hCind : ∀ j ∈ Finset.range q, ∀ x : Fin (2 * m + 1) → Bool,
      (C j).eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = j))
    (hac : ∀ j ∈ Finset.range q, (C j).IsAC0Syntax)
    (ht : ∀ j ∈ Finset.range q, 4 * q * (subcircuits (C j)).toFinset.card ≤ p ^ t)
    (hdepth : ∀ j ∈ Finset.range q, (C j).depth ≤ d)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3) : False :=
  PallLean.Paper93.DeepMath.PathB.Layer4.mod_q_indicators_false p q hpq ht1 hpt1 C hCind
    (fun j hj => isAC0_isAC0p (C j) (hac j hj)) ht hdepth hwindow

/-!
**MOD_q residue-family no-go for unbounded-fan-in `AC⁰`, proved.**  Via `AC⁰ ⊆ AC⁰[p]` (`isAC0_isAC0p`) and
`Layer4.mod_q_indicators_false`.  Remaining (open, not faked): the single-`MOD_q` construction and the Williams cash-out to
`NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModq

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedModq.modq_indicators_false_ac0
