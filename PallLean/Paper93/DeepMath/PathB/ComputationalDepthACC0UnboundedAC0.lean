import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UnboundedParity

/-!
# Bridge (PARITY ∉ poly-size AC⁰, real model) — Håstad's theorem, unbounded fan-in (proved)

The canonical constant-depth lower bound in the genuine model: `PARITY` requires super-polynomial size in **unbounded-fan-in**
`AC⁰` (no `MOD` gates).  An `AC⁰` circuit is `MOD`-free (`IsAC0Syntax`), so the `hmod` side condition of
`Layer3.parity_function_lower_bound` ("all `MOD` gates have modulus `p`") holds vacuously — and the RS bound applies for any
odd prime `p`, giving `p^t < 4·#{distinct subcircuits}`.

This is the Furst–Saxe–Sipser / Håstad theorem (via Razborov–Smolensky), now in the real `BoolCircuitSyntax` model with
`List`-based unbounded-fan-in gates — the genuine upgrade of the binary-fan-in `parity_not_ac0`.

## What is proved (clean axioms, no `sorry`)

* **`isAC0_of_mem_subcircuits`** (PROVED) — `AC⁰` (no-`MOD`) is inherited by subcircuits.
* **`hmod_of_isAC0`** (PROVED) — an `AC⁰` circuit has no `MOD` gates, so the `hmod` condition is vacuous.
* **`parity_superpoly_ac0`** (PROVED) — `PARITY` requires `p^t < 4·#{subcircuits}` in unbounded-fan-in `AC⁰` (for any odd
  prime `p`, in the RS window) — super-polynomial size.

## Honest scope

This is the real (unbounded-fan-in) `PARITY ∉ poly-size AC⁰`.  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different,
P≠NP-strength theorem and remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedAC0

open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits parity_function_lower_bound)
open PallLean.Paper93.DeepMath.PathB.Layer4 (exists_of_mem_subcircuitsList)

/-- **`AC⁰` (no-`MOD`) is inherited by subcircuits (PROVED).** -/
theorem isAC0_of_mem_subcircuits {n : ℕ} :
    ∀ (C : BoolCircuitSyntax n), BoolCircuitSyntax.IsAC0Syntax C →
      ∀ G ∈ subcircuits C, BoolCircuitSyntax.IsAC0Syntax G
  | .const b, h, G, hG => by simp only [subcircuits, List.mem_singleton] at hG; subst hG; exact h
  | .input i, h, G, hG => by simp only [subcircuits, List.mem_singleton] at hG; subst hG; exact h
  | .not c, h, G, hG => by
      simp only [subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact h
      · simp only [BoolCircuitSyntax.IsAC0Syntax] at h
        exact isAC0_of_mem_subcircuits c h G hG
  | .orGate cs, h, G, hG => by
      simp only [subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact h
      · simp only [BoolCircuitSyntax.IsAC0Syntax] at h
        obtain ⟨c, hc, hGc⟩ := exists_of_mem_subcircuitsList G cs hG
        exact isAC0_of_mem_subcircuits c (h c hc) G hGc
  | .andGate cs, h, G, hG => by
      simp only [subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact h
      · simp only [BoolCircuitSyntax.IsAC0Syntax] at h
        obtain ⟨c, hc, hGc⟩ := exists_of_mem_subcircuitsList G cs hG
        exact isAC0_of_mem_subcircuits c (h c hc) G hGc
  | .modGate q r cs, h, G, hG => by simp only [BoolCircuitSyntax.IsAC0Syntax] at h

/-- **`AC⁰ ⇒ hmod` (PROVED).**  An `AC⁰` circuit has no `MOD` gates among its subcircuits, so the modulus condition is
vacuous (any `p` works). -/
theorem hmod_of_isAC0 {n p : ℕ} (C : BoolCircuitSyntax n) (h : BoolCircuitSyntax.IsAC0Syntax C)
    (a r cs) (hG : (BoolCircuitSyntax.modGate a r cs : BoolCircuitSyntax n) ∈ subcircuits C) :
    a = p := by
  have h2 := isAC0_of_mem_subcircuits C h _ hG
  simp only [BoolCircuitSyntax.IsAC0Syntax] at h2

open Classical in
/-- **PARITY requires super-polynomial size in unbounded-fan-in `AC⁰` (PROVED).**  For any odd prime `p`, a `MOD`-free
(`IsAC0Syntax`) circuit of depth `≤ d` computing `PARITY` has `p^t < 4·(subcircuits).toFinset.card` in the RS window — the
real Furst–Saxe–Sipser / Håstad lower bound. -/
theorem parity_superpoly_ac0 (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {m d : ℕ}
    (Cir : BoolCircuitSyntax (2 * m + 1)) (hac : BoolCircuitSyntax.IsAC0Syntax Cir)
    (hd : Cir.depth ≤ d) (t : ℕ) (ht1 : 1 ≤ t)
    (hparity : ∀ x : Fin (2 * m + 1) → Bool,
      Cir.eval x = decide (Odd (Finset.univ.filter (fun i => x i = true)).card))
    (hm : 8 * (((p - 1) * t) ^ d) ^ 2 ≤ m) :
    p ^ t < 4 * (subcircuits Cir).toFinset.card :=
  parity_function_lower_bound p hp2 Cir hd t ht1 hparity (hmod_of_isAC0 Cir hac) hm

/-!
**PARITY ∉ poly-size unbounded-fan-in `AC⁰`, proved.**  The real Furst–Saxe–Sipser / Håstad theorem via Razborov–Smolensky,
in the genuine constant-depth model.  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not
`NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedAC0

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedAC0.parity_superpoly_ac0
