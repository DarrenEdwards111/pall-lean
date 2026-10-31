import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UnboundedSep

/-!
# Bridge (AC⁰[2] ⊄ AC⁰[3], real model) — the prime modulus matters, unbounded fan-in (proved)

The prime-modulus separation in the genuine (unbounded-fan-in) `BoolCircuitSyntax` model: `AC⁰[2]` and `AC⁰[3]` are different.
`PARITY` is computed by a single unbounded-fan-in `MOD_2` gate — a depth-`1` `AC⁰[2]` circuit
(`parity_mem_acc02_unbounded`) — yet every `AC⁰[3]` circuit computing `PARITY` needs super-polynomial size
(`parity_superpoly_ac0p` at the odd prime `3`).  Hence `AC⁰[2] ⊄ AC⁰[3]` (`acc02_not_subset_acc03_unbounded`), so
`AC⁰[2] ≠ AC⁰[3]` even in the real model.

## What is proved (clean axioms, no `sorry`)

* **`acc02_not_subset_acc03_unbounded`** (PROVED) — `PARITY` is a depth-`1` `AC⁰[2]` circuit, but any depth-`d` `AC⁰[3]`
  circuit computing it has `3^t < 4·#{subcircuits}` (super-polynomial) — witnessing `AC⁰[2] ⊄ AC⁰[3]`.

## Honest scope

The prime-modulus separation `AC⁰[2] ⊄ AC⁰[3]` in the real unbounded-fan-in model.  The reverse `AC⁰[3] ⊄ AC⁰[2]` needs
`MOD_3 ∉ AC⁰[2]` (`p = 2` has no primitive cube root in the polynomial-method machinery), not claimed.  The **Williams
cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains **open** / not faked.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedPrimeSep

open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (parityFn)
open PallLean.Paper93.DeepMath.PathB.ACC0UnboundedSep (parity_mem_acc02_unbounded)
open PallLean.Paper93.DeepMath.PathB.ACC0UnboundedParity (parity_superpoly_ac0p)
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)

private theorem two_ne_zero_mod3 : (2 : ZMod 3) ≠ 0 := by decide

open Classical in
/-- **`AC⁰[2] ⊄ AC⁰[3]` in the real (unbounded-fan-in) model (PROVED).**  `PARITY` is a depth-`1` `AC⁰[2]` circuit (one
`MOD_2` gate) but every depth-`d` `AC⁰[3]` circuit computing it has `3^t < 4·(subcircuits).toFinset.card` (super-poly) — so
the `MOD`-gate prime is not interchangeable, `AC⁰[2] ≠ AC⁰[3]`. -/
theorem acc02_not_subset_acc03_unbounded {m d t : ℕ} (ht1 : 1 ≤ t) (hm : 8 * ((2 * t) ^ d) ^ 2 ≤ m) :
    (∃ Cir : BoolCircuitSyntax (2 * m + 1), BoolCircuitSyntax.IsAC0pSyntax 2 Cir ∧ Cir.depth ≤ 1
        ∧ Cir.eval = parityFn) ∧
      (∀ Cir : BoolCircuitSyntax (2 * m + 1), BoolCircuitSyntax.IsAC0pSyntax 3 Cir → Cir.depth ≤ d →
        Cir.eval = parityFn → 3 ^ t < 4 * (subcircuits Cir).toFinset.card) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨parity_mem_acc02_unbounded, ?_⟩
  intro Cir hac hd heval
  exact parity_superpoly_ac0p 3 two_ne_zero_mod3 Cir hac hd t ht1
    (fun x => by rw [heval]; rfl) (by simpa using hm)

/-!
**`AC⁰[2] ⊄ AC⁰[3]` in the real model, proved.**  The prime modulus genuinely matters in the unbounded-fan-in model —
`PARITY` separates the two `MOD`-prime classes.  Remaining (open, not faked): the reverse `AC⁰[3] ⊄ AC⁰[2]`, and the Williams
cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedPrimeSep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedPrimeSep.acc02_not_subset_acc03_unbounded
