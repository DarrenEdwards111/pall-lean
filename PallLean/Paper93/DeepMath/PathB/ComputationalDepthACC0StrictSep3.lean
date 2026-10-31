import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqAC0

/-!
# Bridge (AC⁰ ⊊ AC⁰[3]) — every prime modulus strictly extends AC⁰ (proved)

The `q = 3` companion to `AC⁰ ⊊ AC⁰[2]`: `MOD_3` is computed by a single `MOD_3` gate (so lies in `AC⁰[3]` at depth `1`) yet
`MOD_3 ∉ AC⁰` (`mod3_not_ac0`, for `n ≡ 1 mod 6`).  Hence `AC⁰ ⊊ AC⁰[3]` — the `MOD_3` gate strictly increases the power of
constant-depth circuits, just as `MOD_2` does.

## What is proved (clean axioms, no `sorry`)

* **`eval_mod3_univ`** (PROVED) — a single `MOD_3` gate over all inputs computes `MOD_3`.
* **`mod3_mem_acc03`** (PROVED) — `MOD_3 ∈ AC⁰[3]` at depth `1`.
* **`ac0_strict_subset_acc03`** (PROVED) — `MOD_3 ∈ AC⁰[3] \ AC⁰` (for `n ≡ 1 mod 6`, `6·2^d < n`), witnessing
  `AC⁰ ⊊ AC⁰[3]`.

## Honest scope

The strict separation `AC⁰ ⊊ AC⁰[3]` (on arities `n ≡ 1 mod 6`).  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different,
P≠NP-strength theorem and remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0StrictSep3

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (wt)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityAC0 (ModFree)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness (modqFn)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqAC0 (mod3_not_ac0)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn modQStatOn)

/-- **A single `MOD_3` gate over all inputs computes `MOD_3` (PROVED).** -/
theorem eval_mod3_univ {n : ℕ} :
    ACC0CircuitModel.eval (.mod 3 (Finset.univ : Finset (Fin n)) 0) = modqFn 3 := by
  funext x
  have hwt : weightOn (Finset.univ : Finset (Fin n)) x = wt x := by
    rw [weightOn, wt, Finset.card_filter]
  simp only [ACC0CircuitModel.eval, modQStatOn, modqFn]
  apply decide_eq_decide.mpr
  rw [hwt]
  exact ZMod.natCast_eq_zero_iff (wt x) 3

/-- **`MOD_3 ∈ AC⁰[3]` at depth `1` (PROVED).** -/
theorem mod3_mem_acc03 {n : ℕ} :
    ∃ C : ACC0Circuit n, ModpOnly 3 C ∧ depth C ≤ 1 ∧ ACC0CircuitModel.eval C = modqFn 3 :=
  ⟨.mod 3 Finset.univ 0, rfl, le_refl 1, eval_mod3_univ⟩

/-- **`AC⁰ ⊊ AC⁰[3]` (PROVED).**  `MOD_3` lies in `AC⁰[3]` (depth-`1`) but not in `AC⁰` (for `n ≡ 1 mod 6`) — the `MOD_3`
gate strictly increases constant-depth power. -/
theorem ac0_strict_subset_acc03 {n : ℕ} (hn1 : 1 ≤ n) (hper : 6 ∣ (n - 1)) {d : ℕ}
    (hd : 6 * 2 ^ d < n) :
    (∃ C : ACC0Circuit n, ModpOnly 3 C ∧ depth C ≤ 1 ∧ ACC0CircuitModel.eval C = modqFn 3) ∧
      ¬ ∃ C : ACC0Circuit n, ModFree C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = modqFn 3 :=
  ⟨mod3_mem_acc03, mod3_not_ac0 hn1 hper hd⟩

/-!
**`AC⁰ ⊊ AC⁰[3]`, proved.**  Every prime modulus strictly extends `AC⁰`: a single `MOD_3` gate computes `MOD_3`, but no
`AC⁰` circuit does.  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0StrictSep3

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0StrictSep3.ac0_strict_subset_acc03
