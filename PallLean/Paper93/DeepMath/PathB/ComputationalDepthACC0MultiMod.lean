import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0StrictSep

/-!
# Bridge (AC⁰[3] ⊊ AC⁰[{2,3}]) — adding moduli strictly grows the class (proved)

The constant-depth `MOD`-class hierarchy grows with the set of available moduli.  Let `AC⁰[{2,3}]` be the circuits whose
`MOD` gates use modulus `2` or `3` (`ModIn23`).  Then `AC⁰[3] ⊆ AC⁰[{2,3}]` (`modpOnly3_modIn23`), and the inclusion is
strict: `PARITY` is computed by a single `MOD_2` gate — so it lies in `AC⁰[{2,3}]` — yet `PARITY ∉ AC⁰[3]`.  Hence
`AC⁰[3] ⊊ AC⁰[{2,3}]` (`acc03_strict_subset_acc023`): granting the prime `2` to an `AC⁰[3]` circuit strictly increases power.

## What is proved (clean axioms, no `sorry`)

* **`ModIn23`** — the `AC⁰[{2,3}]` predicate (`MOD` moduli in `{2,3}`).
* **`modpOnly3_modIn23`** (PROVED) — `AC⁰[3] ⊆ AC⁰[{2,3}]`.
* **`parity_mem_acc023`** (PROVED) — `PARITY ∈ AC⁰[{2,3}]` at depth `1`.
* **`acc03_strict_subset_acc023`** (PROVED) — `PARITY ∈ AC⁰[{2,3}] \ AC⁰[3]` (for `n > 2^{d+1}`), witnessing the strict
  inclusion.

## Honest scope

This is the multi-modulus hierarchy growth `AC⁰[3] ⊊ AC⁰[{2,3}]`.  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different,
P≠NP-strength theorem and remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MultiMod

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (parityFn)
open PallLean.Paper93.DeepMath.PathB.ACC0StrictSep (eval_mod2_univ)
open PallLean.Paper93.DeepMath.PathB.ACC0DepthDegreeBound (parity_not_acc0p_depth)

variable {n : ℕ}

/-- `AC⁰[{2,3}]` circuits: `MOD` gates use modulus `2` or `3`. -/
def ModIn23 : ACC0Circuit n → Prop
  | .const _ => True
  | .var _ => True
  | .not c => ModIn23 c
  | .and a b => ModIn23 a ∧ ModIn23 b
  | .or a b => ModIn23 a ∧ ModIn23 b
  | .mod q _ _ => q = 2 ∨ q = 3

/-- **`AC⁰[3] ⊆ AC⁰[{2,3}]` (PROVED).** -/
theorem modpOnly3_modIn23 (C : ACC0Circuit n) (h : ModpOnly 3 C) : ModIn23 C := by
  induction C with
  | const b => trivial
  | var i => trivial
  | not c ih => exact ih (by simpa [ModpOnly] using h)
  | and a b iha ihb => simp only [ModpOnly] at h; exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb => simp only [ModpOnly] at h; exact ⟨iha h.1, ihb h.2⟩
  | mod q S t => simp only [ModpOnly] at h; exact Or.inr h

/-- **`PARITY ∈ AC⁰[{2,3}]` at depth `1` (PROVED).** -/
theorem parity_mem_acc023 :
    ∃ C : ACC0Circuit n, ModIn23 C ∧ depth C ≤ 1 ∧ ACC0CircuitModel.eval C = parityFn :=
  ⟨.mod 2 Finset.univ 1, Or.inl rfl, le_refl 1, eval_mod2_univ⟩

/-- **`AC⁰[3] ⊊ AC⁰[{2,3}]` (PROVED).**  Granting the prime `2` strictly increases power: `PARITY ∈ AC⁰[{2,3}]` (one `MOD_2`
gate) but `PARITY ∉ AC⁰[3]` (for `n > 2^{d+1}`). -/
theorem acc03_strict_subset_acc023 {d : ℕ} (hd : 2 * 2 ^ d < n) :
    (∃ C : ACC0Circuit n, ModIn23 C ∧ depth C ≤ 1 ∧ ACC0CircuitModel.eval C = parityFn) ∧
      ¬ ∃ C : ACC0Circuit n, ModpOnly 3 C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = parityFn := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact ⟨parity_mem_acc023, parity_not_acc0p_depth (p := 3) (by norm_num) (by simpa using hd)⟩

/-!
**`AC⁰[3] ⊊ AC⁰[{2,3}]`, proved.**  The `MOD`-class hierarchy grows with the moduli set: adding the prime `2` to `AC⁰[3]`
strictly increases power (`PARITY` separates).  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not
`NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0MultiMod

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MultiMod.acc03_strict_subset_acc023
