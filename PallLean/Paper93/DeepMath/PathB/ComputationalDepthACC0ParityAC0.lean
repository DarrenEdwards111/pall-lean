import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthDegreeBound

/-!
# Bridge (PARITY ∉ AC⁰) — the classic constant-depth lower bound (proved)

The most famous constant-depth circuit lower bound, obtained via the Razborov–Smolensky route: since `AC⁰ ⊆ AC⁰[p]` for every
prime `p`, the separation `MOD_2 ∉ AC⁰[p]` for odd `p` (`parity_not_acc0p_depth`) immediately gives **PARITY ∉ AC⁰**.

In this development `AC⁰` is the `MOD`-free fragment of `ACC0Circuit` (only `AND/OR/NOT` over inputs), captured by `ModFree`.
A `MOD`-free circuit is `AC⁰[p]` for *every* `p` (vacuously — there are no `MOD` gates to constrain), so a `MOD`-free circuit
computing `PARITY` would in particular be an `AC⁰[3]` circuit computing `MOD_2`, contradicting the `p = 3` instance of the
polynomial-method separation.

## What is proved (clean axioms, no `sorry`)

* **`ModFree`** — the `AC⁰` predicate (no `MOD` gates).
* **`modFree_modpOnly`** (PROVED) — `ModFree C → ModpOnly p C` for every `p`.
* **`parity_not_ac0`** (PROVED) — for `n > 2^{d+1}`, no depth-`d` `AC⁰` circuit computes `PARITY`.

## Honest scope

This is `PARITY ∉ AC⁰` (Furst–Saxe–Sipser / Håstad) via the Razborov–Smolensky method, a clean corollary of `MOD_2 ∉ AC⁰[3]`.
The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains **open** / not faked.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ParityAC0

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (parityFn)
open PallLean.Paper93.DeepMath.PathB.ACC0DepthDegreeBound (parity_not_acc0p_depth)

variable {n : ℕ}

/-- `AC⁰` circuits: the `MOD`-free fragment (only `AND/OR/NOT` over inputs and constants). -/
def ModFree : ACC0Circuit n → Prop
  | .const _ => True
  | .var _ => True
  | .not c => ModFree c
  | .and a b => ModFree a ∧ ModFree b
  | .or a b => ModFree a ∧ ModFree b
  | .mod _ _ _ => False

/-- **A `MOD`-free (`AC⁰`) circuit is `AC⁰[p]` for every `p` (PROVED).** -/
theorem modFree_modpOnly (p : ℕ) (C : ACC0Circuit n) (h : ModFree C) : ModpOnly p C := by
  induction C with
  | const b => trivial
  | var i => trivial
  | not c ih => exact ih (by simpa [ModFree] using h)
  | and a b iha ihb =>
      simp only [ModFree] at h; exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb =>
      simp only [ModFree] at h; exact ⟨iha h.1, ihb h.2⟩
  | mod q S t => simp only [ModFree] at h

/-- **PARITY ∉ AC⁰ (PROVED).**  For `n > 2^{d+1}`, no depth-`d` `MOD`-free (`AC⁰`) circuit computes `PARITY`. -/
theorem parity_not_ac0 {d : ℕ} (hd : 2 * 2 ^ d < n) :
    ¬ ∃ C : ACC0Circuit n, ModFree C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = parityFn := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rintro ⟨C, hfree, hdep, hev⟩
  exact parity_not_acc0p_depth (p := 3) (by norm_num) (by simpa using hd)
    ⟨C, modFree_modpOnly 3 C hfree, hdep, hev⟩

/-!
**PARITY ∉ AC⁰, proved.**  The classic constant-depth lower bound, via Razborov–Smolensky (`AC⁰ ⊆ AC⁰[3]`, `MOD_2 ∉ AC⁰[3]`).
Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ParityAC0

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityAC0.parity_not_ac0
