import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0StrictSep

/-!
# Bridge (AC⁰[2] ⊄ AC⁰[3]) — the prime modulus matters (proved)

The `MOD`-gate prime is not interchangeable: `AC⁰[2]` and `AC⁰[3]` are genuinely different classes.  `PARITY` is computed by a
single `MOD_2` gate (so lies in `AC⁰[2]`), but `PARITY = MOD_2 ∉ AC⁰[3]` (the Razborov–Smolensky separation at the odd prime
`3`, for all `n`).  Hence `AC⁰[2] ⊄ AC⁰[3]` (`acc02_not_subset_acc03`), so in particular `AC⁰[2] ≠ AC⁰[3]`.

## What is proved (clean axioms, no `sorry`)

* **`acc02_not_subset_acc03`** (PROVED) — for `n > 2^{d+1}`, `PARITY ∈ AC⁰[2] \ AC⁰[3]`, witnessing `AC⁰[2] ⊄ AC⁰[3]`.

## Honest scope

This shows the prime modulus matters: `AC⁰[2] ≠ AC⁰[3]` (via `PARITY`).  The reverse non-inclusion `AC⁰[3] ⊄ AC⁰[2]` would
need `MOD_3 ∉ AC⁰[2]`, which the (odd-prime) polynomial-method machinery here does not supply (`p = 2` has no primitive cube
root), so it is not claimed.  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains
**open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimeSep

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (parityFn)
open PallLean.Paper93.DeepMath.PathB.ACC0StrictSep (parity_mem_acc02)
open PallLean.Paper93.DeepMath.PathB.ACC0DepthDegreeBound (parity_not_acc0p_depth)

/-- **`AC⁰[2] ⊄ AC⁰[3]` (PROVED).**  `PARITY` lies in `AC⁰[2]` (a single `MOD_2` gate, depth `1`) but not in `AC⁰[3]` (for
`n > 2^{d+1}`) — the `MOD`-gate prime is not interchangeable, so `AC⁰[2] ≠ AC⁰[3]`. -/
theorem acc02_not_subset_acc03 {n d : ℕ} (hd : 2 * 2 ^ d < n) :
    (∃ C : ACC0Circuit n, ModpOnly 2 C ∧ depth C ≤ 1 ∧ ACC0CircuitModel.eval C = parityFn) ∧
      ¬ ∃ C : ACC0Circuit n, ModpOnly 3 C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = parityFn := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact ⟨parity_mem_acc02, parity_not_acc0p_depth (p := 3) (by norm_num) (by simpa using hd)⟩

/-!
**`AC⁰[2] ⊄ AC⁰[3]`, proved.**  The prime modulus genuinely matters — `PARITY` separates the two `MOD`-prime classes.
Remaining (open, not faked): the reverse `AC⁰[3] ⊄ AC⁰[2]` (needs `MOD_3 ∉ AC⁰[2]`), and the Williams cash-out to
`NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PrimeSep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeSep.acc02_not_subset_acc03
