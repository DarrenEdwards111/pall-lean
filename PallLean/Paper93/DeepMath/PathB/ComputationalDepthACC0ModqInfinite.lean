import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqPeriod

/-!
# Brick (MOD_q infinite) — `MOD_q ∉` constant-depth `AC⁰[p]` for infinitely many arities (proved)

The asymptotic packaging of the periodic `MOD_q` separation (Brick MOD_q period).  Since `n ≡ 1 mod (p−1)` admits infinitely
many `n` (any `n = 1 + k(p−1)`), the unconditional separation `MOD_q ∉` depth-`d` `AC⁰[p]` holds for arbitrarily large
arities: for every bound `N` there is an `n > N` with the `n`-ary `MOD_q` not computed by any depth-`d` `AC⁰[p]` circuit.

This is the standard "for infinitely many `n`" form of the `q>2` Razborov–Smolensky separation, in-framework and
unconditional (for `ζ` a primitive `q`-th root, `q ∣ p−1`, `p` odd).

## What is proved (clean axioms, no `sorry`)

* **`exists_large_arity_modq_not_acc0p`** (PROVED) — `∀ N, ∃ n > N, ¬∃ C : ACC0Circuit n, ModpOnly p C ∧ depth C ≤ d ∧ eval C
  = MOD_q` — the separation for arbitrarily large arities.

## Honest scope

The unconditional `q>2` separation for infinitely many arities (the `n ≡ 1 mod (p−1)` family).  It does **not** cover *all*
large `n` (the full RS rank bound; tree's `Layer4`) nor the Williams cash-out.  General YBT and `NEXP ⊄ ACC⁰` remain open.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqInfinite

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness (modqFn)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqPeriod (modq_not_acc0p_depth_period)

variable {p : ℕ} [Fact p.Prime]

/-- **`MOD_q ∉` constant-depth `AC⁰[p]` for arbitrarily large arities (PROVED).** -/
theorem exists_large_arity_modq_not_acc0p (hp2 : p ≠ 2) (q : ℕ) (hq2 : 2 ≤ q) (hq : (q : ZMod p) ≠ 0)
    (ζ : ZMod p) (hord : orderOf ζ = q) (d : ℕ) (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      ¬ ∃ C : ACC0Circuit n, ModpOnly p C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = modqFn q := by
  have hp1 : 0 < p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  have hmul : (N + (p - 1) * 2 ^ d + 1) ≤ (N + (p - 1) * 2 ^ d + 1) * (p - 1) :=
    Nat.le_mul_of_pos_right _ hp1
  refine ⟨1 + (N + (p - 1) * 2 ^ d + 1) * (p - 1), by omega, ?_⟩
  refine modq_not_acc0p_depth_period hp2 q hq2 hq ζ hord (by omega)
    ⟨N + (p - 1) * 2 ^ d + 1, by rw [Nat.mul_comm]; omega⟩ (by omega)

/-!
**The asymptotic `MOD_q` separation, proved.**  For arbitrarily large arities `n`, `MOD_q ∉` constant-depth `AC⁰[p]` — the
standard "infinitely many `n`" form of the `q>2` Razborov–Smolensky separation, unconditional and in-framework.  Remaining
(open, not faked): all large `n` (RS rank bound), Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqInfinite

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqInfinite.exists_large_arity_modq_not_acc0p
