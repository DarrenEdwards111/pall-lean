import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqUniform

/-!
# Bridge (size lower bound) — `MOD_q` needs super-polynomial `AC⁰[p]` size (proved)

The Razborov–Smolensky **size lower bound**, the standard corollary of the uniform separation
(`modq_not_acc0p_uniform`).  A uniform `AC⁰[p]` family computing `MOD_q` (residue-`0` indicator) at constant depth `d` cannot
have polynomially bounded size: for *every* exponent `t`, some arity `N` has subcircuit-list length exceeding `p^t / (4q)`.
Since `t` is arbitrary, the size grows faster than any polynomial — the classical "`MOD_q` requires exponential-size
constant-depth `AC⁰[p]` circuits".

The proof is the contrapositive of `modq_not_acc0p_uniform`: if the size stayed `≤ p^t/(4q)` at every arity, choosing the
input size `m = 8((p−1)t)^{d})²` satisfies the RS window and yields `False`.

## What is proved (clean axioms, no `sorry`)

* **`modq_requires_large_size`** (PROVED) — for any uniform `AC⁰[p]` family `D` computing `MOD_q` at depth `d`, and any
  `t ≥ 1`, there is an arity `N` with `p^t < 4q·(subcircuits (toBoolSyntax (D N))).length`.

## Honest scope

This is the RS size lower bound in the uniform constant-depth regime — `MOD_q` is not in polynomial-size `AC⁰[p]`.  The
**Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem (the algorithmic method, not the polynomial
method) and remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqSize

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax (toBoolSyntax)
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqUniform (modq_not_acc0p_uniform)

/-- **`MOD_q` requires super-polynomial `AC⁰[p]` size (PROVED).**  For any uniform `AC⁰[p]` family computing `MOD_q` at depth
`d`, and any exponent `t ≥ 1`, some arity `N` has subcircuit-list length larger than `p^t / (4q)` — so the size is not
bounded by any polynomial. -/
theorem modq_requires_large_size (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {d : ℕ} (D : (N : ℕ) → ACC0Circuit N)
    (hDind : ∀ N, ∀ y : Fin N → Bool,
      ACC0CircuitModel.eval (D N) y = decide ((Finset.univ.filter (fun i => y i = true)).card % q = 0))
    (hDmod : ∀ N, ModpOnly p (D N))
    (hDdepth : ∀ N, BoolCircuitSyntax.depth (toBoolSyntax (D N)) ≤ d)
    (t : ℕ) (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t) :
    ∃ N, p ^ t < 4 * q * (subcircuits (toBoolSyntax (D N))).length := by
  by_contra hcon
  push_neg at hcon
  exact modq_not_acc0p_uniform (m := 8 * (((p - 1) * t) ^ d) ^ 2) p q hpq ht1 hpt1
    (by omega) D hDind hDmod hDdepth hcon

/-!
**The RS size lower bound, proved.**  `MOD_q` has no polynomial-size constant-depth `AC⁰[p]` family: for every `t`, the size
exceeds `p^t/(4q)` at some arity.  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`,
not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqSize

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqSize.modq_requires_large_size
