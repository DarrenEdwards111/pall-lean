import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqSize

/-!
# Bridge (concrete instantiation) — `MOD_3` needs super-polynomial `AC⁰[5]` size (proved)

A concrete, self-contained instance of the Razborov–Smolensky size lower bound (`modq_requires_large_size`): taking the prime
`p = 5` and the coprime prime `q = 3` (`3 ∤ 5`), every uniform `AC⁰[5]` family computing `MOD_3` (the residue-`0` indicator
`[weight ≡ 0 mod 3]`) at constant depth `d` has, for every exponent `t`, some arity `N` with `5^t < 12·(subcircuits
(toBoolSyntax (D N))).length`.  This discharges the `Fact`-prime and `¬ q ∣ p` side conditions at concrete values,
demonstrating the abstract machinery yields a named separation.

## What is proved (clean axioms, no `sorry`)

* **`mod3_requires_large_size_acc05`** (PROVED) — `MOD_3` has no polynomial-size constant-depth `AC⁰[5]` family.

## Honest scope

This is one concrete instance (`p=5, q=3`) of the polynomial-method `MOD_q ∉ AC⁰[p]` size lower bound — the natural endpoint
of the Razborov–Smolensky arc.  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains
**open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod3Acc5

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax (toBoolSyntax)
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqSize (modq_requires_large_size)

/-- **`MOD_3` needs super-polynomial `AC⁰[5]` size (PROVED).**  A concrete instance of the RS size lower bound: no uniform
`AC⁰[5]` family computes `MOD_3` at constant depth with polynomially bounded size. -/
theorem mod3_requires_large_size_acc05 {d : ℕ} (D : (N : ℕ) → ACC0Circuit N)
    (hDind : ∀ N, ∀ y : Fin N → Bool,
      ACC0CircuitModel.eval (D N) y = decide ((Finset.univ.filter (fun i => y i = true)).card % 3 = 0))
    (hDmod : ∀ N, ModpOnly 5 (D N))
    (hDdepth : ∀ N, BoolCircuitSyntax.depth (toBoolSyntax (D N)) ≤ d)
    (t : ℕ) (ht1 : 1 ≤ t) :
    ∃ N, 5 ^ t < 12 * (subcircuits (toBoolSyntax (D N))).length := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := modq_requires_large_size 5 3 (by decide) D hDind hDmod hDdepth t ht1 (by omega)
  simpa using h

/-!
**A concrete RS separation, proved.**  `MOD_3 ∉` polynomial-size constant-depth `AC⁰[5]` — the abstract polynomial-method
machinery instantiated at concrete primes.  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not
`NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Mod3Acc5

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod3Acc5.mod3_requires_large_size_acc05
