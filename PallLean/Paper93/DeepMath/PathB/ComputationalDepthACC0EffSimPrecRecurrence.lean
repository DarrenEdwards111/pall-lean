import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimRuntime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimIterationFuel

/-!
# Interpreter grind, step 2: runtime recurrence for `prec` — iteration enters (PROVED)

The key step: the `prec` runtime recurrence, where the iteration counter enters the bound.  `prec`'s
iteration step recurses at counter `y` **at fuel `k` (decremented by one)** (`evaln_prec_succ_fuel`).  So
the runtime at counter `y+1` is bounded by the runtime at counter `y` **plus one** — capturing exactly the
`+1`-per-iteration growth:

  `runtimeOf_prec_zero_le` — base: `runtimeOf (prec cf cg) (pair a 0) ≤ max (pair a 0 + 1) (runtimeOf cf a)`.
  `runtimeOf_prec_succ_le` — step: `runtimeOf (prec cf cg) (pair a (y+1)) ≤
    max (pair a (y+1) + 1) (max (runtimeOf (prec cf cg) (pair a y) + 1) (runtimeOf cg …))`.

The `runtimeOf (prec …) (pair a y) + 1` term is the decremented recursive fuel.  Iterating this recurrence
`m` times adds `m` — so `prec` runtime grows **linearly** in the iteration count `m`, confirming
quantitatively that iteration contributes only linear fuel (the earlier qualitative claim, now grounded as
a proved recurrence).

## What is proved (clean axioms, no `sorry`)

* `runtimeOf_prec_zero_le`, `runtimeOf_prec_succ_le` — the `prec` runtime recurrence (base + step).

## Honest scope

The `prec` runtime recurrence (linear-in-iteration).  `rfind'` is analogous; solving the recurrence into a
closed runtime bound, then the explicit universal interpreter + value-bound, remain the grind ahead.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimPrecRecurrence

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime
  (runtimeOf runtimeOf_isSome le_runtimeOf evaln_runtimeOf_stable)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimIterationFuel
  (evaln_prec_zero_fuel evaln_prec_succ_fuel)

/-- **`prec` runtime recurrence, base (proved).** -/
theorem runtimeOf_prec_zero_le {cf cg : Code} {a : ℕ}
    (hf : ∃ k, (Code.evaln k cf a).isSome)
    (hprec : ∃ k, (Code.evaln k (Code.prec cf cg) (Nat.pair a 0)).isSome) :
    runtimeOf (Code.prec cf cg) (Nat.pair a 0) hprec ≤ max (Nat.pair a 0 + 1) (runtimeOf cf a hf) := by
  obtain ⟨vf, hfv⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome cf a hf)
  set K := max (Nat.pair a 0 + 1) (runtimeOf cf a hf) with hKdef
  have hn1 : Nat.pair a 0 + 1 ≤ K := le_max_left _ _
  have hrf : runtimeOf cf a hf ≤ K := le_max_right _ _
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hnk : Nat.pair a 0 ≤ k := by omega
  have hfk : Code.evaln (k + 1) cf a = some vf := by
    rw [← hk, evaln_runtimeOf_stable cf a hf hrf]; exact hfv
  have hpreck : Code.evaln (k + 1) (Code.prec cf cg) (Nat.pair a 0) = some vf :=
    evaln_prec_zero_fuel hnk hfk
  rw [hk]
  exact le_runtimeOf (Code.prec cf cg) (Nat.pair a 0) hprec (by rw [hpreck]; rfl)

/-- **`prec` runtime recurrence, iteration step (proved): the recursive term carries `+1` (the decremented
fuel) — linear-in-iteration growth.** -/
theorem runtimeOf_prec_succ_le {cf cg : Code} {a y i : ℕ}
    (hp : ∃ k, (Code.evaln k (Code.prec cf cg) (Nat.pair a y)).isSome)
    (hpi : Code.evaln (runtimeOf (Code.prec cf cg) (Nat.pair a y) hp) (Code.prec cf cg) (Nat.pair a y)
      = some i)
    (hg : ∃ k, (Code.evaln k cg (Nat.pair a (Nat.pair y i))).isSome)
    (hprec : ∃ k, (Code.evaln k (Code.prec cf cg) (Nat.pair a (y + 1))).isSome) :
    runtimeOf (Code.prec cf cg) (Nat.pair a (y + 1)) hprec
      ≤ max (Nat.pair a (y + 1) + 1)
          (max (runtimeOf (Code.prec cf cg) (Nat.pair a y) hp + 1)
               (runtimeOf cg (Nat.pair a (Nat.pair y i)) hg)) := by
  obtain ⟨vg, hgv⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome cg (Nat.pair a (Nat.pair y i)) hg)
  set K := max (Nat.pair a (y + 1) + 1)
      (max (runtimeOf (Code.prec cf cg) (Nat.pair a y) hp + 1)
           (runtimeOf cg (Nat.pair a (Nat.pair y i)) hg)) with hKdef
  have hn1 : Nat.pair a (y + 1) + 1 ≤ K := le_max_left _ _
  have hrp : runtimeOf (Code.prec cf cg) (Nat.pair a y) hp + 1 ≤ K :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hrg : runtimeOf cg (Nat.pair a (Nat.pair y i)) hg ≤ K :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hnk : Nat.pair a (y + 1) ≤ k := by omega
  have hrpk : runtimeOf (Code.prec cf cg) (Nat.pair a y) hp ≤ k := by omega
  have hik : Code.evaln k (Code.prec cf cg) (Nat.pair a y) = some i := by
    rw [evaln_runtimeOf_stable (Code.prec cf cg) (Nat.pair a y) hp hrpk]; exact hpi
  have hgk : Code.evaln (k + 1) cg (Nat.pair a (Nat.pair y i)) = some vg := by
    rw [← hk, evaln_runtimeOf_stable cg (Nat.pair a (Nat.pair y i)) hg hrg]; exact hgv
  have hpreck : Code.evaln (k + 1) (Code.prec cf cg) (Nat.pair a (y + 1)) = some vg :=
    evaln_prec_succ_fuel hnk hik hgk
  rw [hk]
  exact le_runtimeOf (Code.prec cf cg) (Nat.pair a (y + 1)) hprec (by rw [hpreck]; rfl)

/-!
**Interpreter grind step 2 proved.**  `prec` runtime recurrence: the iteration step carries `+1` (the
decremented recursive fuel), so `m` iterations add `m` — runtime is **linear** in the iteration count, now
a proved recurrence (not just a heuristic).  Next: `rfind'`, solving the recurrence, the explicit
interpreter.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimPrecRecurrence

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimPrecRecurrence.runtimeOf_prec_succ_le
