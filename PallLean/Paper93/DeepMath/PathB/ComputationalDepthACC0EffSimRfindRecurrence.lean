import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimRuntime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimIterationFuel

/-!
# Interpreter grind, step 2b: runtime recurrence for `rfind'` — recurrences complete (PROVED)

The `rfind'` runtime recurrence, completing the iterating-constructor recurrences.  `rfind'`'s continuation
recurses at counter `m+1` **at fuel `k` (decremented)** (`evaln_rfind'_step_fuel`), so the runtime at `m`
is bounded by the runtime at `m+1` **plus one** — linear in the search depth, like `prec`:

  `runtimeOf_rfind'_found_le` — halt (`cf = 0`): `runtimeOf (rfind' cf) (pair a m) ≤
    max (pair a m + 1) (runtimeOf cf (pair a m))`.
  `runtimeOf_rfind'_step_le` — continue (`cf ≠ 0`): `runtimeOf (rfind' cf) (pair a m) ≤
    max (pair a m + 1) (max (runtimeOf cf (pair a m)) (runtimeOf (rfind' cf) (pair a (m+1)) + 1))`.

With steps 1 (`comp`/`pair`) and 2 (`prec`), the runtime recurrences now cover **all** recursive `Code`
constructors; iteration contributes `+1` per step (proved), so runtime is linear in iteration depth.

## What is proved (clean axioms, no `sorry`)

* `runtimeOf_rfind'_found_le`, `runtimeOf_rfind'_step_le` — the `rfind'` runtime recurrence.

## Honest scope

The runtime recurrences are complete (all constructors).  Solving them into a closed runtime bound, then
the explicit universal interpreter + value-bound, remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimRfindRecurrence

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime
  (runtimeOf runtimeOf_isSome le_runtimeOf evaln_runtimeOf_stable)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimIterationFuel
  (evaln_rfind'_found_fuel evaln_rfind'_step_fuel)

/-- **`rfind'` runtime recurrence, halt case (proved).** -/
theorem runtimeOf_rfind'_found_le {cf : Code} {a m : ℕ}
    (hc : ∃ k, (Code.evaln k cf (Nat.pair a m)).isSome)
    (hcx : Code.evaln (runtimeOf cf (Nat.pair a m) hc) cf (Nat.pair a m) = some 0)
    (hrf : ∃ k, (Code.evaln k (Code.rfind' cf) (Nat.pair a m)).isSome) :
    runtimeOf (Code.rfind' cf) (Nat.pair a m) hrf
      ≤ max (Nat.pair a m + 1) (runtimeOf cf (Nat.pair a m) hc) := by
  set K := max (Nat.pair a m + 1) (runtimeOf cf (Nat.pair a m) hc) with hKdef
  have hn1 : Nat.pair a m + 1 ≤ K := le_max_left _ _
  have hrc : runtimeOf cf (Nat.pair a m) hc ≤ K := le_max_right _ _
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hnk : Nat.pair a m ≤ k := by omega
  have hxk : Code.evaln (k + 1) cf (Nat.pair a m) = some 0 := by
    rw [← hk, evaln_runtimeOf_stable cf (Nat.pair a m) hc hrc]; exact hcx
  have hrfk : Code.evaln (k + 1) (Code.rfind' cf) (Nat.pair a m) = some m :=
    evaln_rfind'_found_fuel hnk hxk
  rw [hk]
  exact le_runtimeOf (Code.rfind' cf) (Nat.pair a m) hrf (by rw [hrfk]; rfl)

/-- **`rfind'` runtime recurrence, continuation case (proved): the recursive term carries `+1` (decremented
fuel) — linear in search depth.** -/
theorem runtimeOf_rfind'_step_le {cf : Code} {a m x : ℕ} (hx0 : x ≠ 0)
    (hc : ∃ k, (Code.evaln k cf (Nat.pair a m)).isSome)
    (hcx : Code.evaln (runtimeOf cf (Nat.pair a m) hc) cf (Nat.pair a m) = some x)
    (hr : ∃ k, (Code.evaln k (Code.rfind' cf) (Nat.pair a (m + 1))).isSome)
    (hrf : ∃ k, (Code.evaln k (Code.rfind' cf) (Nat.pair a m)).isSome) :
    runtimeOf (Code.rfind' cf) (Nat.pair a m) hrf
      ≤ max (Nat.pair a m + 1)
          (max (runtimeOf cf (Nat.pair a m) hc) (runtimeOf (Code.rfind' cf) (Nat.pair a (m + 1)) hr + 1)) := by
  obtain ⟨vr, hrv⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome (Code.rfind' cf) (Nat.pair a (m + 1)) hr)
  set K := max (Nat.pair a m + 1)
      (max (runtimeOf cf (Nat.pair a m) hc) (runtimeOf (Code.rfind' cf) (Nat.pair a (m + 1)) hr + 1))
      with hKdef
  have hn1 : Nat.pair a m + 1 ≤ K := le_max_left _ _
  have hrc : runtimeOf cf (Nat.pair a m) hc ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrr : runtimeOf (Code.rfind' cf) (Nat.pair a (m + 1)) hr + 1 ≤ K :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hnk : Nat.pair a m ≤ k := by omega
  have hrrk : runtimeOf (Code.rfind' cf) (Nat.pair a (m + 1)) hr ≤ k := by omega
  have hxk : Code.evaln (k + 1) cf (Nat.pair a m) = some x := by
    rw [← hk, evaln_runtimeOf_stable cf (Nat.pair a m) hc hrc]; exact hcx
  have hrk : Code.evaln k (Code.rfind' cf) (Nat.pair a (m + 1)) = some vr := by
    rw [evaln_runtimeOf_stable (Code.rfind' cf) (Nat.pair a (m + 1)) hr hrrk]; exact hrv
  have hrfk : Code.evaln (k + 1) (Code.rfind' cf) (Nat.pair a m) = some vr :=
    evaln_rfind'_step_fuel hnk hx0 hxk hrk
  rw [hk]
  exact le_runtimeOf (Code.rfind' cf) (Nat.pair a m) hrf (by rw [hrfk]; rfl)

/-!
**Interpreter grind step 2b proved — recurrences complete.**  `rfind'` runtime recurrence: continuation
carries `+1` (decremented fuel), so runtime is linear in search depth.  All recursive constructors now have
runtime recurrences.  Next: solve into a closed bound, then the explicit interpreter.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimRfindRecurrence

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimRfindRecurrence.runtimeOf_rfind'_step_le
