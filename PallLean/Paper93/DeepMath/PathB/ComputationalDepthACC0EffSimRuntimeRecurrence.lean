import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimRuntime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimFuelComposition

/-!
# Interpreter grind, step 1: runtime upper-bound recurrences for `comp`/`pair` (PROVED)

The committed Hennie–Stearns interpreter grind.  The fuel-*sufficiency* lemmas (`evaln_comp_fuel` etc.)
say "fuel `k+1` works for the composite if it works for the parts and `n ≤ k`".  Combined with rung 1's
runtime measure and **stability**, they yield runtime **upper-bound recurrences** — `runtimeOf` of a
composite bounded by the `runtimeOf`s of its parts:

  `runtimeOf_comp_le` — `runtimeOf (comp cf cg) n ≤ max (n+1) (max (runtimeOf cg n) (runtimeOf cf w))`
    where `w` is `cg`'s output.
  `runtimeOf_pair_le` — `runtimeOf (pair cf cg) n ≤ max (n+1) (max (runtimeOf cf n) (runtimeOf cg n))`.

These are the cost-recurrence building blocks: solving them over a code's structure gives an explicit
runtime bound, the foundation for bounding the universal interpreter's fuel.

## What is proved (clean axioms, no `sorry`)

* `runtimeOf_comp_le`, `runtimeOf_pair_le` — runtime recurrences for the non-iterating constructors.

## Honest scope

The non-iterating runtime recurrences (built from rungs 1 + 5a via stability).  The `prec`/`rfind'`
recurrences (where the iteration count enters) and assembling them into an explicit universal interpreter
+ value-bound remain the grind ahead.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntimeRecurrence

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime
  (runtimeOf runtimeOf_isSome le_runtimeOf evaln_runtimeOf_stable)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimFuelComposition (evaln_comp_fuel evaln_pair_fuel)

/-- **Runtime recurrence for `comp` (proved).** -/
theorem runtimeOf_comp_le {cf cg : Code} {n w : ℕ}
    (hg : ∃ k, (Code.evaln k cg n).isSome)
    (hgw : Code.evaln (runtimeOf cg n hg) cg n = some w)
    (hf : ∃ k, (Code.evaln k cf w).isSome)
    (hcomp : ∃ k, (Code.evaln k (Code.comp cf cg) n).isSome) :
    runtimeOf (Code.comp cf cg) n hcomp
      ≤ max (n + 1) (max (runtimeOf cg n hg) (runtimeOf cf w hf)) := by
  obtain ⟨vf, hfw⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome cf w hf)
  set K := max (n + 1) (max (runtimeOf cg n hg) (runtimeOf cf w hf)) with hKdef
  have hn1 : n + 1 ≤ K := le_max_left _ _
  have hrg : runtimeOf cg n hg ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrf : runtimeOf cf w hf ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hnk : n ≤ k := by omega
  have hgK : Code.evaln (k + 1) cg n = some w := by
    rw [← hk, evaln_runtimeOf_stable cg n hg hrg]; exact hgw
  have hfK : Code.evaln (k + 1) cf w = some vf := by
    rw [← hk, evaln_runtimeOf_stable cf w hf hrf]; exact hfw
  have hcompK : Code.evaln (k + 1) (Code.comp cf cg) n = some vf := evaln_comp_fuel hnk hgK hfK
  rw [hk]
  exact le_runtimeOf (Code.comp cf cg) n hcomp (by rw [hcompK]; rfl)

/-- **Runtime recurrence for `pair` (proved).** -/
theorem runtimeOf_pair_le {cf cg : Code} {n : ℕ}
    (hf : ∃ k, (Code.evaln k cf n).isSome)
    (hg : ∃ k, (Code.evaln k cg n).isSome)
    (hpair : ∃ k, (Code.evaln k (Code.pair cf cg) n).isSome) :
    runtimeOf (Code.pair cf cg) n hpair
      ≤ max (n + 1) (max (runtimeOf cf n hf) (runtimeOf cg n hg)) := by
  obtain ⟨a, hfa⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome cf n hf)
  obtain ⟨b, hgb⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome cg n hg)
  set K := max (n + 1) (max (runtimeOf cf n hf) (runtimeOf cg n hg)) with hKdef
  have hn1 : n + 1 ≤ K := le_max_left _ _
  have hrf : runtimeOf cf n hf ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrg : runtimeOf cg n hg ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hnk : n ≤ k := by omega
  have hfK : Code.evaln (k + 1) cf n = some a := by
    rw [← hk, evaln_runtimeOf_stable cf n hf hrf]; exact hfa
  have hgK : Code.evaln (k + 1) cg n = some b := by
    rw [← hk, evaln_runtimeOf_stable cg n hg hrg]; exact hgb
  have hpairK : Code.evaln (k + 1) (Code.pair cf cg) n = some (Nat.pair a b) := evaln_pair_fuel hnk hfK hgK
  rw [hk]
  exact le_runtimeOf (Code.pair cf cg) n hpair (by rw [hpairK]; rfl)

/-!
**Interpreter grind step 1 proved.**  Runtime recurrences for `comp`/`pair`: the composite's `runtimeOf`
is bounded by `max(n+1, parts' runtimeOf)`.  Next: `prec`/`rfind'` recurrences (iteration count enters),
then solving the recurrence over code structure, then the explicit universal interpreter.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntimeRecurrence

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntimeRecurrence.runtimeOf_comp_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntimeRecurrence.runtimeOf_pair_le
