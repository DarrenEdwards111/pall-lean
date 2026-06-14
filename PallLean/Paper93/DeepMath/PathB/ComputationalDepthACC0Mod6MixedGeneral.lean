import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Mod6Mixed

/-!
# Mixed moduli `MOD₆`, general `ρ`: forced true ∧, forced false ∨

`mod6_realizable_iff_mixed` handled a *forced-true* `MOD₆` family (every gate must fire).  This file does the general
restriction `ρ : Fin k → Option Bool`, mixing forced-true and forced-false gates.  By CRT a `MOD₆` gate fires iff its
count is `≡ target` mod 2 **and** mod 3, so **forcing it false negates that conjunction** — giving a *disjunction*:

```
(MOD₆ S t).eval x = false  ⟺  count_S(x) ≢ t.val [MOD 2]  ∨  count_S(x) ≢ t.val [MOD 3]
```

So a general forced `MOD₆` family is realizable iff there is a Boolean `x` meeting, per gate, a **conjunction** of the
two CRT congruences (forced-true gates) and a **disjunction** of the two CRT disequalities (forced-false gates) — all
coupled through the shared `x`.  This is the honest fully-general mixed-modulus realization condition.

## What is proved (clean axioms, no `sorry`)

* `mod6_eval_false_iff` — forcing a `MOD₆` gate false is the disjunction of the two CRT disequalities.
* `mod6_realizable_iff_general` — general `ρ` realizability: `∃ x` meeting the per-gate conjunction (true) /
  disjunction (false) of the mod-2 and mod-3 conditions.

## Honest scope

The forced-false disjunction is exactly why the composite case is harder than either prime alone: the feasibility
region is an intersection of clauses each of which is itself a conjunction (true gates) or disjunction (false gates)
of a linear (mod 2) and a feasibility (mod 3) atom — a genuine mixed CSP over the Boolean cube, with no rank or
product shortcut.  Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod6MixedGeneral

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization
open PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6Mixed

variable {n k : ℕ}

/-- **Forcing a `MOD₆` gate false (proved): the disjunction of the two CRT disequalities.** -/
theorem mod6_eval_false_iff (S : Finset (Fin n)) (t : ZMod 6) (x : Fin n → Bool) :
    (⟨6, S, t⟩ : ModGate n).eval x = false ↔
      ¬(weightOn S x ≡ t.val [MOD 2]) ∨ ¬(weightOn S x ≡ t.val [MOD 3]) := by
  rw [Bool.eq_false_iff, ne_eq, mod6_eval_true_iff, not_and_or]

/-- **General mixed-modulus realization (proved): a forced `MOD₆` family (arbitrary `ρ`) is realizable iff some
Boolean `x` meets the per-gate conjunction (forced-true) / disjunction (forced-false) of the mod-2 and mod-3
conditions.** -/
theorem mod6_realizable_iff_general (ρ : Fin k → Option Bool)
    (S : Fin k → Finset (Fin n)) (t : Fin k → ZMod 6) :
    RealizableByInputRestriction ρ (fun j => (⟨6, S j, t j⟩ : ModGate n)) ↔
      ∃ x : Fin n → Bool, ∀ j,
        (ρ j = some true →
          (weightOn (S j) x ≡ (t j).val [MOD 2]) ∧ (weightOn (S j) x ≡ (t j).val [MOD 3])) ∧
        (ρ j = some false →
          ¬(weightOn (S j) x ≡ (t j).val [MOD 2]) ∨ ¬(weightOn (S j) x ≡ (t j).val [MOD 3])) := by
  rw [realizable_iff_achievable]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun j => ⟨fun h => (mod6_eval_true_iff (S j) (t j) x).mp (hx j true h),
                        fun h => (mod6_eval_false_iff (S j) (t j) x).mp (hx j false h)⟩⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, fun j b hjb => ?_⟩
    cases b with
    | true => exact (mod6_eval_true_iff (S j) (t j) x).mpr ((hx j).1 hjb)
    | false => exact (mod6_eval_false_iff (S j) (t j) x).mpr ((hx j).2 hjb)

end PallLean.Paper93.DeepMath.PathB.ACC0Mod6MixedGeneral

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6MixedGeneral.mod6_eval_false_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6MixedGeneral.mod6_realizable_iff_general
