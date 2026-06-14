import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModQFeasibility

/-!
# Mixed moduli: `MOD₆ = MOD₂ ∧ MOD₃` realization via CRT

The composite-modulus case combines the parity (F₂, linear/rank) story with the `MOD₃` (0/1-feasibility) story.  By
CRT (`Nat.modEq_and_modEq_iff_modEq_mul`, `2 ⊥ 3`), a `MOD₆` gate fires iff the support count is `≡ target` **both**
mod 2 and mod 3:

```
(MOD₆ S t).eval x = true  ⟺  count_S(x) ≡ t.val [MOD 2]  ∧  count_S(x) ≡ t.val [MOD 3]
```

So forcing a `MOD₆` family decomposes into a **mod-2 system** (linear over F₂ — the rank story) **and** a **mod-3
system** (0/1-feasibility) imposed on the *same* `x`.  `mod6_realizable_iff_mixed` characterizes realizability as the
simultaneous solvability of both — the honest "mixed" condition: neither the F₂ rank nor the F₃ feasibility alone
suffices, because the two constraint systems are coupled through the shared Boolean assignment.

## What is proved (clean axioms, no `sorry`)

* `mod6_eval_true_iff` — the CRT split: a `MOD₆` gate fires iff count `≡ t.val` mod 2 and mod 3.
* `mod6_realizable_iff_mixed` — a forced-true `MOD₆` family is realizable iff `∃ x` solving the mod-2 **and** mod-3
  count systems simultaneously.

## Honest scope

The mod-2 component is linear (plugs into the `2^rank` story); the mod-3 component is 0/1-feasibility (no rank, by
`modq_residue_image_not_subspace`).  Their conjunction is coupled through `x`, so the combined realizability is
genuinely the intersection of an F₂-affine condition and an F₃-feasibility region — no product/closed-form shortcut.
This is the forced-true case (cleanest); a fully general `ρ` (mixing forced true/false) makes the per-gate condition a
conjunction/disjunction of the two CRT parts.  Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod6Mixed

open scoped Classical
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0OracleRestrictionRealization
open PallLean.Paper93.DeepMath.PathB.ACC0ParityConstraintRealization
open PallLean.Paper93.DeepMath.PathB.ACC0ModQFeasibility

variable {n k : ℕ}

/-- **The CRT split of a `MOD₆` gate (proved): it fires iff the count is `≡ target` mod 2 and mod 3.** -/
theorem mod6_eval_true_iff (S : Finset (Fin n)) (t : ZMod 6) (x : Fin n → Bool) :
    (⟨6, S, t⟩ : ModGate n).eval x = true ↔
      (weightOn S x ≡ t.val [MOD 2]) ∧ (weightOn S x ≡ t.val [MOD 3]) := by
  rw [modGate_eval_true_iff]
  show modQStatOn S 6 x = t ↔ _
  unfold modQStatOn
  conv_lhs => rw [← ZMod.natCast_rightInverse t, ZMod.natCast_eq_natCast_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 2 3 by decide)).symm

/-- **Mixed-modulus realization (proved): a forced-true `MOD₆` family is realizable iff some Boolean `x` solves the
mod-2 system AND the mod-3 system simultaneously.**  The mod-2 part is linear (rank); the mod-3 part is
0/1-feasibility; both are imposed on the shared `x`. -/
theorem mod6_realizable_iff_mixed (S : Fin k → Finset (Fin n)) (t : Fin k → ZMod 6) :
    RealizableByInputRestriction (fun _ => some true) (fun j => (⟨6, S j, t j⟩ : ModGate n)) ↔
      ∃ x : Fin n → Bool, ∀ j,
        (weightOn (S j) x ≡ (t j).val [MOD 2]) ∧ (weightOn (S j) x ≡ (t j).val [MOD 3]) := by
  rw [realizable_iff_achievable]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun j => (mod6_eval_true_iff (S j) (t j) x).mp (hx j true rfl)⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, fun j b hjb => ?_⟩
    obtain rfl : b = true := (Option.some.inj hjb).symm
    exact (mod6_eval_true_iff (S j) (t j) x).mpr (hx j)

end PallLean.Paper93.DeepMath.PathB.ACC0Mod6Mixed

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6Mixed.mod6_eval_true_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod6Mixed.mod6_realizable_iff_mixed
