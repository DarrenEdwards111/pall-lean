import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ToBoolSyntax
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone

/-!
# Bridge (Layer4 discharge) — the `MOD_q` residue-indicator lower bound, in the `ACC0Circuit` model (proved)

Discharging the tree's `Layer4.mod_q_indicators_false` (a `BoolCircuitSyntax` Razborov–Smolensky bound) into *this*
development's `ACC0Circuit` model, via the eval/AC0p-preserving translation `toBoolSyntax` (Brick model translation).  The
result: **no family of `AC⁰[p]` `ACC0Circuit`s can compute all `q` residue indicators `[weight ≡ j mod q]` with bounded
depth and subcircuit count** (for `q ∤ p`, `p,q` prime) — the genuine RS family lower bound, now available natively in the
`ACC0Circuit` framework.

The discharge takes the family as the refuted hypothesis (so no residue-family *construction* is needed), translates each
member with `toBoolSyntax` (preserving eval and `IsAC0pSyntax`), and applies `Layer4.mod_q_indicators_false`.

## What is proved (clean axioms — inherits Layer4's)

* **`modq_indicators_false_acc0`** (PROVED) — for `p,q` prime, `q ∤ p`, no family `C : ℕ → ACC0Circuit (2m+1)` of `AC⁰[p]`
  circuits computes the `q` residue indicators with `(p−1,t,d)`-bounded depth/size and the RS window — i.e. `False`.

## Honest scope

This is the `MOD_q` **residue-family** lower bound (matching `Layer4`'s shape) brought into the `ACC0Circuit` model.  It does
**not** by itself give a *single* `MOD_q ∉ AC⁰[p]` for all `n`: that needs the residue-family *construction* (build all `q`
indicators from one), a separate intricate step — **not** done here and **not** faked.  (The single-`MOD_q` separation is
already proved unconditionally for `MOD_2` all `n`, and `MOD_q` infinitely many `n`, by the in-framework degree argument.)
The size/depth bounds are stated on the `toBoolSyntax` translation (the natural resource measures).  Williams cash-out still
open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Layer4Discharge

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax (toBoolSyntax toBoolSyntax_eval toBoolSyntax_isAC0p)

open Classical in
/-- **The `MOD_q` residue-indicator family lower bound, in the `ACC0Circuit` model (PROVED).**  Discharges
`Layer4.mod_q_indicators_false` via the model translation. -/
theorem modq_indicators_false_acc0 (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m t d : ℕ} (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t)
    (C : ℕ → ACC0Circuit (2 * m + 1))
    (hmod : ∀ j ∈ Finset.range q, ModpOnly p (C j))
    (hind : ∀ j ∈ Finset.range q, ∀ x : Fin (2 * m + 1) → Bool,
      ACC0CircuitModel.eval (C j) x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = j))
    (hsize : ∀ j ∈ Finset.range q,
      4 * q * (PallLean.Paper93.DeepMath.PathB.Layer3.subcircuits (toBoolSyntax (C j))).toFinset.card ≤ p ^ t)
    (hdepth : ∀ j ∈ Finset.range q, BoolCircuitSyntax.depth (toBoolSyntax (C j)) ≤ d)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3) : False := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  refine PallLean.Paper93.DeepMath.PathB.Layer4.mod_q_indicators_false p q hpq ht1 hpt1
    (fun j => toBoolSyntax (C j)) ?_ ?_ hsize hdepth hwindow
  · intro j hj x
    rw [toBoolSyntax_eval p (C j) x (hmod j hj)]
    exact hind j hj x
  · intro j hj
    exact toBoolSyntax_isAC0p p (C j) (hmod j hj)

/-!
**The Layer4 discharge, proved.**  The `BoolCircuitSyntax` RS family bound (`Layer4.mod_q_indicators_false`) now holds in the
`ACC0Circuit` model via the eval/AC0p-preserving translation: no `AC⁰[p]` `ACC0Circuit` family computes all `q` residue
indicators within the RS resource window.  Remaining (open, not faked): the single-`MOD_q` residue-family *construction*, and
the Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0Layer4Discharge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Layer4Discharge.modq_indicators_false_acc0
