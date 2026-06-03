import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestDecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReadOnceId

/-!
# Forward-scan invariant: the monotonicity backbone

The forward-scan decoder reconstructs `ρ` by scanning clauses in `cs` order, matching the *first
live clause* to the active clause at each step.  This works because the active clauses are processed
in **non-decreasing** `cs`-order — equivalently, once a clause is falsified it *stays* falsified
along the path, so the live frontier only advances.  That monotonicity is the structural backbone of
the invariant, and it holds for **general (non-falsify) steps** — not only the falsify path.

* `litFalse_fixVar_of_free` — a false literal stays false after fixing any *other* (free) variable to
  **any** bit: `litFalse σ m → σ v = none → litFalse (fixVar σ v b) m`.  (The false literal's variable
  is fixed, hence `≠ v`, so the step does not touch it.)
* `termFalsified_fixVar_of_free` — hence a falsified clause stays falsified: `termFalsified σ C →
  σ v = none → termFalsified (fixVar σ v b) C`.

These generalise the falsify-only `termFalsified_replayStep_of` to arbitrary steps, so along the
*deepest* (general-bit) branch the falsified set grows monotonically: the active clause never
revisits an earlier index, and the forward scan's clause order is consistent.

## What remains (honest)

This is the *ordering* half of the forward-scan invariant.  The *reconstruction-correctness* half —
that the first live clause in the restriction reconstructed so far is exactly the active clause at
that step, so freeing its labelled path-variables advances the reconstruction toward `ρ` — is the
genuine hard core of Håstad's switching-lemma decoding for general branches, and is **not** discharged
here and **not** faked.  The monotonicity proved here is a real, correct fragment of it.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **A false literal survives any step on another variable.**  If `m` is false under `σ` and `v`
is free, then `m` stays false after fixing `v` to any bit — the step cannot touch `m`'s (already
fixed) variable. -/
theorem litFalse_fixVar_of_free {σ : Fin n → Option Bool} {v : Fin n} {b : Bool}
    {m : Rung4Literal n} (hm : SwitchingCounting.litFalse σ m = true) (hv : σ v = none) :
    SwitchingCounting.litFalse (fixVar σ v b) m = true := by
  have hvar : litVar m ≠ v := fun he =>
    SwitchingCounting.litFalse_litVar_fixed hm (he.symm ▸ hv)
  have hval : (fixVar σ v b) (litVar m) = σ (litVar m) := by
    rw [fixVar, Function.update_of_ne hvar]
  rw [SwitchingCounting.litFalse_eq_of_litVar_val hval]
  exact hm

/-- **Falsified clauses stay falsified under any step (the forward-scan monotonicity).**  Generalises
`termFalsified_replayStep_of` from the falsify step to an arbitrary `fixVar` of a free variable, so
it applies along the deepest (general-bit) branch. -/
theorem termFalsified_fixVar_of_free {σ : Fin n → Option Bool} {v : Fin n} {b : Bool}
    {C : Clause n} (h : SwitchingCounting.termFalsified σ C = true) (hv : σ v = none) :
    SwitchingCounting.termFalsified (fixVar σ v b) C = true := by
  rw [SwitchingCounting.termFalsified, List.any_eq_true] at h ⊢
  obtain ⟨m, hm, hf⟩ := h
  exact ⟨m, hm, litFalse_fixVar_of_free hf hv⟩

/-- **Monotonicity at an active step.**  At a step with active literal `ℓ` (its variable free), every
clause already falsified stays falsified after either branch — so the falsified frontier only
advances, never revisiting an earlier active clause. -/
theorem termFalsified_active_step {cs : List (Clause n)} {σ : Fin n → Option Bool}
    {ℓ : Rung4Literal n} {C : Clause n} (h : SwitchingCounting.termFalsified σ C = true)
    (hatl : SwitchingCounting.activeTermLit cs σ = some ℓ) (b : Bool) :
    SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) C = true :=
  termFalsified_fixVar_of_free h (activeTermLit_var_free hatl)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.litFalse_fixVar_of_free
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termFalsified_fixVar_of_free
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termFalsified_active_step
