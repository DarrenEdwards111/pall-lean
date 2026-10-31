import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatEncode

/-!
# Block-DT model, foundation 1: the kill operation (branch only)

The binary `canonicalDT` kills a term with one query, which is incompatible with the satisfying
encoding (which must set *all* of a term's free variables).  We re-found the switching count on a
**block** decision-tree model: each block queries *all* of the active term's free variables at once.

The block descent kills the active term by setting **all** its free variables to their **falsifying**
values; the satisfying encoding (`satExtendTerm`, already built) sets them to their satisfying values.
The two are duals.  This file builds the kill operation:

* `falsValue` — the value of a literal's variable that makes the literal *false*.
* `killTerm σ T` — set each free coordinate of `T` to its falsifying value (keep fixed coordinates).
* `killTerm_extends` — it extends `σ` (only fills free coordinates).
* `killTerm_falsifies` — if `T` has a free literal, `killTerm σ T` **falsifies** `T`.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The value of a literal's variable that makes the literal **false**. -/
def falsValue : Rung4Literal n → Bool
  | .pos _ => false
  | .neg _ => true

/-- **The kill operation.**  Keep `σ`'s fixed coordinates; fill each free coordinate of `T` with the
value that makes its literal false. -/
def killTerm (σ : Restriction n) (T : Clause n) : Restriction n :=
  fun v =>
    if σ v = none then
      (if (Rung4Literal.pos v) ∈ T.lits then some false
       else if (Rung4Literal.neg v) ∈ T.lits then some true else none)
    else σ v

/-- The kill operation extends `σ` (it only fills free coordinates). -/
theorem killTerm_extends (σ : Restriction n) (T : Clause n) :
    Extends σ (killTerm σ T) := by
  intro v b h
  simp only [killTerm, h, reduceCtorEq, if_false]

/-- The active literal's variable is free at the descent state. -/
private theorem head_free_kill {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) : σ (litVar ℓ) = none := by
  have hmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
  have hfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hmem).2
  rw [litFree_var] at hfree
  cases hx : σ (litVar ℓ) with
  | none => rfl
  | some _ => rw [hx] at hfree; simp at hfree

/-- The killing value of a free literal's variable makes that literal false. -/
private theorem killTerm_litFalse {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (hcons : Consistent T) (hmem : ℓ ∈ T.lits) (hfree : σ (litVar ℓ) = none) :
    SwitchingCounting.litFalse (killTerm σ T) ℓ = true := by
  cases ℓ with
  | pos v =>
    have hf : σ v = none := hfree
    simp [SwitchingCounting.litFalse, Depth3.litFixedVal, killTerm, hf, hmem]
  | neg v =>
    have hf : σ v = none := hfree
    have hpos : (Rung4Literal.pos v) ∉ T.lits := fun hp => hcons v ⟨hp, hmem⟩
    simp [SwitchingCounting.litFalse, Depth3.litFixedVal, killTerm, hf, hpos, hmem]

/-- **The kill operation falsifies a consistent term with a free literal.** -/
theorem killTerm_falsifies {σ : Restriction n} {T : Clause n} (hcons : Consistent T)
    (hfree : (SwitchingCounting.freeLits σ T).head?.isSome) :
    SwitchingCounting.termFalsified (killTerm σ T) T = true := by
  obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp hfree
  have hmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hℓ
  have hℓT : ℓ ∈ T.lits := (List.mem_filter.mp hmem).1
  have hℓfree : σ (litVar ℓ) = none := head_free_kill hℓ
  rw [SwitchingCounting.termFalsified, List.any_eq_true]
  exact ⟨ℓ, hℓT, killTerm_litFalse hcons hℓT hℓfree⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.killTerm_extends
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.killTerm_falsifies
