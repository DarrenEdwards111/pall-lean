import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRelevanceLeafBound

/-!
# Restriction preserves relevance — tying the relevance base to the shrinkage schematic

`…RelevanceLeafBound` proved the non‑counting base `leaves F ≥ #{relevant variables}`.  `…AndreevShrinkageRoute`
proved the combination `H · D ≤ leaves` from a (cited) shrinkage factor `D` and a surviving‑complexity bound `H`.
This file connects them: it grounds the abstract `H` in the *relevance* of the **restricted** formula, with no
appeal to the deep Håstad theorem.

A restriction `ρ : Fin n → Option Bool` fixes some variables (`some b`) and leaves others free (`none`).

## What is proved (clean axioms, no `sorry`)

* `eval_restrict` — the restricted formula computes the restricted function: `eval (restrict F ρ) x =
  eval F (override x ρ)`.
* `restrict_leaves_le` — **restriction does not increase leaves**: `leaves (restrict F ρ) ≤ leaves F`.
* `original_leaves_ge_surviving_relevance` — combining the relevance base with the previous: the original formula
  has `≥` the **surviving relevance** of the restricted function: `#{relevant vars of eval (restrict F ρ)} ≤
  leaves F`.
* `shrinkage_plus_surviving_relevance` — **the tight schematic**: given a shrinkage factor `D`
  (`leaves (restrict F ρ) · D ≤ leaves F`, the *cited* Håstad input) and surviving relevance `r`, the original has
  `r · D ≤ leaves F`.  Here `r` is genuine surviving *relevance* (structurally grounded), not an abstract
  parameter.

## How this completes the schematic

The Andreev lower bound is exactly `shrinkage_plus_surviving_relevance` with: `D` = the shrinkage factor `≈ p^{-2}`
(Håstad `Γ=2`, *cited*, the only non‑elementary input); `r` = the relevance surviving a good restriction (for
Andreev's lookup, the `≈ 2^k` table bits stay relevant).  Everything *except* the deep shrinkage factor is now
proved from the formula's structure and the function's sensitivity — no function counting, no reproof of the
random‑restriction theorem.  The remaining step beyond this is proving the shrinkage theorem itself, a separate
project; this file connects the proved relevance base to it as tightly as possible without it.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictionSensitivity

open Classical
open PallLean.Paper93.DeepMath.PathB.RelevanceLeafBound
open PallLean.Paper93.DeepMath.PathB.AndreevShrinkageRoute

variable {n : ℕ}

/-- Apply a restriction `ρ` (fix `some b`, keep `none` free) to a formula. -/
def restrict : Formula n → (Fin n → Option Bool) → Formula n
  | .var i, ρ => match ρ i with
                  | none => .var i
                  | some true => .tru
                  | some false => .fls
  | .tru, _ => .tru
  | .fls, _ => .fls
  | .neg f, ρ => .neg (restrict f ρ)
  | .conj f g, ρ => .conj (restrict f ρ) (restrict g ρ)
  | .disj f g, ρ => .disj (restrict f ρ) (restrict g ρ)

/-- The full assignment obtained by overriding `x` with the fixed values of `ρ`. -/
def override (x : Fin n → Bool) (ρ : Fin n → Option Bool) : Fin n → Bool :=
  fun i => (ρ i).getD (x i)

/-- **Restriction does not increase leaves (proved).** -/
theorem restrict_leaves_le (F : Formula n) (ρ : Fin n → Option Bool) :
    leaves (restrict F ρ) ≤ leaves F := by
  induction F with
  | var i =>
      cases h : ρ i with
      | none => simp [restrict, leaves, h]
      | some b => cases b <;> simp [restrict, leaves, h]
  | tru => simp [restrict, leaves]
  | fls => simp [restrict, leaves]
  | neg f ih => simpa [restrict, leaves] using ih
  | conj f g ihf ihg => simp only [restrict, leaves]; exact Nat.add_le_add ihf ihg
  | disj f g ihf ihg => simp only [restrict, leaves]; exact Nat.add_le_add ihf ihg

/-- **The restricted formula computes the restricted function (proved).** -/
theorem eval_restrict (F : Formula n) (ρ : Fin n → Option Bool) (x : Fin n → Bool) :
    eval (restrict F ρ) x = eval F (override x ρ) := by
  induction F with
  | var i =>
      cases h : ρ i with
      | none => simp [restrict, eval, override, h]
      | some b => cases b <;> simp [restrict, eval, override, h]
  | tru => rfl
  | fls => rfl
  | neg f ih => simp only [restrict, eval]; rw [ih]
  | conj f g ihf ihg => simp only [restrict, eval]; rw [ihf, ihg]
  | disj f g ihf ihg => simp only [restrict, eval]; rw [ihf, ihg]

/-- The surviving relevance is bounded by the restricted formula's leaves (the relevance base, applied to the
restricted formula). -/
theorem surviving_relevance_le_restricted_leaves (F : Formula n) (ρ : Fin n → Option Bool) :
    (Finset.univ.filter (fun i => relevantVar (eval (restrict F ρ)) i)).card ≤ leaves (restrict F ρ) :=
  leaves_ge_relevant_card (restrict F ρ)

/-- **The original formula has at least the surviving relevance in leaves (proved).**  Combining the relevance
base on the restricted formula with `restrict_leaves_le`. -/
theorem original_leaves_ge_surviving_relevance (F : Formula n) (ρ : Fin n → Option Bool) :
    (Finset.univ.filter (fun i => relevantVar (eval (restrict F ρ)) i)).card ≤ leaves F :=
  le_trans (surviving_relevance_le_restricted_leaves F ρ) (restrict_leaves_le F ρ)

/-- **The tight schematic (proved): shrinkage × surviving relevance ⇒ original leaf bound.**  Given a shrinkage
factor `D` (`leaves (restrict F ρ) · D ≤ leaves F` — the cited Håstad input) and surviving relevance `r`, the
original formula has `r · D ≤ leaves F`.  This is the Andreev lower bound with the surviving complexity grounded
in genuine *relevance*. -/
theorem shrinkage_plus_surviving_relevance (F : Formula n) (ρ : Fin n → Option Bool) (D r : ℕ)
    (shrinkage : leaves (restrict F ρ) * D ≤ leaves F)
    (hsurv : r ≤ (Finset.univ.filter (fun i => relevantVar (eval (restrict F ρ)) i)).card) :
    r * D ≤ leaves F :=
  andreev_leaf_lower_bound shrinkage (le_trans hsurv (surviving_relevance_le_restricted_leaves F ρ))

end PallLean.Paper93.DeepMath.PathB.RestrictionSensitivity

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionSensitivity.restrict_leaves_le
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionSensitivity.eval_restrict
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionSensitivity.shrinkage_plus_surviving_relevance
