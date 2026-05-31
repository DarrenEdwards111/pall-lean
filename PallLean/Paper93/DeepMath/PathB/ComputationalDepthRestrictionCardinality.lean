import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Restriction-class cardinalities (toward discharging the switching parameter gate)

**STATUS: REAL FOUNDATIONAL COUNTING.  THE BINOMIAL-RATIO BALANCE IS THE GATE.**

The switching parameter gate `|Short| · ((2^w)^m)^numTerms < |U|` is discharged by
the cardinalities of restriction classes.  This file proves the two foundational
counts:

* `card_restrictions` — there are `3^N` restrictions on `Fin N`;
* `card_freeVars_eq` — exactly `2^(N - |S|)` restrictions have free set exactly `S`
  (the free coordinates are forced `none`, each fixed coordinate has two choices).

From these the per-star count `|{stars = t}| = C(N,t)·2^(N-t)` and then the
ratio inequality (choosing the restriction parameter so that the bad class is
outnumbered) follow — that ratio/parameter balance is the remaining quantitative
gate, not addressed here.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

variable {N : ℕ}

/-- **There are `3^N` restrictions.**  Each coordinate is `none`, `some true`, or
`some false`. -/
theorem card_restrictions : Fintype.card (Restriction N) = 3 ^ N := by
  show Fintype.card (Fin N → Option Bool) = 3 ^ N
  simp [Fintype.card_fun, Fintype.card_option, Fintype.card_bool, Fintype.card_fin]

/-- The restrictions with free set exactly `S` are in bijection with the Boolean
assignments to the *fixed* coordinates `Sᶜ`. -/
def freeVarsEquiv (S : Finset (Fin N)) :
    {ρ : Restriction N // freeVars ρ = S} ≃ ((Sᶜ : Finset (Fin N)) → Bool) where
  toFun ρ := fun i => (ρ.1 i.1).getD false
  invFun f := ⟨fun j => if h : j ∈ S then none else some (f ⟨j, Finset.mem_compl.mpr h⟩), by
    ext j
    rw [mem_freeVars]
    by_cases h : j ∈ S <;> simp [h]⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    apply Subtype.ext
    funext j
    by_cases h : j ∈ S
    · simp only [h, dif_pos]
      have : ρ j = none := mem_freeVars.mp (hρ ▸ h)
      exact this.symm
    · simp only [h, dif_neg, not_false_iff]
      have hne : ρ j ≠ none := by
        intro hc; exact h (hρ ▸ mem_freeVars.mpr hc)
      cases hr : ρ j with
      | none => exact absurd hr hne
      | some b => simp [hr]
  right_inv := by
    intro f
    funext i
    have h : i.1 ∉ S := Finset.mem_compl.mp i.2
    simp [h]

/-- **Exactly `2^(N - |S|)` restrictions have free set `S`.** -/
theorem card_freeVars_eq (S : Finset (Fin N)) :
    (Finset.univ.filter (fun ρ : Restriction N => freeVars ρ = S)).card = 2 ^ (N - S.card) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (freeVarsEquiv S), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_restrictions
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_freeVars_eq
