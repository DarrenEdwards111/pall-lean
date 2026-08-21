import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCounting
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
# Restriction-class cardinalities (toward discharging the switching parameter gate)

**STATUS: REAL FOUNDATIONAL COUNTING.  THE BINOMIAL-RATIO BALANCE IS THE GATE.**

The switching parameter gate `|Short| · ((2^w)^m)^numTerms < |U|` is discharged by
the cardinalities of restriction classes.  This file proves the two foundational
counts:

* `card_restrictions` — there are `3^N` restrictions on `Fin N`;
* `card_freeVars_eq` — exactly `2^(N - |S|)` restrictions have free set exactly `S`
  (the free coordinates are forced `none`, each fixed coordinate has two choices).

The module now also proves the per-star count
`|{stars = t}| = C(N,t)·2^(N-t)`.  The ratio inequality choosing parameters so that
the bad class is outnumbered remains the quantitative gate.
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

/-- A restriction with exactly `K` stars is equivalently its `K`-element free set together with a
restriction in the corresponding exact-free-set fiber. -/
def starsFiberEquiv (K : ℕ) :
    {ρ : Restriction N // stars ρ = K} ≃
      Σ S : {S : Finset (Fin N) // S.card = K},
        {ρ : Restriction N // freeVars ρ = S.1} where
  toFun ρ := ⟨⟨freeVars ρ.1, ρ.2⟩, ⟨ρ.1, rfl⟩⟩
  invFun z := ⟨z.2.1, by rw [stars, z.2.2, z.1.2]⟩
  left_inv ρ := rfl
  right_inv z := by
    rcases z with ⟨⟨S, hS⟩, ⟨ρ, hρ⟩⟩
    change freeVars ρ = S at hρ
    subst S
    rfl

/-- **Exact `K`-star shell cardinality.**  Choose the `K` free coordinates, then choose one Boolean
value for each of the other `N-K` coordinates. -/
theorem card_stars_eq (N K : ℕ) :
    (Finset.univ.filter (fun ρ : Restriction N => stars ρ = K)).card =
      Nat.choose N K * 2 ^ (N - K) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (starsFiberEquiv (N := N) K),
    Fintype.card_sigma]
  calc
    ∑ S : {S : Finset (Fin N) // S.card = K},
        Fintype.card {ρ : Restriction N // freeVars ρ = S.1} =
        ∑ _S : {S : Finset (Fin N) // S.card = K}, 2 ^ (N - K) := by
          apply Finset.sum_congr rfl
          intro S _
          have hfiber := card_freeVars_eq (N := N) S.1
          rw [← Fintype.card_subtype] at hfiber
          rw [hfiber, S.2]
    _ = Fintype.card {S : Finset (Fin N) // S.card = K} * 2 ^ (N - K) := by simp
    _ = Nat.choose N K * 2 ^ (N - K) := by rw [Fintype.card_finset_len, Fintype.card_fin]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_restrictions
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_freeVars_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_stars_eq
