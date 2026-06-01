import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActivePath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStable

/-!
# Toward active-clause stability: `find?` stability + free-set shrinking

**STATUS: REAL.  REUSABLE LEMMAS FOR THE DECODER INVARIANT.**

Two building blocks for `activeClause_stable` (the decoder invariant that the
active clause does not move while it still has a free literal):

* `find?_stable`: if `find? p l = some C`, `p' C = true`, and `p'` is false wherever
  `p` is false, then `find? p' l = some C` — the active element is unchanged when the
  predicate is preserved on the discarded prefix and still holds on the target;
* `litFree_falFix_imp`: `falFix` shrinks the free set — a literal free after the step
  was free before — and `freeLits_falFix_subset` for the clause's free literals.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **`find?` stability.**  The found element is unchanged if the predicate stays
false on the discarded prefix and still holds on the target. -/
theorem find?_stable {α : Type*} {p p' : α → Bool} {l : List α} {C : α}
    (h : l.find? p = some C) (hp' : p' C = true)
    (hagree : ∀ x ∈ l, p x = false → p' x = false) : l.find? p' = some C := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.find?_cons] at h ⊢
    cases hpa : p a with
    | true =>
      simp only [hpa] at h
      obtain rfl : a = C := by simpa using h
      simp [hp']
    | false =>
      simp only [hpa] at h
      have hpa' : p' a = false := hagree a (List.mem_cons.mpr (Or.inl rfl)) hpa
      simp only [hpa']
      exact ih h (fun x hx hpx => hagree x (List.mem_cons.mpr (Or.inr hx)) hpx)

/-- `falFix` shrinks the free set: a literal free after the step was free before. -/
theorem litFree_falFix_imp {σ : Restriction n} {ℓ ℓ' : Rung4Literal n}
    (h : Depth3.litFree (falFix σ ℓ) ℓ' = true) : Depth3.litFree σ ℓ' = true := by
  by_cases hv : litVar ℓ' = litVar ℓ
  · rw [litFree_var, hv, falFix] at h
    simp [Function.update_self] at h
  · rw [litFree_var, falFix, Function.update_of_ne hv] at h
    rw [litFree_var]; exact h

/-- **The free set of a clause shrinks under a step.**  A literal of `C` free after
the step was free before — so `freeLits (falFix σ ℓ) C ⊆ freeLits σ C`.  In
particular, if `C` had no free literal, it still has none. -/
theorem freeLits_falFix_subset {σ : Restriction n} {ℓ : Rung4Literal n} {C : Clause n} :
    freeLits (falFix σ ℓ) C ⊆ freeLits σ C := by
  intro ℓ' h
  rw [freeLits, List.mem_filter] at h ⊢
  exact ⟨h.1, litFree_falFix_imp h.2⟩

/-- If a clause had no free literal, it still has none after a step. -/
theorem freeLits_falFix_eq_nil {σ : Restriction n} {ℓ : Rung4Literal n} {C : Clause n}
    (h : freeLits σ C = []) : freeLits (falFix σ ℓ) C = [] :=
  List.eq_nil_of_subset_nil (h ▸ freeLits_falFix_subset)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB
