import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStable2

/-!
# `find?`-advance: the active clause advances past an exhausted clause

**STATUS: REAL.  THE GENUINE NEW CONTENT FOR MULTI-CLAUSE BOUNDARY RECOVERY.**

Companion to `find?_stable`.  When the found element is removed from the predicate
(here: the active clause is exhausted by a boundary step) and the discarded prefix
stays discarded, `find?` advances to the suffix strictly after it:

* `find?_advance_append`: `(pre ++ C :: post).find? p = post.find? p` when `p` is false
  on `pre` and on `C`;
* `find?_some_decompose`: `find? p l = some C` exhibits `l = pre ++ C :: post` with `p`
  false on `pre`;
* `activeClause_actStep_advance`: at a length-1 boundary the active clause advances —
  `activeClause cs (actStep cs σ)` is the active clause computed over the suffix of
  `cs` strictly after the exhausted clause `C`.

This is the `cs`-pointer advance the boundary decoder needs: the exhausted clause and
everything before it drop out, and the new active clause lives in the remaining suffix.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **`find?`-advance.**  If `p` is false on `pre` and on `C`, `find?` skips them. -/
theorem find?_advance_append {α : Type*} {p : α → Bool} {pre post : List α} {C : α}
    (hpre : ∀ x ∈ pre, p x = false) (hC : p C = false) :
    (pre ++ C :: post).find? p = post.find? p := by
  induction pre with
  | nil => simp [List.find?_cons, hC]
  | cons a pre ih =>
    have ha : p a = false := hpre a (List.mem_cons.mpr (Or.inl rfl))
    simp only [List.cons_append, List.find?_cons, ha]
    exact ih (fun x hx => hpre x (List.mem_cons.mpr (Or.inr hx)))

/-- **`find?` decomposition.**  A found element splits the list, with `p` false on the
prefix. -/
theorem find?_some_decompose {α : Type*} {p : α → Bool} {l : List α} {C : α}
    (h : l.find? p = some C) :
    ∃ pre post, l = pre ++ C :: post ∧ (∀ x ∈ pre, p x = false) ∧ p C = true := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.find?_cons] at h
    cases hpa : p a with
    | true =>
      simp only [hpa] at h
      obtain rfl : a = C := by simpa using h
      exact ⟨[], t, by simp, by simp, hpa⟩
    | false =>
      simp only [hpa] at h
      obtain ⟨pre, post, hl, hpre, hC⟩ := ih h
      refine ⟨a :: pre, post, by rw [hl]; rfl, ?_, hC⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hpa
      · exact hpre x hx

/-- The predicate defining the active clause. -/
private def acP (σ : Restriction n) (C : Clause n) : Bool :=
  !clauseSatisfied σ C && decide (0 < (freeLits σ C).length)

/-- **Active-clause advance at a boundary.**  When the active clause `C` has exactly one
free literal, the step exhausts it and the active clause advances: it is the active
clause computed over the part of `cs` strictly after `C`. -/
theorem activeClause_actStep_advance {cs : List (Clause n)} {σ : Restriction n}
    {C : Clause n} (hC : activeClause cs σ = some C) (hlen : (freeLits σ C).length = 1) :
    ∃ pre post, cs = pre ++ C :: post ∧
      activeClause cs (actStep cs σ) = post.find? (acP (actStep cs σ)) := by
  obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp (activeLit_isSome hC)
  have hstep : actStep cs σ = falFix σ ℓ := by rw [actStep, hℓ]
  have hℓfree : Depth3.litFree σ ℓ = true := activeLit_free hℓ
  -- `C` is exhausted after the step
  have hexh : freeLits (actStep cs σ) C = [] := freeLits_actStep_eq_nil_of_length_one hC hlen
  -- decompose `cs` at `C`
  obtain ⟨pre, post, hcs, hpre, _⟩ := find?_some_decompose hC
  refine ⟨pre, post, hcs, ?_⟩
  -- make the stepped restriction opaque so rewriting `cs` only hits the searched list
  set τ := actStep cs σ with hτ
  show cs.find? (acP τ) = post.find? (acP τ)
  rw [hcs]
  refine find?_advance_append ?_ ?_
  · -- discarded prefix stays discarded
    intro x hx
    have hpx : acP σ x = false := hpre x hx
    rw [hstep]
    by_cases hsat : clauseSatisfied σ x = true
    · have : clauseSatisfied (falFix σ ℓ) x = true := clauseSatisfied_mono_falFix x hℓfree hsat
      simp [acP, this]
    · have hns : clauseSatisfied σ x = false := by simpa using hsat
      have hempty : freeLits σ x = [] := by
        rw [acP, hns] at hpx
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not] at hpx
        rw [List.length_pos_iff_ne_nil, not_not] at hpx
        exact hpx
      simp [acP, freeLits_falFix_eq_nil hempty]
  · -- `C` itself is exhausted
    rw [acP, hexh]; simp

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.find?_advance_append
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeClause_actStep_advance
