import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pApprox

/-!
# Layer 3 — probabilistic averaging (first moment) for the OR approximator

The agreement bounds so far are *per input over random forms* (`orApprox_disagree_count`: a fixed nonzero
input errs on a `p^{-t}` fraction of form tuples).  To feed the dimension argument we need the dual: a
*single* form choice that errs on few **inputs**.  This is the first-moment / averaging step:

* `exists_card_mul_le_sum` — the min-≤-mean principle: over a finite nonempty index set some element is
  at most the average.
* `exists_form_few_errors` — instantiated for one OR gate (via Fubini + `orApprox_disagree_count`):
  there is a form tuple `R` whose number of erring inputs `E` satisfies `(p^m)^t · E ≤ 2^m · (p^{m-1})^t`,
  i.e. `E ≤ 2^m · p^{-t}` — a `p^{-t}` *input*-error rate.

No lower bound; far below P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open MvPolynomial Finset

/-- **First-moment principle.**  Over a finite nonempty index set, some element's value is at most the
average: `s.card * f ω ≤ ∑ f` for some `ω ∈ s` (the minimiser). -/
theorem exists_card_mul_le_sum {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (f : Ω → ℕ) :
    ∃ ω ∈ s, s.card * f ω ≤ ∑ ω' ∈ s, f ω' := by
  obtain ⟨ω₀, hω₀, hmin⟩ := s.exists_min_image f hs
  refine ⟨ω₀, hω₀, ?_⟩
  calc s.card * f ω₀ = ∑ _ω ∈ s, f ω₀ := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ ω' ∈ s, f ω' := Finset.sum_le_sum (fun ω' hω' => hmin ω' hω')

/-- **Per-input bad-form count is `≤ (p^{m-1})^t`** (with equality for nonzero inputs;
the all-`false` input never errs). -/
theorem orApprox_badForm_card_le (p : ℕ) [Fact p.Prime] {m t : ℕ} (x : Fin m → Bool) :
    (univ.filter (fun R : Fin t → Fin m → ZMod p =>
        eval (fun i => boolToZMod p (x i)) (orApprox p R)
          ≠ boolToZMod p (decide (∃ i, x i = true)))).card ≤ (p ^ (m - 1)) ^ t := by
  classical
  by_cases hx : ∃ i, x i = true
  · have hc1 : boolToZMod p (decide (∃ i, x i = true)) = 1 := by
      rw [show decide (∃ i, x i = true) = true by simp [hx], boolToZMod_true]
    rw [show (univ.filter (fun R : Fin t → Fin m → ZMod p =>
        eval (fun i => boolToZMod p (x i)) (orApprox p R)
          ≠ boolToZMod p (decide (∃ i, x i = true))))
        = univ.filter (fun R : Fin t → Fin m → ZMod p =>
            eval (fun i => boolToZMod p (x i)) (orApprox p R) ≠ 1) from by
        apply Finset.filter_congr; intro R _; rw [hc1]]
    exact le_of_eq (orApprox_disagree_count p x hx)
  · have hxf : x = fun _ => false := by
      funext i; cases hxi : x i
      · rfl
      · exact absurd ⟨i, hxi⟩ hx
    have hempty : (univ.filter (fun R : Fin t → Fin m → ZMod p =>
        eval (fun i => boolToZMod p (x i)) (orApprox p R)
          ≠ boolToZMod p (decide (∃ i, x i = true)))) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro R _
      subst hxf
      rw [orApprox_eval_allFalse]
      simp
    rw [hempty]; simp

/-- **Averaging for one OR gate.**  There is a form tuple `R` whose number of erring inputs `E`
satisfies `(p^m)^t · E ≤ 2^m · (p^{m-1})^t` — input-error rate `≤ 2^m · p^{-t}`. -/
theorem exists_form_few_errors (p : ℕ) [Fact p.Prime] {m t : ℕ} :
    ∃ R : Fin t → Fin m → ZMod p,
      (p ^ m) ^ t * (univ.filter (fun x : Fin m → Bool =>
          eval (fun i => boolToZMod p (x i)) (orApprox p R)
            ≠ boolToZMod p (decide (∃ i, x i = true)))).card
        ≤ 2 ^ m * (p ^ (m - 1)) ^ t := by
  classical
  set f : (Fin t → Fin m → ZMod p) → ℕ := fun R =>
    (univ.filter (fun x : Fin m → Bool =>
      eval (fun i => boolToZMod p (x i)) (orApprox p R)
        ≠ boolToZMod p (decide (∃ i, x i = true)))).card with hf
  have hsum : ∑ R, f R ≤ 2 ^ m * (p ^ (m - 1)) ^ t := by
    have hfub : ∑ R, f R
        = ∑ x : Fin m → Bool, (univ.filter (fun R : Fin t → Fin m → ZMod p =>
            eval (fun i => boolToZMod p (x i)) (orApprox p R)
              ≠ boolToZMod p (decide (∃ i, x i = true)))).card := by
      simp only [hf, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hfub]
    refine le_trans (Finset.sum_le_sum (fun x _ => orApprox_badForm_card_le p x)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      smul_eq_mul]
  obtain ⟨R₀, _, hR₀⟩ := exists_card_mul_le_sum univ univ_nonempty f
  refine ⟨R₀, ?_⟩
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
    Fintype.card_fin] at hR₀
  exact le_trans hR₀ hsum

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.exists_card_mul_le_sum
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orApprox_badForm_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.exists_form_few_errors
