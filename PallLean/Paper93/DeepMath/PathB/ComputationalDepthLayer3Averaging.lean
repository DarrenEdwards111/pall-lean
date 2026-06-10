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

/-! ## Circuit-level averaging: combine per-gate bounds over a joint form space

To lift averaging from one gate to a whole circuit, the form space `Φ` is the *joint* choice over all
`s` gates, and the composed approximant errs at an input only where some gate does (`hsub`: composed bad
⊆ union of per-gate bads).  Summing the per-gate first-moment bounds gives a single joint form `ω` whose
total composed-error count is at most the average of the summed bounds. -/

/-- First moment over a sum of per-gate error functions: some `ω` has `card·(∑ᵢ gᵢ ω) ≤ ∑ᵢ Bᵢ`, given
each gate's column-sum bound `∑_ω gᵢ ω ≤ Bᵢ` (Fubini + `exists_card_mul_le_sum`). -/
theorem exists_le_sum_of_sum_le {Ω ι : Type*} (s : Finset Ω) (hs : s.Nonempty)
    (gates : Finset ι) (g : ι → Ω → ℕ) (B : ι → ℕ)
    (hB : ∀ i ∈ gates, ∑ ω ∈ s, g i ω ≤ B i) :
    ∃ ω ∈ s, s.card * (∑ i ∈ gates, g i ω) ≤ ∑ i ∈ gates, B i := by
  obtain ⟨ω, hω, hle⟩ := exists_card_mul_le_sum s hs (fun ω => ∑ i ∈ gates, g i ω)
  refine ⟨ω, hω, le_trans hle ?_⟩
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum hB

/-- **Circuit-level averaging.**  With `Φ` the joint form space, `gbad i ω` the inputs gate `i` errs on
under joint form `ω`, and `cbad ω` the composed approximant's error set contained in the union of the
per-gate ones (`hsub`), the per-gate first-moment bounds `∑_ω (gbad i ω).card ≤ Bᵢ` yield a *single*
joint form `ω` with `Φ.card · |cbad ω| ≤ ∑ᵢ Bᵢ` — total composed-error rate `≤ (∑ᵢ Bᵢ)/|Φ|`. -/
theorem exists_form_total_errors {Ω ι X : Type*} [DecidableEq X] (Φ : Finset Ω) (hΦ : Φ.Nonempty)
    (gates : Finset ι) (gbad : ι → Ω → Finset X) (cbad : Ω → Finset X) (B : ι → ℕ)
    (hsub : ∀ ω ∈ Φ, cbad ω ⊆ gates.biUnion (fun i => gbad i ω))
    (hB : ∀ i ∈ gates, ∑ ω ∈ Φ, (gbad i ω).card ≤ B i) :
    ∃ ω ∈ Φ, Φ.card * (cbad ω).card ≤ ∑ i ∈ gates, B i := by
  obtain ⟨ω, hω, hle⟩ :=
    exists_le_sum_of_sum_le Φ hΦ gates (fun i ω => (gbad i ω).card) B hB
  refine ⟨ω, hω, le_trans ?_ hle⟩
  exact Nat.mul_le_mul_left _
    (le_trans (Finset.card_le_card (hsub ω hω)) Finset.card_biUnion_le)

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.exists_card_mul_le_sum
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orApprox_badForm_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.exists_form_few_errors
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.exists_le_sum_of_sum_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.exists_form_total_errors
