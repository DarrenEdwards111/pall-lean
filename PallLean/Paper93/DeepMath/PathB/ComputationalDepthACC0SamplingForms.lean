import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SamplingExistence

/-!
# Instantiating the sampling existence to the parity forms (the quasipoly family exists)

`…ACC0SamplingExistence` proved the abstract union-bound existence; `…ACC0ProbabilisticBoost` proved the boosted
`t`-tuple form family is majority-correct at every input.  This file **plugs the boosted forms into the abstract
lemma**, closing the sampling gate concretely:

* inputs `X = Fin m → Bool` (so `|X| = 2^m`);
* predictor pool `P = Fin t → Finset (Fin m)` (the boosted `t`-tuples of parity forms);
* good set `boostGood v ⊆ P` = the tuples whose boosted `OR`-prediction is correct on `v`.

For `t ≥ 2` the per-input density is `≥ 3/4` (`boost_correct_card`: a `1 - 2^{-t}` fraction on nonzero `v`; *all*
tuples on the zero input).  So once `2^m·(7/8)^r < 1` — i.e. `r = O(m)` — the abstract lemma yields a *single* sample
of `r` boosted forms that is **majority-correct at every one of the `2^m` inputs**: `r = O(m) = polylog`-many forms
suffice.  This is exactly the quasipolynomial majority-correct family the socket `ApproxToExactSymmetricDecode`
needs — its open clause, now discharged for the parity-form construction (modulo the basis bridge).

## What is proved (clean axioms, no `sorry`)

* `boostCorrect` / `boostGood` — a boosted `t`-tuple is *correct on `v`* iff its `OR`-prediction matches `OR(v)`; the
  good set is the tuples correct on `v`.
* `boostGood_card_ge` — every input's good set has density `≥ 3/4`: `3·|P| ≤ 4·|boostGood v|` (for `t ≥ 2`).
* `exists_quasipoly_majority_correct_forms` — for `t ≥ 2` and `2^m·(7/8)^r < 1`, there is a sample
  `σ : Fin r → (Fin t → Finset (Fin m))` majority-correct at every input: `∀ v, r < 2·#{i | σ i ∈ boostGood v}`.

## Honest scope

This discharges the **sampling gate** for the parity-form construction: a quasipolynomial (`r = O(m)`) family of
boosted parity forms majority-correct everywhere genuinely exists.  Combined with the majority decoder
(`…ACC0ApproxToExactDecode`), the boosted forms exactly compute `OR` via a symmetric count.  The **one remaining
piece** of the Beigel–Tarui front half is the *basis bridge*: these forms are low *polynomial* (`F₂`) degree but high
*monomial-`AND`* degree, while the socket's `IsLowDegreeGate` is monomial-`AND`-based — the `AND`/`XOR` RS
translation.  That, the last step, is **Wall 1**, not done here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SamplingForms

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost
open PallLean.Paper93.DeepMath.PathB.ACC0SamplingExistence

variable {m t : ℕ}

/-- A boosted `t`-tuple `σ` is **correct on `v`** iff its `OR`-prediction (`∃ k, L_{σ k}(v) = 1`) matches the true
`OR(v)` (`∃ i, v i = true`). -/
def boostCorrect (v : Fin m → Bool) (σ : Fin t → Finset (Fin m)) : Prop :=
  (∃ k, pv v (σ k) = 1) ↔ (∃ i, v i = true)

/-- The **good set** at input `v`: the boosted tuples correct on `v`. -/
noncomputable def boostGood (v : Fin m → Bool) : Finset (Fin t → Finset (Fin m)) :=
  Finset.univ.filter (fun σ => boostCorrect v σ)

/-- On an all-`0` input the linear form vanishes for every subset (proved). -/
theorem pv_all_false {v : Fin m → Bool} (hv : ∀ i, v i = false) (S : Finset (Fin m)) :
    pv v S = 0 := by
  simp only [pv]
  exact Finset.sum_eq_zero (fun i _ => by simp [hv i])

/-- The pool has `(2^m)^t` boosted tuples (proved). -/
theorem card_pool : Fintype.card (Fin t → Finset (Fin m)) = (2 ^ m) ^ t := by
  rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin]

/-- **Every input's good set has density `≥ 3/4` (proved): `3·|P| ≤ 4·|boostGood v|`, for `t ≥ 2`.** -/
theorem boostGood_card_ge (ht : 2 ≤ t) (v : Fin m → Bool) :
    3 * Fintype.card (Fin t → Finset (Fin m)) ≤ 4 * (boostGood (t := t) v).card := by
  by_cases hv : ∃ i, v i = true
  · -- nonzero input: good set = the firing tuples, density `1 - 2^{-t} ≥ 3/4`
    obtain ⟨j, hj⟩ := hv
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le j.val) j.is_lt
    have hgv : boostGood v
        = Finset.univ.filter (fun σ : Fin t → Finset (Fin m) => ∃ k, pv v (σ k) = 1) := by
      rw [boostGood]
      apply Finset.filter_congr
      intro σ _
      unfold boostCorrect
      constructor
      · intro h; exact h.mpr ⟨j, hj⟩
      · intro hk; exact ⟨fun _ => ⟨j, hj⟩, fun _ => hk⟩
    have hgvcard : (boostGood (t := t) v).card = (2 ^ m) ^ t - (2 ^ (m - 1)) ^ t := by
      rw [hgv]; exact boost_correct_card t v j hj
    rw [card_pool, hgvcard]
    have hsucc : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hm]
      rw [pow_succ, Nat.pred_eq_sub_one]; ring
    have h4WN : 4 * (2 ^ (m - 1)) ^ t ≤ (2 ^ m) ^ t := by
      have hNW : (2 ^ m) ^ t = 2 ^ t * (2 ^ (m - 1)) ^ t := by rw [hsucc, mul_pow]
      have h2t : (4 : ℕ) ≤ 2 ^ t := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
      calc 4 * (2 ^ (m - 1)) ^ t ≤ 2 ^ t * (2 ^ (m - 1)) ^ t := by gcongr
        _ = (2 ^ m) ^ t := hNW.symm
    have hWN : (2 ^ (m - 1)) ^ t ≤ (2 ^ m) ^ t :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le m 1)) t
    omega
  · -- zero input: every tuple is correct, density `1`
    simp only [not_exists, Bool.not_eq_true] at hv
    have hgv : boostGood v = (Finset.univ : Finset (Fin t → Finset (Fin m))) := by
      rw [boostGood, Finset.filter_true_of_mem]
      intro σ _
      unfold boostCorrect
      constructor
      · rintro ⟨k, hk⟩; rw [pv_all_false hv] at hk; exact absurd hk (by decide)
      · rintro ⟨i, hi⟩; rw [hv i] at hi; exact absurd hi (by decide)
    rw [hgv, Finset.card_univ]
    omega

/-- **The quasipolynomial majority-correct parity-form family exists (proved).**  For `t ≥ 2` and
`2^m·(7/8)^r < 1` (so `r = O(m)`), a single sample of `r` boosted parity-form tuples is majority-correct at every one
of the `2^m` inputs.  This is the socket's open clause, discharged for the parity-form construction. -/
theorem exists_quasipoly_majority_correct_forms (ht : 2 ≤ t) (r : ℕ)
    (hbound : (2 ^ m : ℝ) * (7 / 8) ^ r < 1) :
    ∃ σ : Fin r → (Fin t → Finset (Fin m)),
      ∀ v : Fin m → Bool, r < 2 * (Finset.univ.filter (fun i => σ i ∈ boostGood v)).card := by
  have hP : 0 < Fintype.card (Fin t → Finset (Fin m)) := by rw [card_pool]; positivity
  have hbound' : (Fintype.card (Fin m → Bool) : ℝ) * (7 / 8) ^ r < 1 := by
    rw [show Fintype.card (Fin m → Bool) = 2 ^ m from by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]]
    exact_mod_cast hbound
  exact exists_sample_majority_correct_all r boostGood (boostGood_card_ge ht) hP hbound'

end PallLean.Paper93.DeepMath.PathB.ACC0SamplingForms

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SamplingForms.boostGood_card_ge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SamplingForms.exists_quasipoly_majority_correct_forms
