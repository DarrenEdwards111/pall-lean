import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ProbabilisticForm

/-!
# Degree-`t` boosting: the full `t`-tuple form family is majority-correct everywhere

`…ACC0ProbabilisticForm` proved the atom: a single random `F₂` linear form is a one-sided `1/2`-correct `OR`-predictor
(`pv_false`, `pv_balanced`).  This file does the **boosting** step: the `OR` of `t` independent forms,
`q_{(S_1,…,S_t)}(v) = ⋁_k L_{S_k}(v)`, is wrong only when *all* `t` forms vanish, and on a nonzero input that happens
for exactly `(2^{m-1})^t` of the `(2^m)^t` tuples — a `2^{-t}` fraction.  Hence the **full family of `t`-tuples is
majority-correct at every input** for `t ≥ 2`:

* on `v = 0` (`OR = 0`): the boosted predictor never fires (`boost_predict_zero`) — *all* tuples correct;
* on `v ≠ 0` (`OR = 1`): correct except for the `(2^{m-1})^t` all-zero tuples, i.e. `(2^m)^t - (2^{m-1})^t` correct,
  which is `> 1/2` of `(2^m)^t` once `t ≥ 2` (`boost_majority_nonzero`).

This **discharges the "majority-correct" clause** of the socket `ApproxToExactSymmetricDecode` for `OR`: there *is* a
family of low-(polynomial-)degree gates that is majority-correct at every point.  The **sole remaining gap** is the
family *size*: `(2^m)^t` is exponential, whereas the socket needs `r =` quasipolynomial.  Reducing it is the
probabilistic-method *sampling* step (Chernoff + union bound) — the last piece of Wall 1.

## What is proved (clean axioms, no `sorry`)

* `pv_zero_card` — for `v ≠ 0`, exactly `2^{m-1}` subsets give form value `0` (the complement of `pv_balanced`).
* `boost_wrong_card` — for `v ≠ 0`, the all-zero (wrong) `t`-tuples number `(2^{m-1})^t` (independence, `card_piFinset`).
* `boost_total` — there are `(2^m)^t` tuples in all.
* `boost_correct_card` — for `v ≠ 0`, the correct tuples number `(2^m)^t - (2^{m-1})^t`.
* `boost_predict_zero` — on the all-`0` input the boosted predictor fires for *no* tuple (one-sided).
* `boost_majority_nonzero` — for `t ≥ 2` and `v ≠ 0`, a strict majority of the `t`-tuples are correct
  (`total < 2 · correct`).

## Honest scope

The boosting count is exact and the full family genuinely is majority-correct at every point (`t ≥ 2`).  What is
**not** done (and not faked): shrinking the family from `(2^m)^t` to quasipolynomial size while keeping
majority-correctness — the Chernoff + union-bound *sampling*.  And the basis caveat from `…ACC0ProbabilisticForm`
stands (parity forms are low *poly*-degree, not low *monomial-`AND`*-degree).  Those two are the last of the
Beigel–Tarui front half, **Wall 1**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm

variable {m : ℕ}

/-- **The zero-parity subsets also number `2^{m-1}` (proved): the complement of `pv_balanced`.** -/
theorem pv_zero_card (v : Fin m → Bool) (j : Fin m) (hj : v j = true) :
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 0)).card = 2 ^ (m - 1) := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Finset (Fin m)))) (fun S => pv v S = 1)
  have hne : ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => ¬ pv v S = 1))
      = ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 0)) :=
    Finset.filter_congr (fun S _ => (by decide : ∀ a : ZMod 2, (¬ a = 1) ↔ a = 0) (pv v S))
  rw [hne, pv_balanced v j hj, Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at hpart
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le j.val) j.is_lt
  have hsucc : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hm]
    rw [pow_succ, Nat.pred_eq_sub_one]; ring
  omega

/-- **The all-zero (wrong) `t`-tuples number `(2^{m-1})^t` (proved), by independence across coordinates.** -/
theorem boost_wrong_card (t : ℕ) (v : Fin m → Bool) (j : Fin m) (hj : v j = true) :
    ((Finset.univ : Finset (Fin t → Finset (Fin m))).filter
        (fun σ => ∀ k, pv v (σ k) = 0)).card = (2 ^ (m - 1)) ^ t := by
  classical
  have hpi : ((Finset.univ : Finset (Fin t → Finset (Fin m))).filter (fun σ => ∀ k, pv v (σ k) = 0))
      = Fintype.piFinset (fun _ : Fin t =>
          (Finset.univ : Finset (Finset (Fin m))).filter (fun S => pv v S = 0)) := by
    ext σ
    simp [Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset_const, pv_zero_card v j hj]

/-- **There are `(2^m)^t` form-tuples in all (proved).** -/
theorem boost_total (t : ℕ) :
    (Finset.univ : Finset (Fin t → Finset (Fin m))).card = (2 ^ m) ^ t := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin]

/-- **On the all-`0` input the boosted predictor fires for no tuple (proved): one-sided, no false positive.** -/
theorem boost_predict_zero (t : ℕ) :
    ((Finset.univ : Finset (Fin t → Finset (Fin m))).filter
        (fun σ => ∃ k, pv (fun _ => false) (σ k) = 1)) = ∅ := by
  classical
  rw [Finset.filter_eq_empty_iff]
  rintro σ _ ⟨k, hk⟩
  rw [pv_false] at hk
  exact absurd hk (by decide)

/-- **The correct `t`-tuples number `(2^m)^t - (2^{m-1})^t` (proved), for a nonzero input.** -/
theorem boost_correct_card (t : ℕ) (v : Fin m → Bool) (j : Fin m) (hj : v j = true) :
    ((Finset.univ : Finset (Fin t → Finset (Fin m))).filter
        (fun σ => ∃ k, pv v (σ k) = 1)).card = (2 ^ m) ^ t - (2 ^ (m - 1)) ^ t := by
  classical
  have heq : ((Finset.univ : Finset (Fin t → Finset (Fin m))).filter (fun σ => ∃ k, pv v (σ k) = 1))
      = (Finset.univ : Finset (Fin t → Finset (Fin m))).filter (fun σ => ¬ ∀ k, pv v (σ k) = 0) := by
    apply Finset.filter_congr
    intro σ _
    rw [not_forall]
    exact exists_congr (fun k => ((by decide : ∀ a : ZMod 2, (¬ a = 0) ↔ a = 1) (pv v (σ k))).symm)
  rw [heq]
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin t → Finset (Fin m)))) (fun σ => ∀ k, pv v (σ k) = 0)
  rw [boost_wrong_card t v j hj] at hpart
  have htot : (Finset.univ : Finset (Fin t → Finset (Fin m))).card = (2 ^ m) ^ t := boost_total t
  omega

/-- **Boosting majority (proved): for `t ≥ 2` and a nonzero input, a strict majority of the `t`-tuples are correct.**
So the full `t`-tuple form family is majority-correct on every nonzero input — the boosted predictor is right except
on a `2^{-t}` fraction. -/
theorem boost_majority_nonzero (t : ℕ) (v : Fin m → Bool) (j : Fin m) (hj : v j = true) (ht : 2 ≤ t) :
    (Finset.univ : Finset (Fin t → Finset (Fin m))).card
      < 2 * ((Finset.univ : Finset (Fin t → Finset (Fin m))).filter
          (fun σ => ∃ k, pv v (σ k) = 1)).card := by
  rw [boost_total t, boost_correct_card t v j hj]
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le j.val) j.is_lt
  have h2m : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hm]
    rw [pow_succ, Nat.pred_eq_sub_one]; ring
  have ha : 0 < ((2 : ℕ) ^ (m - 1)) ^ t := pow_pos (pow_pos (by norm_num) _) t
  have h2t : (2 : ℕ) < 2 ^ t :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) ht)
  have hkey : 2 * ((2 : ℕ) ^ (m - 1)) ^ t < (2 ^ m) ^ t := by
    rw [h2m, mul_pow]
    exact (Nat.mul_lt_mul_right ha).2 h2t
  have hWX : ((2 : ℕ) ^ (m - 1)) ^ t ≤ (2 ^ m) ^ t :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le m 1)) t
  omega

end PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost.boost_wrong_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost.boost_correct_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost.boost_predict_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost.boost_majority_nonzero
