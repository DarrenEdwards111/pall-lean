import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ProbabilisticBoost
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BasisBridge

/-!
# A single boosted form with small error (averaging) — the per-gate error for error accumulation

The error-accumulation lemma (`…ACC0ErrorAccumulation`) needs each gate to have a *single* approximant with a small
error set.  The boosting (`…ACC0ProbabilisticBoost`) gives a *family* that is majority-correct; this file extracts a
*single* good form by **averaging** (the first-moment / probabilistic method): the average over all boosted forms `σ`
of the error count is `≤ 2^{-t}·|inputs|`, so *some* `σ` achieves at most the average.

The error set of a boosted form `σ` (one-sided: it never errs when `OR = 0`, errs at `w ≠ 0` only when every form
vanishes) is `{w : (∃ j, w_j) ∧ ∀ l, L_{σ l}(w) = 0}`.  Counting the pairs `(σ, w)` two ways (Fubini): for each
nonzero `w` exactly `(2^{k-1})^t` forms err on it (`boost_wrong_card`), so

```
∑_σ |error σ|  =  ∑_{w≠0} (2^{k-1})^t  ≤  2^k · (2^{k-1})^t .
```

Dividing by the `(2^k)^t` forms: the average error is `≤ 2^k·(2^{k-1})^t / (2^k)^t = 2^{-t}·2^k`, so some `σ` errs on
`≤ 2^{-t}` fraction of inputs — a single low-degree form with error `< 2^{-t}|inputs|`, exactly the per-gate input for
error accumulation.

## What is proved (clean axioms, no `sorry`)

* `errSet` — the error set of a boosted form, and `errSet_eq` relating it to the actual `boostPredict`-vs-`OR` error.
* `sum_errSet_card_le` — `∑_σ |errSet σ| ≤ 2^k · (2^{k-1})^t` (the Fubini double-count).
* **`exists_small_errSet`** — `∃ σ, (2^k)^t · |errSet σ| ≤ 2^k · (2^{k-1})^t` (averaging): a single form whose error,
  scaled by the number of forms, is at most the total — i.e. error fraction `≤ 2^{-t}`.

## Honest scope

This is the averaging step: from the boosted family to a single small-error form.  Feeding it into
`…ACC0ErrorAccumulation` (one form per gate, union-bound the errors) and the depth composition
(`…ACC0LayerCompose`, `…ACC0CompositionCorrect`) is the assembly toward the full `ACC⁰ → SYM∘AND` normal form; that
inductive assembly, with `MOD` (prime-power only — composite `MOD` is the genuine barrier), is the rest of the
Beigel–Tarui/Yao front half, **Wall 1**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost
open PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge

variable {k t : ℕ}

/-- The `OR` target over the subgate-output vector `w`. -/
def orTarget (w : Fin k → Bool) : Bool := decide (∃ j, w j = true)

/-- The **error set** of the boosted form `σ`: the inputs where the boosted `OR`-predictor disagrees with `OR`.  By
one-sidedness this is `{w : (∃ j, w_j) ∧ ∀ l, L_{σ l}(w) = 0}`. -/
noncomputable def errSet (σ : Fin t → Finset (Fin k)) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun w => (∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0)

/-- The form vanishes on the all-`0` input (proved). -/
theorem pv_all_false {w : Fin k → Bool} (hw : ∀ j, w j = false) (S : Finset (Fin k)) :
    pv w S = 0 := by
  simp only [pv]
  exact Finset.sum_eq_zero (fun j _ => by simp [hw j])

/-- One-sidedness (proved): if a linear form fires, the input has a set bit. -/
theorem pv_one_imp_exists {w : Fin k → Bool} {S : Finset (Fin k)} (h : pv w S = 1) :
    ∃ j, w j = true := by
  by_contra hne
  push_neg at hne
  have hwf : ∀ j, w j = false := fun j => by simpa using hne j
  rw [pv_all_false hwf S] at h
  exact absurd h (by decide)

/-- **`errSet` is exactly the boosted-predictor error set (proved).**  By one-sidedness (`pv = 1 → ∃ j, w_j`), the
boosted `OR`-predictor disagrees with `OR` exactly on `{w : (∃ j, w_j) ∧ ∀ l, L_{σ l}(w) = 0}`. -/
theorem errSet_eq (σ : Fin t → Finset (Fin k)) :
    errSet σ = Finset.univ.filter (fun w => boostPredict σ w ≠ orTarget w) := by
  apply Finset.filter_congr
  intro w _
  unfold boostPredict orTarget
  rw [ne_eq, decide_eq_decide]
  have hAB : (∃ l, pv w (σ l) = 1) → (∃ j, w j = true) := fun ⟨l, hl⟩ => pv_one_imp_exists hl
  have hAnot : (∀ l, pv w (σ l) = 0) ↔ ¬ (∃ l, pv w (σ l) = 1) := by
    constructor
    · rintro hall ⟨l, hl⟩; rw [hall l] at hl; exact absurd hl (by decide)
    · intro hne l; by_contra hl
      exact hne ⟨l, (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) (pv w (σ l)) hl⟩
  rw [hAnot]
  constructor
  · rintro ⟨hB, hnA⟩ hiff; exact hnA (hiff.mpr hB)
  · intro hniff
    refine ⟨?_, ?_⟩
    · by_contra hB; exact hniff ⟨fun hA => absurd (hAB hA) hB, fun hB' => absurd hB' hB⟩
    · intro hA; exact hniff ⟨fun _ => hAB hA, fun _ => hA⟩

/-- **The Fubini double-count (proved): `∑_σ |errSet σ| ≤ 2^k · (2^{k-1})^t`.** -/
theorem sum_errSet_card_le :
    ∑ σ : Fin t → Finset (Fin k), (errSet σ).card
      ≤ Fintype.card (Fin k → Bool) * (2 ^ (k - 1)) ^ t := by
  have hper : ∀ w : Fin k → Bool,
      (Finset.univ.filter (fun σ : Fin t → Finset (Fin k) =>
        (∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0)).card ≤ (2 ^ (k - 1)) ^ t := by
    intro w
    by_cases hj : ∃ j, w j = true
    · obtain ⟨j, hjw⟩ := hj
      have heq : (Finset.univ.filter (fun σ : Fin t → Finset (Fin k) =>
            (∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0))
          = Finset.univ.filter (fun σ : Fin t → Finset (Fin k) => ∀ l, pv w (σ l) = 0) := by
        apply Finset.filter_congr
        exact fun σ _ => ⟨fun h => h.2, fun h => ⟨⟨j, hjw⟩, h⟩⟩
      rw [heq, boost_wrong_card t w j hjw]
    · rw [Finset.filter_false_of_mem (fun σ _ h => hj h.1)]
      simp
  calc ∑ σ : Fin t → Finset (Fin k), (errSet σ).card
      = ∑ σ : Fin t → Finset (Fin k), ∑ w : Fin k → Bool,
          (if (∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0 then 1 else 0) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [errSet, Finset.card_filter]
    _ = ∑ w : Fin k → Bool, ∑ σ : Fin t → Finset (Fin k),
          (if (∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0 then 1 else 0) := Finset.sum_comm
    _ = ∑ w : Fin k → Bool, (Finset.univ.filter (fun σ : Fin t → Finset (Fin k) =>
          (∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0)).card := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.card_filter]
    _ ≤ ∑ _w : Fin k → Bool, (2 ^ (k - 1)) ^ t := Finset.sum_le_sum (fun w _ => hper w)
    _ = Fintype.card (Fin k → Bool) * (2 ^ (k - 1)) ^ t := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **A single small-error form exists (proved), by averaging.**  Some boosted form `σ` has
`(2^k)^t · |errSet σ| ≤ 2^k · (2^{k-1})^t` — error fraction `≤ 2^{-t}`. -/
theorem exists_small_errSet :
    ∃ σ : Fin t → Finset (Fin k),
      (Fintype.card (Finset (Fin k))) ^ t * (errSet σ).card
        ≤ Fintype.card (Fin k → Bool) * (2 ^ (k - 1)) ^ t := by
  obtain ⟨σ₀, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin t → Finset (Fin k)))
    (fun σ => (errSet σ).card) Finset.univ_nonempty
  refine ⟨σ₀, ?_⟩
  have hns : (Finset.univ : Finset (Fin t → Finset (Fin k))).card • (errSet σ₀).card
      ≤ ∑ σ : Fin t → Finset (Fin k), (errSet σ).card :=
    Finset.card_nsmul_le_sum Finset.univ (fun σ => (errSet σ).card) (errSet σ₀).card
      (fun σ hσ => hmin σ hσ)
  have hpool : (Finset.univ : Finset (Fin t → Finset (Fin k))).card
      = (Fintype.card (Finset (Fin k))) ^ t := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [hpool, smul_eq_mul] at hns
  exact le_trans hns sum_errSet_card_le

end PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm.sum_errSet_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm.exists_small_errSet
