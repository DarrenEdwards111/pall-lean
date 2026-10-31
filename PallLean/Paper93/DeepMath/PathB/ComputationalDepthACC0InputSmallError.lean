import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SmallErrorForm

/-!
# Input-space small-error averaging — the per-gate error for the circuit induction

`…ACC0SmallErrorForm` averaged the boosted-form error over the **subgate-output** space `Fin k → Bool`.  But in the
circuit induction the gate's inputs are the *circuit* inputs `x`, and the subgate values are `v(x) = (c_1(x), …,
c_k(x))` — the map `x ↦ v(x)` is **not** measure-preserving, so the per-output error count does not transfer.  This
file does the averaging over the **input** space directly, for an arbitrary value map `v : X → (Fin k → Bool)`.

For each fixed input `x`, the fraction of boosted forms `σ` that err on `v(x)` is `2^{-t}` (or `0` if `v(x) = 0`), so

```
∑_σ |{x : σ errs on v(x)}|  =  ∑_x |{σ : σ errs on v(x)}|  ≤  ∑_x (2^{k-1})^t  =  |X|·(2^{k-1})^t .
```

Averaging over the `(2^k)^t` forms, some `σ` errs on `≤ 2^{-t}·|X|` inputs.  This is exactly the per-gate small-error
form *over the circuit inputs*, the input needed for the `OR`/`AND` inductive step of `…ACC0CircuitApprox`.  It
generalizes `…ACC0SmallErrorForm` (the case `X = Fin k → Bool`, `v = id`).

## What is proved (clean axioms, no `sorry`)

* `boostError_iff` — the boosted `OR`-predictor errs at output vector `w` iff `(∃ j, w_j) ∧ ∀ l, L_{σ l}(w) = 0`.
* `errSetV` / `errSetV_eq` — the input error set for value map `v`, and that it is the actual `boostPredict`-vs-`OR`
  error on `v(x)`.
* `sum_errSetV_card_le` — `∑_σ |errSetV v σ| ≤ |X|·(2^{k-1})^t` (Fubini over inputs).
* **`exists_small_errSetV`** — `∃ σ, (2^k)^t · |errSetV v σ| ≤ |X|·(2^{k-1})^t` (averaging): a single boosted form
  erring on `≤ 2^{-t}` fraction of *inputs*.

## Honest scope

This is the input-space per-gate small-error form.  Plugging it into the `OR`/`AND` inductive step of
`…ACC0CircuitApprox` (the gate's boosting error over inputs) + per-point composition (`…ACC0CompositionCorrect`) +
union bound over subgate errors (`…ACC0ErrorAccumulation`) gives one layer of the depth induction; iterating it, and
handling `MOD` (prime-power only — composite `MOD` is the genuine open barrier), is the rest of the Beigel–Tarui/Yao
front half, **Wall 1**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0InputSmallError

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticBoost
open PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge
open PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm

variable {X : Type*} [Fintype X] {k t : ℕ}

/-- **The boosted `OR`-predictor errs at `w` iff `(∃ j, w_j) ∧ ∀ l, L_{σ l}(w) = 0` (proved).** -/
theorem boostError_iff (w : Fin k → Bool) (σ : Fin t → Finset (Fin k)) :
    (boostPredict σ w ≠ orTarget w) ↔ ((∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0) := by
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
  · intro hniff
    refine ⟨?_, ?_⟩
    · by_contra hB; exact hniff ⟨fun hA => absurd (hAB hA) hB, fun hB' => absurd hB' hB⟩
    · intro hA; exact hniff ⟨fun _ => hAB hA, fun _ => hA⟩
  · rintro ⟨hB, hnA⟩ hiff; exact hnA (hiff.mpr hB)

/-- The **input error set** for a value map `v`: inputs `x` where the boosted form errs on the subgate values `v(x)`. -/
noncomputable def errSetV (v : X → (Fin k → Bool)) (σ : Fin t → Finset (Fin k)) : Finset X :=
  Finset.univ.filter (fun x => (∃ j, (v x) j = true) ∧ ∀ l, pv (v x) (σ l) = 0)

/-- **`errSetV` is the actual `boostPredict`-vs-`OR` error on `v(x)` (proved).** -/
theorem errSetV_eq (v : X → (Fin k → Bool)) (σ : Fin t → Finset (Fin k)) :
    errSetV v σ = Finset.univ.filter (fun x => boostPredict σ (v x) ≠ orTarget (v x)) := by
  apply Finset.filter_congr
  exact fun x _ => (boostError_iff (v x) σ).symm

/-- For a fixed output vector `w`, the boosted forms vanishing on it number `≤ (2^{k-1})^t` (proved). -/
theorem vanish_card_le (w : Fin k → Bool) :
    (Finset.univ.filter (fun σ : Fin t → Finset (Fin k) =>
      (∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0)).card ≤ (2 ^ (k - 1)) ^ t := by
  by_cases hj : ∃ j, w j = true
  · obtain ⟨j, hjw⟩ := hj
    have heq : (Finset.univ.filter (fun σ : Fin t → Finset (Fin k) =>
          (∃ j, w j = true) ∧ ∀ l, pv w (σ l) = 0))
        = Finset.univ.filter (fun σ : Fin t → Finset (Fin k) => ∀ l, pv w (σ l) = 0) :=
      Finset.filter_congr (fun σ _ => ⟨fun h => h.2, fun h => ⟨⟨j, hjw⟩, h⟩⟩)
    rw [heq, boost_wrong_card t w j hjw]
  · rw [Finset.filter_false_of_mem (fun σ _ h => hj h.1)]
    simp

/-- **The Fubini double-count over inputs (proved): `∑_σ |errSetV v σ| ≤ |X|·(2^{k-1})^t`.** -/
theorem sum_errSetV_card_le (v : X → (Fin k → Bool)) :
    ∑ σ : Fin t → Finset (Fin k), (errSetV v σ).card
      ≤ Fintype.card X * (2 ^ (k - 1)) ^ t := by
  calc ∑ σ : Fin t → Finset (Fin k), (errSetV v σ).card
      = ∑ σ : Fin t → Finset (Fin k), ∑ x : X,
          (if (∃ j, (v x) j = true) ∧ ∀ l, pv (v x) (σ l) = 0 then 1 else 0) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [errSetV, Finset.card_filter]
    _ = ∑ x : X, ∑ σ : Fin t → Finset (Fin k),
          (if (∃ j, (v x) j = true) ∧ ∀ l, pv (v x) (σ l) = 0 then 1 else 0) := Finset.sum_comm
    _ = ∑ x : X, (Finset.univ.filter (fun σ : Fin t → Finset (Fin k) =>
          (∃ j, (v x) j = true) ∧ ∀ l, pv (v x) (σ l) = 0)).card := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.card_filter]
    _ ≤ ∑ _x : X, (2 ^ (k - 1)) ^ t := Finset.sum_le_sum (fun x _ => vanish_card_le (v x))
    _ = Fintype.card X * (2 ^ (k - 1)) ^ t := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Input-space small-error form exists (proved), by averaging.**  Some boosted form errs on `≤ 2^{-t}` fraction of
the circuit inputs: `(2^k)^t · |errSetV v σ| ≤ |X| · (2^{k-1})^t`. -/
theorem exists_small_errSetV (v : X → (Fin k → Bool)) :
    ∃ σ : Fin t → Finset (Fin k),
      (Fintype.card (Finset (Fin k))) ^ t * (errSetV v σ).card
        ≤ Fintype.card X * (2 ^ (k - 1)) ^ t := by
  obtain ⟨σ₀, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin t → Finset (Fin k)))
    (fun σ => (errSetV v σ).card) Finset.univ_nonempty
  refine ⟨σ₀, ?_⟩
  have hns : (Finset.univ : Finset (Fin t → Finset (Fin k))).card • (errSetV v σ₀).card
      ≤ ∑ σ : Fin t → Finset (Fin k), (errSetV v σ).card :=
    Finset.card_nsmul_le_sum Finset.univ (fun σ => (errSetV v σ).card) (errSetV v σ₀).card
      (fun σ hσ => hmin σ hσ)
  have hpool : (Finset.univ : Finset (Fin t → Finset (Fin k))).card
      = (Fintype.card (Finset (Fin k))) ^ t := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [hpool, smul_eq_mul] at hns
  exact le_trans hns (sum_errSetV_card_le v)

end PallLean.Paper93.DeepMath.PathB.ACC0InputSmallError

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0InputSmallError.boostError_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0InputSmallError.sum_errSetV_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0InputSmallError.exists_small_errSetV
