import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BasisBridge

/-!
# The `AND`-gate Beigel–Tarui front half, via `OR`-duality

`…ACC0BasisBridge` did the `OR` gate.  The `AND` gate follows by duality: `AND(v) = ¬ OR(¬v)`.  Dualizing the `OR`
construction replaces the linear form `L_S = ∑_{i∈S} X_i` by the **affine** form `A_S = ∑_{i∈S} (1 + X_i)` (which
evaluates to `L_S(¬v)` — the negated input), and the `OR` polynomial `1 − ∏_k(1 − L_{σ k})` by the dual
`andPoly = ∏_k (1 − A_{σ k})`.  Crucially `1 + X_i` is still *degree 1*, so the whole `AND` construction has exactly
the same degree profile as `OR`: total degree `≤ t`, hence in the fan-in-`≤t` monomial-`AND` span.

So the unbounded-fan-in `AND` gate has low-monomial-`AND`-degree approximants too — the second of the three `ACC⁰`
gate types (after `OR`; `MOD` next).

## What is proved (clean axioms, no `sorry`)

* `affForm` / `andPoly` — the affine form `∑_{i∈S}(1 + X_i)` and the dual polynomial `∏_k (1 − A_{σ k})`.
* `affForm_totalDegree_le` (`≤ 1`) and **`andPoly_totalDegree_le`** (`≤ t`).
* `eval_affForm` (`= pv (¬v) S`), `eval_andPoly_eq` (`= boolToZMod 2 (andPredict σ v)`).
* `andPredict_eq_not_boostPredict` — the duality: `andPredict σ v = ¬ boostPredict σ (¬v)`, so `OR`'s
  majority-correctness (`…ACC0SamplingForms`) transfers to `AND` under the input-negation bijection.
* **`andPredict_mem_monoAND_span`** — the `AND` basis bridge: the boosted `AND` predictor's `F₂`-embedding lies in the
  span of the degree-`≤t` monomial-`AND` indicators.

## Honest scope

This is the `AND`-gate front half, parallel to `OR` — an unbounded-fan-in `AND` has degree-`≤t` `F₂`-polynomial
(= fan-in-`≤t` monomial-`AND`) majority-correct approximants.  The remaining `ACC⁰` pieces: the `MOD` gate, and the
**depth composition** of these approximants through a constant-depth circuit (degree `(log s)^{O(d)}`), then assembly
into the `SYM∘AND` normal form.  Those are the rest of the Beigel–Tarui/Yao front half, **Wall 1**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AndBasisBridge

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm
open PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge

variable {m t : ℕ}

/-- Negate the input bitwise. -/
def notInput (v : Fin m → Bool) : Fin m → Bool := fun i => !(v i)

/-- The `F₂` **affine form** `A_S = ∑_{i∈S} (1 + X_i)` — evaluates to the linear form on the *negated* input. -/
noncomputable def affForm (S : Finset (Fin m)) : MvPolynomial (Fin m) (ZMod 2) :=
  ∑ i ∈ S, (1 + X i)

/-- The **dual (`AND`) polynomial** `∏_k (1 − A_{σ k})` — the dual of `boostPoly`, total degree `≤ t`. -/
noncomputable def andPoly (σ : Fin t → Finset (Fin m)) : MvPolynomial (Fin m) (ZMod 2) :=
  ∏ k, (1 - affForm (σ k))

/-- The boosted `AND` predictor: fires iff every form vanishes on the negated input (i.e. `¬ OR(¬v)`). -/
def andPredict (σ : Fin t → Finset (Fin m)) (v : Fin m → Bool) : Bool :=
  decide (∀ k, pv (notInput v) (σ k) = 0)

/-- **An affine form has total degree `≤ 1` (proved).** -/
theorem affForm_totalDegree_le (S : Finset (Fin m)) : (affForm S).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  refine le_trans (totalDegree_add _ _) ?_
  simp [totalDegree_one, totalDegree_X]

/-- `1 − A_S` has total degree `≤ 1` (proved). -/
theorem oneSubAff_totalDegree_le (S : Finset (Fin m)) :
    ((1 : MvPolynomial (Fin m) (ZMod 2)) - affForm S).totalDegree ≤ 1 := by
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le 1) (affForm_totalDegree_le S)

/-- **The dual `AND` polynomial has total degree `≤ t` (proved).** -/
theorem andPoly_totalDegree_le (σ : Fin t → Finset (Fin m)) : (andPoly σ).totalDegree ≤ t := by
  unfold andPoly
  refine le_trans (totalDegree_finset_prod Finset.univ _) ?_
  calc ∑ k : Fin t, ((1 : MvPolynomial (Fin m) (ZMod 2)) - affForm (σ k)).totalDegree
      ≤ ∑ _k : Fin t, 1 := Finset.sum_le_sum (fun k _ => oneSubAff_totalDegree_le (σ k))
    _ = t := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- The affine form evaluates to the parity form on the *negated* input (proved). -/
theorem eval_affForm (v : Fin m → Bool) (S : Finset (Fin m)) :
    eval (fun i => boolToZMod 2 (v i)) (affForm S) = pv (notInput v) S := by
  unfold affForm pv notInput
  rw [eval_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add, map_one, eval_X]
  cases v i <;> decide

/-- `andPoly` evaluates to `∏_k (1 − pv (¬v) (σ k))` on the Boolean cube (proved). -/
theorem eval_andPoly (v : Fin m → Bool) (σ : Fin t → Finset (Fin m)) :
    eval (fun i => boolToZMod 2 (v i)) (andPoly σ) = ∏ k, (1 - pv (notInput v) (σ k)) := by
  unfold andPoly
  rw [eval_prod]
  exact Finset.prod_congr rfl (fun k _ => by rw [eval_sub, map_one, eval_affForm])

/-- **`andPoly` evaluates to the boosted `AND` predictor (proved).** -/
theorem eval_andPoly_eq (v : Fin m → Bool) (σ : Fin t → Finset (Fin m)) :
    eval (fun i => boolToZMod 2 (v i)) (andPoly σ) = boolToZMod 2 (andPredict σ v) := by
  rw [eval_andPoly]
  by_cases h : ∀ k, pv (notInput v) (σ k) = 0
  · rw [Finset.prod_eq_one (fun k _ => by rw [h k]; decide)]
    simp [andPredict, boolToZMod, h]
  · obtain ⟨k, hk⟩ := not_forall.mp h
    have hnotall : ¬ ∀ k, pv (notInput v) (σ k) = 0 := h
    rw [Finset.prod_eq_zero (Finset.mem_univ k)
        (show (1 : ZMod 2) - pv (notInput v) (σ k) = 0 by
          rw [(by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) (pv (notInput v) (σ k)) hk]; decide)]
    simp [andPredict, boolToZMod, hnotall]

/-- **`AND`–`OR` duality (proved): `andPredict σ v = ¬ boostPredict σ (¬v)`.**  So the `OR` family's
majority-correctness transfers to `AND` under the input-negation bijection. -/
theorem andPredict_eq_not_boostPredict (σ : Fin t → Finset (Fin m)) (v : Fin m → Bool) :
    andPredict σ v = !(boostPredict σ (notInput v)) := by
  unfold andPredict boostPredict
  have hPQ : (∀ k, pv (notInput v) (σ k) = 0) ↔ ¬ ∃ k, pv (notInput v) (σ k) = 1 := by
    constructor
    · rintro hall ⟨k, hk⟩; rw [hall k] at hk; exact absurd hk (by decide)
    · intro hne k; by_contra hk
      exact hne ⟨k, (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) (pv (notInput v) (σ k)) hk⟩
  rw [(decide_eq_decide).mpr hPQ, decide_not]

/-- **The `AND` basis bridge (proved).**  The boosted `AND` predictor's `F₂`-embedding lies in the span of the
degree-`≤t` monomial-`AND` indicators — the `AND` gate is a low-monomial-`AND`-degree object too. -/
theorem andPredict_mem_monoAND_span (σ : Fin t → Finset (Fin m)) :
    (fun v : Fin m → Bool => boolToZMod 2 (andPredict σ v))
      ∈ Submodule.span (ZMod 2)
        (Set.range (fun S : {S // S ∈ lowDegMonomials m t} =>
          fun v : Fin m → Bool => if monoAND S.1 v then (1 : ZMod 2) else 0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkey := lowDegPolyEval_mem_monoAND_span 2 t (andPoly σ) (andPoly_totalDegree_le σ)
  have hfun : (fun v : Fin m → Bool => boolToZMod 2 (andPredict σ v))
      = (fun v : Fin m → Bool => eval (fun i => boolToZMod 2 (v i)) (andPoly σ)) := by
    funext v
    exact (eval_andPoly_eq v σ).symm
  rw [hfun]
  exact hkey

end PallLean.Paper93.DeepMath.PathB.ACC0AndBasisBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndBasisBridge.andPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndBasisBridge.andPredict_eq_not_boostPredict
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AndBasisBridge.andPredict_mem_monoAND_span
