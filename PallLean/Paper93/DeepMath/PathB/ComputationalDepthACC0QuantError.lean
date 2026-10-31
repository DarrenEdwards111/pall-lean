import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0QuantDegree

/-!
# Quantitative error bound: every `MOD`-free circuit is approximable at degree `≤ t^depth` and error `≤ size·2^{-t}`

This completes the quantitative Razborov–Smolensky package for the `MOD`-free (`AC⁰`) fragment.  `…ACC0QuantDegree`
gave degree `≤ t^depth`; here the *error* is bounded by `size·2^{-t}` (count form `2^t·error ≤ size·2^n`).  Each gate
contributes a `2^{-t}`-fraction boosting error, and errors accumulate *additively* across the `size` gates (union
bound), so the whole-circuit error stays `≤ size·2^{-t}`.

## What is proved (clean axioms, no `sorry`)

* `gate_bound` — a boosted form whose error is `≤ 2^{-t}` of the inputs: `∃ σ, 2^t·|errSetV v σ| ≤ 2^n` (the gate's
  own boosting error; the `k = 0` empty-gate case has `errSetV = ∅`).
* `or_step_quant` / `and_step_quant` — the `OR`/`AND` step with degree `≤ t·D`, error `≤ (∑ subgate errors) + Eg`, and
  the gate bound `2^t·Eg ≤ 2^n`.
* **`approximable_full`** — for `t ≥ 1`, `∀ C, ∃ Q, Q.totalDegree ≤ t^cdepth C ∧ 2^t·(perr Q ⟦C⟧).card ≤ size C·2^n`:
  every `MOD`-free circuit has an `F₂` approximant of degree `≤ t^depth` *and* error `≤ size·2^{-t}`.

## Honest scope

This finishes the quantitative `AC⁰` Razborov–Smolensky construction (degree `t^depth`, error `size·2^{-t}`) — the
package now "feels finished" for `AC⁰`.  It is **classical** (`AC⁰`/`AC⁰[2]`-level, Tier 1/2), **not** new mathematics
and **not** progress toward `P ≠ NP`.  `MOD` extends only to prime-power moduli (`MOD₂` done); composite `MOD_m` is
the genuine `ACC⁰` barrier the polynomial method cannot cross — **Wall 1**, the reason `NEXP ⊄ ACC⁰` needed Williams'
algorithmic method.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0QuantError

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge
open PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm
open PallLean.Paper93.DeepMath.PathB.ACC0LayerCompose
open PallLean.Paper93.DeepMath.PathB.ACC0CompositionCorrect
open PallLean.Paper93.DeepMath.PathB.ACC0InputSmallError
open PallLean.Paper93.DeepMath.PathB.ACC0OrStep
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox
open PallLean.Paper93.DeepMath.PathB.ACC0DepthInduction
open PallLean.Paper93.DeepMath.PathB.ACC0QuantDegree

variable {n k t : ℕ}

/-- **The per-gate boosting error is `≤ 2^{-t}` of the inputs (proved): `∃ σ, 2^t·|errSetV v σ| ≤ 2^n`.**  Cancels the
`(2^{k-1})^t` factor (`k ≥ 1`); the empty-gate `k = 0` case has `errSetV = ∅`. -/
theorem gate_bound (v : (Fin n → Bool) → (Fin k → Bool)) :
    ∃ σ : Fin t → Finset (Fin k), 2 ^ t * (errSetV v σ).card ≤ Fintype.card (Fin n → Bool) := by
  obtain ⟨σ, hσ⟩ := exists_small_errSetV (X := Fin n → Bool) (k := k) (t := t) v
  refine ⟨σ, ?_⟩
  rw [Fintype.card_finset, Fintype.card_fin] at hσ
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hzero : (errSetV v σ).card = 0 := by
      rw [Finset.card_eq_zero, errSetV, Finset.filter_eq_empty_iff]
      rintro x _ ⟨⟨j, _⟩, _⟩
      exact j.elim0
    rw [hzero]; simp
  · have hpow : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hk]
      rw [pow_succ, Nat.pred_eq_sub_one]; ring
    rw [hpow, mul_pow] at hσ
    have key : 2 ^ t * (errSetV v σ).card * (2 ^ (k - 1)) ^ t
        ≤ Fintype.card (Fin n → Bool) * (2 ^ (k - 1)) ^ t := by
      calc 2 ^ t * (errSetV v σ).card * (2 ^ (k - 1)) ^ t
          = (2 ^ t * (2 ^ (k - 1)) ^ t) * (errSetV v σ).card := by ring
        _ ≤ Fintype.card (Fin n → Bool) * (2 ^ (k - 1)) ^ t := hσ
    exact Nat.le_of_mul_le_mul_right key (pow_pos (pow_pos (by norm_num) _) t)

/-- **`OR` quantitative step (proved): degree `≤ t·D`, error `≤ (∑ subgate errors) + Eg`, gate `2^t·Eg ≤ 2^n`.** -/
theorem or_step_quant (h : Fin k → (Fin n → Bool) → Bool) (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (D : ℕ) (Ef : Fin k → ℕ) (hdeg : ∀ i, (P i).totalDegree ≤ D)
    (herr : ∀ i, (perr (P i) (h i)).card ≤ Ef i) :
    ∃ (Q : MvPolynomial (Fin n) (ZMod 2)) (Eg : ℕ),
      Q.totalDegree ≤ t * D
        ∧ (perr Q (fun x => orTarget (fun i => h i x))).card ≤ (∑ i, Ef i) + Eg
        ∧ 2 ^ t * Eg ≤ Fintype.card (Fin n → Bool) := by
  obtain ⟨σ, hgate⟩ := gate_bound (t := t) (fun x i => h i x)
  refine ⟨compPoly P σ, (errSetV (fun x i => h i x) σ).card,
    compPoly_totalDegree_le P hdeg σ, ?_, hgate⟩
  have hsub : perr (compPoly P σ) (fun x => orTarget (fun i => h i x))
      ⊆ (Finset.univ.biUnion (fun i => perr (P i) (h i))) ∪ errSetV (fun x i => h i x) σ := by
    intro x hx
    rw [perr, Finset.mem_filter] at hx
    rw [Finset.mem_union]
    by_contra hcon
    push_neg at hcon
    obtain ⟨hbu, herv⟩ := hcon
    have hsub_correct : ∀ i, MvPolynomial.eval (fun j => boolToZMod 2 (x j)) (P i)
        = boolToZMod 2 (h i x) := by
      intro i
      by_contra hne
      exact hbu (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩⟩)
    have hQ := eval_compPoly_of_subgates x P h hsub_correct σ
    rw [errSetV_eq, Finset.mem_filter, not_and] at herv
    have heq := not_not.mp (herv (Finset.mem_univ x))
    exact hx.2 (by rw [hQ, heq])
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
  have hbu : (Finset.univ.biUnion (fun i => perr (P i) (h i))).card ≤ ∑ i, Ef i :=
    le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun i _ => herr i))
  omega

/-- **`AND` quantitative step (proved), via `OR`-duality.** -/
theorem and_step_quant (h : Fin k → (Fin n → Bool) → Bool) (P : Fin k → MvPolynomial (Fin n) (ZMod 2))
    (D : ℕ) (Ef : Fin k → ℕ) (hdeg : ∀ i, (P i).totalDegree ≤ D)
    (herr : ∀ i, (perr (P i) (h i)).card ≤ Ef i) :
    ∃ (Q : MvPolynomial (Fin n) (ZMod 2)) (Eg : ℕ),
      Q.totalDegree ≤ t * D
        ∧ (perr Q (fun x => andTarget (fun i => h i x))).card ≤ (∑ i, Ef i) + Eg
        ∧ 2 ^ t * Eg ≤ Fintype.card (Fin n → Bool) := by
  obtain ⟨Q', Eg, hdegQ', herrQ', hgate⟩ := or_step_quant (t := t) (fun i x => !(h i x))
    (fun i => 1 - P i) D Ef
    (fun i => le_trans (MvPolynomial.totalDegree_sub _ _)
      (by rw [MvPolynomial.totalDegree_one]; exact max_le (Nat.zero_le D) (hdeg i)))
    (fun i => by show (perr (1 - P i) (fun x => !(h i x))).card ≤ Ef i
                 rw [perr_not_eq]; exact herr i)
  refine ⟨1 - Q', Eg, ?_, ?_, hgate⟩
  · exact le_trans (MvPolynomial.totalDegree_sub _ _)
      (by rw [MvPolynomial.totalDegree_one]; exact max_le (Nat.zero_le _) hdegQ')
  · have hkey : (fun x => andTarget (fun i => h i x))
        = (fun x => !(orTarget (fun i => !(h i x)))) := by
      funext x; exact andTarget_eq (fun i => h i x)
    rw [hkey, perr_not_eq]
    exact herrQ'

/-- The `Fin`-to-`List` sum bridge (proved). -/
theorem sum_get_eq (cs : List (Circ n)) (g : Circ n → ℕ) :
    (cs.attach.map (fun c => g c.1)).sum = ∑ i : Fin cs.length, g (cs.get i) := by
  have h1 : (cs.attach.map (fun c => g c.1)) = cs.map g := by simp
  rw [h1]
  conv_lhs => rw [← List.ofFn_get cs, List.map_ofFn]
  rw [List.sum_ofFn]
  rfl

/-- **The full quantitative bound (proved): degree `≤ t^depth` AND error `≤ size·2^{-t}`.** -/
theorem approximable_full (ht : 1 ≤ t) : ∀ C : Circ n,
    ∃ Q : MvPolynomial (Fin n) (ZMod 2),
      Q.totalDegree ≤ t ^ cdepth C
        ∧ 2 ^ t * (perr Q (fun x => Circ.eval x C)).card
            ≤ Circ.size C * Fintype.card (Fin n → Bool)
  | .inp i => by
      refine ⟨MvPolynomial.X i, ?_, ?_⟩
      · simp only [cdepth, pow_zero]; exact le_of_eq (MvPolynomial.totalDegree_X i)
      · have : (perr (MvPolynomial.X i) (fun x => Circ.eval x (Circ.inp i))).card = 0 := by
          rw [perr, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _; simp [MvPolynomial.eval_X, Circ.eval]
        rw [this]; simp
  | .const b => by
      refine ⟨MvPolynomial.C (boolToZMod 2 b), ?_, ?_⟩
      · simp only [cdepth, pow_zero]; rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le 1
      · have hz : (perr (MvPolynomial.C (boolToZMod 2 b) : MvPolynomial (Fin n) (ZMod 2))
            (fun x => Circ.eval x (Circ.const b))).card = 0 := by
          rw [perr, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _; simp [MvPolynomial.eval_C, Circ.eval]
        rw [hz]; simp
  | .not c => by
      obtain ⟨Q, hdeg, herr⟩ := approximable_full ht c
      refine ⟨1 - Q, ?_, ?_⟩
      · simp only [cdepth]
        exact le_trans (MvPolynomial.totalDegree_sub _ _)
          (by rw [MvPolynomial.totalDegree_one]; exact max_le (Nat.zero_le _) hdeg)
      · rw [show (fun x => Circ.eval x (Circ.not c)) = (fun x => !(Circ.eval x c)) from by
            funext x; simp [Circ.eval], perr_not_eq]
        simp only [Circ.size]
        nlinarith [herr, Nat.zero_le (Fintype.card (Fin n → Bool))]
  | .or cs => by
      have hforall : ∀ i : Fin cs.length, ∃ (P : MvPolynomial (Fin n) (ZMod 2)),
          P.totalDegree ≤ t ^ cdepth (cs.get i)
            ∧ 2 ^ t * (perr P (fun x => Circ.eval x (cs.get i))).card
                ≤ Circ.size (cs.get i) * Fintype.card (Fin n → Bool) := by
        intro i; exact approximable_full ht (cs.get i)
      choose P hd herr2 using hforall
      have hpos : 1 ≤ cdepth (Circ.or cs) := by simp only [cdepth]; omega
      obtain ⟨Q, Eg, hdegQ, herrQ, hgate⟩ :=
        or_step_quant (t := t) (fun i => fun x => Circ.eval x (cs.get i)) P
          (t ^ (cdepth (Circ.or cs) - 1))
          (fun i => (perr (P i) (fun x => Circ.eval x (cs.get i))).card)
          (fun i => le_trans (hd i)
            (Nat.pow_le_pow_right ht (by have := cdepth_or_get_lt cs i; omega)))
          (fun i => le_refl _)
      refine ⟨Q, ?_, ?_⟩
      · refine le_of_le_of_eq hdegQ ?_
        rw [← pow_succ']; congr 1; omega
      · have hbridge : (fun x => Circ.eval x (Circ.or cs))
            = (fun x => orTarget (fun i : Fin cs.length => Circ.eval x (cs.get i))) := by
          funext x; exact or_eval_bridge x cs
        rw [hbridge]
        calc 2 ^ t * (perr Q (fun x => orTarget (fun i => Circ.eval x (cs.get i)))).card
            ≤ 2 ^ t * ((∑ i, (perr (P i) (fun x => Circ.eval x (cs.get i))).card) + Eg) :=
              Nat.mul_le_mul_left _ herrQ
          _ = (∑ i, 2 ^ t * (perr (P i) (fun x => Circ.eval x (cs.get i))).card) + 2 ^ t * Eg := by
              rw [Nat.mul_add, Finset.mul_sum]
          _ ≤ (∑ i, Circ.size (cs.get i) * Fintype.card (Fin n → Bool))
                + Fintype.card (Fin n → Bool) :=
              Nat.add_le_add (Finset.sum_le_sum (fun i _ => herr2 i)) hgate
          _ = (∑ i, Circ.size (cs.get i)) * Fintype.card (Fin n → Bool)
                + Fintype.card (Fin n → Bool) := by rw [← Finset.sum_mul]
          _ = ((cs.attach.map (fun c => Circ.size c.1)).sum) * Fintype.card (Fin n → Bool)
                + Fintype.card (Fin n → Bool) := by rw [sum_get_eq]
          _ = Circ.size (Circ.or cs) * Fintype.card (Fin n → Bool) := by
              simp only [Circ.size]; ring
  | .and cs => by
      have hforall : ∀ i : Fin cs.length, ∃ (P : MvPolynomial (Fin n) (ZMod 2)),
          P.totalDegree ≤ t ^ cdepth (cs.get i)
            ∧ 2 ^ t * (perr P (fun x => Circ.eval x (cs.get i))).card
                ≤ Circ.size (cs.get i) * Fintype.card (Fin n → Bool) := by
        intro i; exact approximable_full ht (cs.get i)
      choose P hd herr2 using hforall
      have hpos : 1 ≤ cdepth (Circ.and cs) := by simp only [cdepth]; omega
      obtain ⟨Q, Eg, hdegQ, herrQ, hgate⟩ :=
        and_step_quant (t := t) (fun i => fun x => Circ.eval x (cs.get i)) P
          (t ^ (cdepth (Circ.and cs) - 1))
          (fun i => (perr (P i) (fun x => Circ.eval x (cs.get i))).card)
          (fun i => le_trans (hd i)
            (Nat.pow_le_pow_right ht (by have := cdepth_and_get_lt cs i; omega)))
          (fun i => le_refl _)
      refine ⟨Q, ?_, ?_⟩
      · refine le_of_le_of_eq hdegQ ?_
        rw [← pow_succ']; congr 1; omega
      · have hbridge : (fun x => Circ.eval x (Circ.and cs))
            = (fun x => andTarget (fun i : Fin cs.length => Circ.eval x (cs.get i))) := by
          funext x; exact and_eval_bridge x cs
        rw [hbridge]
        calc 2 ^ t * (perr Q (fun x => andTarget (fun i => Circ.eval x (cs.get i)))).card
            ≤ 2 ^ t * ((∑ i, (perr (P i) (fun x => Circ.eval x (cs.get i))).card) + Eg) :=
              Nat.mul_le_mul_left _ herrQ
          _ = (∑ i, 2 ^ t * (perr (P i) (fun x => Circ.eval x (cs.get i))).card) + 2 ^ t * Eg := by
              rw [Nat.mul_add, Finset.mul_sum]
          _ ≤ (∑ i, Circ.size (cs.get i) * Fintype.card (Fin n → Bool))
                + Fintype.card (Fin n → Bool) :=
              Nat.add_le_add (Finset.sum_le_sum (fun i _ => herr2 i)) hgate
          _ = (∑ i, Circ.size (cs.get i)) * Fintype.card (Fin n → Bool)
                + Fintype.card (Fin n → Bool) := by rw [← Finset.sum_mul]
          _ = ((cs.attach.map (fun c => Circ.size c.1)).sum) * Fintype.card (Fin n → Bool)
                + Fintype.card (Fin n → Bool) := by rw [sum_get_eq]
          _ = Circ.size (Circ.and cs) * Fintype.card (Fin n → Bool) := by
              simp only [Circ.size]; ring
  termination_by C => sizeOf C
  decreasing_by
    all_goals simp_wf
    all_goals (first
      | omega
      | (have h := List.sizeOf_lt_of_mem (List.get_mem cs i)
         simp only [List.get_eq_getElem] at h
         omega))

end PallLean.Paper93.DeepMath.PathB.ACC0QuantError

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantError.approximable_full
