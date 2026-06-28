import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOrApprox
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAveraging
import Mathlib

/-!
# A fixed good OR-approximator exists (PROVED) — the per-gate step, made concrete

Combining the averaging argument (`Averaging.exists_few_bad`) with the per-input error bound
(`OrApprox.orApproxT_disagree_count`) yields the concrete per-gate conclusion: **there is a fixed tuple of random
linear forms whose `t`-fold OR-approximator errs on only a small set of inputs.**

  `exists_good_forms` — `∃ Ss : Fin t → Finset (Fin n)`, the set of inputs on which the approximator *disagrees*
        with `OR` (the forms all vanish while the input is nonzero) has size, times `|tuples|`, at most
        `2^((n-1)t) · 2ⁿ` — i.e. an error fraction `≤ 2⁻ᵗ`.

This is the existence of the gate polynomial used in the circuit-approximation induction: the OR/AND of a gate's
inputs is computed, off a `2⁻ᵗ`-fraction bad set, by one fixed degree-`t(p-1)` polynomial.  Its bad set feeds the
`ApproxOn` accounting (`ComputationalDepthCircuitApprox`); the nested-`Circuit` induction threading these gate
approximations up the circuit remains the final target.
-/

open Classical

namespace PallLean.Paper93.DeepMath.PathB.GateApprox

variable {n t : ℕ}

/-- The disagreement relation: the random forms `Ss` all vanish on the input `x` (so the OR-approximator outputs
`0`) yet `x` is nonzero (so `OR(x) = 1`) — the approximator errs. -/
def disagree (p : ℕ) (Ss : Fin t → Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  (∀ j, OrApprox.linForm (fun i => ((x i).toNat : ZMod p)) (Ss j) = 0)
    ∧ (fun i => ((x i).toNat : ZMod p)) ≠ 0

/-- **A fixed good OR-approximator exists.**  Some tuple of random forms disagrees with `OR` on few inputs: the
disagreement count times the number of tuples is `≤ 2^((n-1)t) · 2ⁿ`.  Proof: per input the number of *bad*
tuples is `≤ 2^((n-1)t)` (the halving lemma via `orApproxT_disagree_count`, cancelling the `2ᵗ`), so averaging
(`exists_few_bad`) gives a fixed tuple no worse than the average. -/
theorem exists_good_forms {p : ℕ} [Fact p.Prime] (hn : 1 ≤ n) :
    ∃ Ss : Fin t → Finset (Fin n),
      (Finset.univ.filter (fun x : Fin n → Bool => disagree p Ss x)).card
        * Fintype.card (Fin t → Finset (Fin n))
      ≤ 2 ^ ((n - 1) * t) * Fintype.card (Fin n → Bool) := by
  refine Averaging.exists_few_bad (fun Ss x => disagree p Ss x)
    Finset.univ_nonempty (2 ^ ((n - 1) * t)) ?_
  intro x
  by_cases hx0 : (fun i => ((x i).toNat : ZMod p)) = 0
  · -- `x` is the all-zero vector: never a disagreement (the second conjunct fails), so the count is `0`.
    have hempty : Finset.univ.filter (fun Ss : Fin t → Finset (Fin n) => disagree p Ss x) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro Ss _
      simp [disagree, hx0]
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · -- `x` nonzero: the bad tuples are exactly those with all forms vanishing; `orApproxT_disagree_count` bounds
    -- their number by `2^(nt)/2^t = 2^((n-1)t)`.
    have hd := OrApprox.orApproxT_disagree_count t (fun i => ((x i).toNat : ZMod p)) hx0
    have hbridge :
        (Finset.univ.filter (fun Ss : Fin t → Finset (Fin n) => disagree p Ss x)).card
          = (Fintype.piFinset fun _ : Fin t =>
              Finset.univ.filter fun S =>
                OrApprox.linForm (fun i => ((x i).toNat : ZMod p)) S = 0).card := by
      congr 1
      ext Ss
      simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      exact and_iff_left hx0
    have hpow : (2 : ℕ) ^ (n * t) = 2 ^ t * 2 ^ ((n - 1) * t) := by
      have hnt : n * t = (n - 1) * t + t := by
        conv_lhs => rw [← Nat.sub_add_cancel hn]
        rw [add_mul, one_mul]
      rw [hnt, pow_add, mul_comm]
    rw [hbridge]
    rw [hpow] at hd
    exact Nat.le_of_mul_le_mul_left hd (by positivity)

end PallLean.Paper93.DeepMath.PathB.GateApprox

#print axioms PallLean.Paper93.DeepMath.PathB.GateApprox.exists_good_forms
