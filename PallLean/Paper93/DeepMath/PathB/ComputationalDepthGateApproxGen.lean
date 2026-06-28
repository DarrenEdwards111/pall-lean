import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOrApprox
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAveraging
import Mathlib

/-!
# The general OR-gate approximation (PROVED) — the inductive step for the circuit induction

`exists_good_forms` (`ComputationalDepthGateApprox`) gave a fixed good OR-approximator for the `OR` of the `n`
*input variables*.  The nested-`Circuit` induction needs the `OR` of a *gate's children's outputs* — an arbitrary
`k`-vector of values that varies with the input.  This file proves that general form.

  `exists_good_forms_gen` — for any input space `X` and any "value-vector" map `v : X → (Fin k → 𝔽_p)` (the
        `k` children's outputs as a function of the input), there is a fixed tuple `Ss` of random forms on `Fin k`
        whose `OR`-approximator disagrees with `OR(v x)` on few inputs: `#disagree · |tuples| ≤ 2^((k-1)t) · |X|`,
        an error fraction `≤ 2⁻ᵗ`.

Applied with `X = {0,1}ⁿ`, `k` = a gate's fan-in, and `v x` = the children's (approximating-polynomial) outputs at
`x`, this is the per-`OR`-gate step of the circuit-approximation induction: each gate is approximated off a
`2⁻ᵗ`-fraction bad set, which the `ApproxOn` accounting (`ComputationalDepthCircuitApprox`) unions up the circuit.
The structural recursion threading these gate steps (with `v` the children's polynomials) is the remaining wrapper.
-/

open Classical

namespace PallLean.Paper93.DeepMath.PathB.GateApprox

variable {X : Type*} {k t : ℕ}

/-- The disagreement relation for a gate with value-vector map `v`: all forms vanish on `v x` (approximator
outputs `0`) yet `v x ≠ 0` (`OR = 1`). -/
def disagreeGen {p : ℕ} (v : X → (Fin k → ZMod p)) (Ss : Fin t → Finset (Fin k)) (x : X) : Prop :=
  (∀ j, OrApprox.linForm (v x) (Ss j) = 0) ∧ v x ≠ 0

/-- **The general OR-gate approximation.**  For any value-vector map `v : X → (Fin k → 𝔽_p)`, some fixed tuple of
random forms `Ss : Fin t → Finset (Fin k)` makes the `OR`-approximator disagree with `OR(v x)` (all forms vanish
while `v x ≠ 0`) on few inputs `x`: the disagreement count times the number of tuples is `≤ 2^((k-1)t) · |X|`.
Proof: per input, the bad-tuple count is `≤ 2^((k-1)t)` (halving lemma on `v x` via `orApproxT_disagree_count`,
cancelling `2ᵗ`); averaging (`exists_few_bad`) then yields a fixed tuple no worse than the average. -/
theorem exists_good_forms_gen [Fintype X] {p : ℕ} [Fact p.Prime] (hk : 1 ≤ k)
    (v : X → (Fin k → ZMod p)) :
    ∃ Ss : Fin t → Finset (Fin k),
      (Finset.univ.filter (fun x : X => disagreeGen v Ss x)).card
        * Fintype.card (Fin t → Finset (Fin k))
      ≤ 2 ^ ((k - 1) * t) * Fintype.card X := by
  refine Averaging.exists_few_bad (fun Ss x => disagreeGen v Ss x)
    Finset.univ_nonempty (2 ^ ((k - 1) * t)) ?_
  intro x
  by_cases hx0 : v x = 0
  · -- `v x = 0` (`OR = 0`): never a disagreement, count is `0`.
    have hempty : Finset.univ.filter (fun Ss : Fin t → Finset (Fin k) => disagreeGen v Ss x) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro Ss _
      simp [disagreeGen, hx0]
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · -- `v x ≠ 0`: bad tuples = all forms vanish; bounded by `2^((k-1)t)` via the halving lemma.
    have hd := OrApprox.orApproxT_disagree_count t (v x) hx0
    have hbridge :
        (Finset.univ.filter (fun Ss : Fin t → Finset (Fin k) => disagreeGen v Ss x)).card
          = (Fintype.piFinset fun _ : Fin t =>
              Finset.univ.filter fun S => OrApprox.linForm (v x) S = 0).card := by
      congr 1
      ext Ss
      simp only [disagreeGen, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      exact and_iff_left hx0
    have hpow : (2 : ℕ) ^ (k * t) = 2 ^ t * 2 ^ ((k - 1) * t) := by
      have hkt : k * t = (k - 1) * t + t := by
        conv_lhs => rw [← Nat.sub_add_cancel hk]
        rw [add_mul, one_mul]
      rw [hkt, pow_add, mul_comm]
    rw [hbridge]
    rw [hpow] at hd
    exact Nat.le_of_mul_le_mul_left hd (by positivity)

end PallLean.Paper93.DeepMath.PathB.GateApprox

#print axioms PallLean.Paper93.DeepMath.PathB.GateApprox.exists_good_forms_gen
