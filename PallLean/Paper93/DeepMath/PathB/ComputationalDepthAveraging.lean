import Mathlib

/-!
# The averaging argument (PROVED) — the probabilistic per-gate approximation step

The per-gate approximation in Razborov–Smolensky is *probabilistic*: `orApproxT_disagree_count`
(`ComputationalDepthOrApprox`) bounds, **for each fixed input `x`**, the number of random-form choices `Ss` on
which the `OR`-approximator errs.  To approximate a gate we need a *single fixed* choice `Ss` that errs on **few
inputs** — obtained by averaging (the probabilistic method): the average over `Ss` of the input-error count
equals the average over `x` of the `Ss`-error count, so some `Ss` does no worse than the average.

  `exists_few_bad` — given a relation `bad : S → X → Prop` with `#{s : bad s x} ≤ B` for every `x`, there is an
        `s` with `#{x : bad s x} · |S| ≤ B · |X|` — i.e. an `s` whose input-error count is at most the average
        `B·|X|/|S|`.  Proof: double-count `bad` (`card_filter` + `sum_comm`), bound by `B·|X|`, then take the
        argmin (`exists_min_image`), whose count times `|S|` is `≤` the total.

Applied with `S` = the space of random-form tuples, `X = {0,1}ⁿ`, `bad Ss x` = "`orApproxT` errs at `x`", and
`B = 2^((n-1)t)` (from `orApproxT_disagree_count`): there is a fixed tuple `Ss` whose approximator errs on
`≤ 2^(n-t)` inputs — a `2⁻ᵗ` fraction.  That fixed approximator is the per-gate polynomial; its bad set feeds the
circuit-approximation accounting (`ComputationalDepthCircuitApprox`).
-/

namespace PallLean.Paper93.DeepMath.PathB.Averaging

open Classical in
/-- **The averaging argument (probabilistic method).**  If for every `x` at most `B` of the `s ∈ S` are "bad" for
`x`, then some `s` is bad for at most an average number of `x`: `#{x : bad s x} · |S| ≤ B · |X|`.  Proof:
double-count the bad pairs, bound the total by `B·|X|`, and take the `s` minimising the input-error count — its
count times `|S|` is at most the total. -/
theorem exists_few_bad {S X : Type*} [Fintype S] [Fintype X] (bad : S → X → Prop)
    (hS : (Finset.univ : Finset S).Nonempty) (B : ℕ)
    (hbad : ∀ x, (Finset.univ.filter (fun s => bad s x)).card ≤ B) :
    ∃ s : S, (Finset.univ.filter (fun x => bad s x)).card * Fintype.card S ≤ B * Fintype.card X := by
  -- double counting: Σ_s #{x : bad s x} = Σ_x #{s : bad s x}
  have hfub : ∑ s : S, (Finset.univ.filter (fun x => bad s x)).card
      = ∑ x : X, (Finset.univ.filter (fun s => bad s x)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  -- the total is at most B · |X|
  have htot : ∑ s : S, (Finset.univ.filter (fun x => bad s x)).card ≤ B * Fintype.card X := by
    rw [hfub]
    calc ∑ x : X, (Finset.univ.filter (fun s => bad s x)).card
        ≤ ∑ _x : X, B := Finset.sum_le_sum (fun x _ => hbad x)
      _ = B * Fintype.card X := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  -- take the argmin: its count times |S| is at most the total
  obtain ⟨s, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun s => (Finset.univ.filter (fun x => bad s x)).card) hS
  refine ⟨s, ?_⟩
  have hmincard : (Finset.univ.filter (fun x => bad s x)).card * Fintype.card S
      ≤ ∑ s' : S, (Finset.univ.filter (fun x => bad s' x)).card := by
    rw [← Finset.card_univ, mul_comm]
    calc (Finset.univ : Finset S).card * (Finset.univ.filter (fun x => bad s x)).card
        = ∑ _s' ∈ Finset.univ, (Finset.univ.filter (fun x => bad s x)).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ s' : S, (Finset.univ.filter (fun x => bad s' x)).card :=
          Finset.sum_le_sum (fun s' _ => hmin s' (Finset.mem_univ s'))
  exact le_trans hmincard htot

end PallLean.Paper93.DeepMath.PathB.Averaging

#print axioms PallLean.Paper93.DeepMath.PathB.Averaging.exists_few_bad
