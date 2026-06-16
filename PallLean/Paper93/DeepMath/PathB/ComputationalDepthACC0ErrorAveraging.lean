import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ProbabilisticAmplification

/-!
# The error-averaging bridge — from per-input seed error to a fixed good seed

The degree side was discharged by `…ACC0AevalDegree` (composition raises degree by `≤ δ`).  The error side has two
pieces: the **composition** (the union bound over gates, already proved as `…ACC0CircuitSubstitution.circuit_error_bound`,
total error `≤ size·ε`) and the **per-gate error** itself.  The proved gate errors (`orPoly_error`,
`amplifiedOrPoly_error`) live in *seed* space — they bound, for each fixed input, the fraction of random seeds on which
the gate polynomial errs.  But `circuit_error_bound` needs a *fixed* approximant whose error is bounded in *input*
space.  The bridge is the probabilistic method: averaging the per-input seed-error over seeds produces a single seed
whose total input-error is at most the average.

This file proves that bridge — the genuine error-side analogue of the composition-degree lemma.

## What is proved (clean axioms, no `sorry`)

* **`exists_below_average`** — for `g : ι → ℕ` over a nonempty finite `ι`, some `i` has
  `(card ι)·g i ≤ ∑ⱼ g j` (a value at or below the average; the argmin).
* **`exists_good_seed`** — if every input is erred on by at most `k` seeds
  (`∀ x, #{s : err s x} ≤ k`), then some seed `s` errs on few inputs:
  `(card Seed)·#{x : err s x} ≤ (card Input)·k`.  (Fubini `∑_s #{x} = ∑_x #{s}`, then `exists_below_average`.)

## How it wires the error side

For the amplified `OR` gate, `amplifiedOrPoly_error` gives, per fixed input `v`, a `(1/p)^t` fraction of seeds in
error — i.e. `#{seeds : err} = (card Seed)/p^t =: k`.  Then `exists_good_seed` produces a fixed seed with input-error
`≤ (card Input)·k / card Seed = 2^n / p^t`.  That `2^n/p^t` is the per-gate `ε` consumed by
`circuit_error_bound` (total error `≤ size·ε`); with `p^t > 10·size` (the `error_choice` calibration) the whole
circuit errs on `< 2^n/10` inputs.

## Honest scope

The averaging bridge is *proved*, generically.  It converts the proved seed-space gate errors into the fixed-seed
input-space `ε` that `circuit_error_bound` consumes — the error-side counterpart of the degree discharge.  The
concrete instantiation (`k = card Seed / p^t` from `amplifiedOrPoly_error`) is `ℕ`-division bookkeeping; the abstract
`williams`/`hierarchy` Props remain the named Route-B sockets.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ErrorAveraging

open scoped Classical BigOperators
open Finset

/-- **Below-average existence (proved): some index is at or below the average.**  For `g : ι → ℕ` over a nonempty
finite `ι`, the argmin `i` satisfies `(card ι)·g i ≤ ∑ⱼ g j`. -/
theorem exists_below_average {ι : Type*} [Fintype ι] [Nonempty ι] (g : ι → ℕ) :
    ∃ i, (Fintype.card ι) * g i ≤ ∑ j, g j := by
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc (Fintype.card ι) * g i = ∑ _j : ι, g i := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ j, g j := Finset.sum_le_sum (fun j _ => hi j (Finset.mem_univ j))

/-- **The error-averaging bridge (proved): a per-input seed-error bound yields a fixed good seed.**  If every input is
erred on by at most `k` seeds, then some seed errs on few inputs: `(card Seed)·#{x : err s x} ≤ (card Input)·k`.  This
converts the seed-space gate error (`orPoly_error`/`amplifiedOrPoly_error`) into the fixed-seed input-space error that
`circuit_error_bound` consumes. -/
theorem exists_good_seed {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
    (err : S → I → Prop) [∀ s i, Decidable (err s i)] (k : ℕ)
    (hbound : ∀ x : I, (Finset.univ.filter (fun s => err s x)).card ≤ k) :
    ∃ s : S, (Fintype.card S) * (Finset.univ.filter (fun x => err s x)).card
      ≤ (Fintype.card I) * k := by
  have hfubini : ∑ s : S, (Finset.univ.filter (fun x => err s x)).card ≤ (Fintype.card I) * k := by
    have hcomm : ∑ s : S, (Finset.univ.filter (fun x => err s x)).card
        = ∑ x : I, (Finset.univ.filter (fun s => err s x)).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hcomm]
    calc ∑ x : I, (Finset.univ.filter (fun s => err s x)).card
        ≤ ∑ _x : I, k := Finset.sum_le_sum (fun x _ => hbound x)
      _ = (Fintype.card I) * k := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  obtain ⟨s, hs⟩ := exists_below_average (fun s => (Finset.univ.filter (fun x => err s x)).card)
  exact ⟨s, le_trans hs hfubini⟩

end PallLean.Paper93.DeepMath.PathB.ACC0ErrorAveraging

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ErrorAveraging.exists_below_average
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ErrorAveraging.exists_good_seed
