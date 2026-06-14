import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSwitchingProb
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingCount

/-!
# Connecting the switching decoder arc to a genuine probability tail

The decoder arc proves the **weighted** switching bound `tight_descent_switching_prob`:
\[
   \sum_{\sigma\in\mathrm{Bad}} \mathrm{pweight}\,\sigma
     \;\le\; \Bigl(\tfrac{2p}{1-p}\Bigr)^{s}\,(2w)^{s}\,\sum_{\tau\in\mathrm{Short}}\mathrm{pweight}\,\tau ,
\]
with the `(2w)^s` factor coming from the proved injective path‑label encoding and the `(2p/(1-p))^s` factor from the
per‑restriction weight gain.  What was missing to turn this into an actual **probability tail** was the elementary
but essential fact that `pweight` is a *probability distribution* on restrictions — `∑_ρ pweight p ρ = 1` — so that
`∑_{Short} pweight ≤ 1` and the bound becomes the recognisable Håstad form.

This file supplies that link:

* `pweight_total` — `∑_{ρ : Fin n → Option Bool} pweight p ρ = 1` (the per‑coordinate weights `p + (1-p)/2 + (1-p)/2`
  sum to `1`, so the product distribution has total mass `1`; via `Finset.prod_univ_sum`).
* `pweight_le_one` — any partial sum `∑_{Short} pweight ≤ 1` (nonnegativity + total mass).
* `hastad_switching_prob_tail` — **`∑_{Bad} pweight p σ ≤ (4·p·w/(1-p))^s`**, the clause‑count‑free Håstad switching
  tail (probability that the canonical decision tree has depth `≥ s`), conditional on the reconstruction invariant
  `ReconstructionCorrect`.
* `hastad_switching_prob_tail_fullpath` — the same bound with `ReconstructionCorrect` **discharged** by the proved
  `reconstructionCorrect_fullpath`, i.e. unconditional given the concrete deepest‑descent hypotheses on `Bad`.

For `3p ≤ 1` (so `1-p ≥ 2/3`) this is `≤ (6pw)^s`, the standard `(O(pw))^s` decay: the probability that a width‑`w`
DNF/CNF needs canonical decision‑tree depth `≥ s` under a `p`‑random restriction decays **exponentially in `s` with
no dependence on the number of clauses** — the hallmark of Håstad's switching lemma that the gate‑survival tail
(`…ACC0SatExpTail`) provably could *not* achieve (its `C(k,t)` clause‑count factor).

## Honest scope

This is the genuine clause‑count‑free switching tail, in the depth‑3 DNF/CNF model the arc formalises, for the
canonical deepest‑descent decision tree.  `hastad_switching_prob_tail_fullpath`'s hypotheses (`hnf`, `hleaf`,
`hlen`, `hpos`) characterise `Bad` as the depth‑`≥ s` set under width‑`w` clauses via the canonical descent; they are
the concrete combinatorial conditions the proved `reconstructionCorrect_fullpath` consumes.  The full
`NEXP ⊄ ACC⁰` programme needs this tail *iterated across depth and composed with the MOD‑gate switching step*
(`ACCDepth3Switch.switch_step`) and the Williams algorithmic method; those compositions are separate.  Still a
lower‑bound‑machinery result; it proves nothing about `NEXP/NP ⊄ ACC⁰` or `P ≠ NP` on its own.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-! ## `pweight` is a probability distribution -/

/-- **Total mass `1` (proved): `∑_ρ pweight p ρ = 1`.**  The sum over all restrictions of the product weight
factorises (`Finset.prod_univ_sum`) into a product over coordinates of the per‑coordinate mass
`p + (1-p)/2 + (1-p)/2 = 1`. -/
theorem pweight_total (p : ℚ) : ∑ ρ : Fin n → Option Bool, pweight p ρ = 1 := by
  have key : (∏ _i : Fin n, ∑ j : Option Bool, (if j = none then p else (1 - p) / 2))
      = ∑ ρ : Fin n → Option Bool, pweight p ρ := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  rw [← key]
  apply Finset.prod_eq_one
  intro i _
  rw [Fintype.sum_option, Fintype.sum_bool]
  simp only [reduceCtorEq, if_false, if_true]
  ring

/-- **Any partial mass is `≤ 1` (proved).** -/
theorem pweight_le_one {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Short : Finset (Fin n → Option Bool)) :
    ∑ τ ∈ Short, pweight p τ ≤ 1 := by
  calc ∑ τ ∈ Short, pweight p τ
      ≤ ∑ τ : Fin n → Option Bool, pweight p τ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun τ _ _ => pweight_nonneg hp0 hp1 τ)
    _ = 1 := pweight_total p

/-! ## The Håstad switching probability tail -/

/-- **The clause‑count‑free switching tail (proved, conditional on reconstruction).**
`∑_{σ∈Bad} pweight p σ ≤ (4·p·w/(1-p))^s`: the `p`‑biased probability mass of the restrictions whose canonical
decision tree has depth `≥ s` decays as `(O(p·w))^s`, with **no dependence on the number of clauses**.  This is
`tight_descent_switching_prob` with the `Short`‑mass bounded by the total mass `1` (`pweight_le_one`). -/
theorem hastad_switching_prob_tail {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w s F : ℕ} {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hdepth : ∀ ρ ∈ Bad, s ≤ (canonicalDT cs F ρ).depth)
    (hrec : ReconstructionCorrect cs w s F Bad) :
    ∑ σ ∈ Bad, pweight p σ ≤ (4 * p * (w : ℚ) / (1 - p)) ^ s := by
  have h1p : (0 : ℚ) < 1 - p := by linarith
  have h1p' : (1 : ℚ) - p ≠ 0 := h1p.ne'
  have hbase : (0 : ℚ) ≤ 2 * p / (1 - p) := div_nonneg (by linarith) (by linarith)
  have hcoef : (0 : ℚ) ≤ (2 * p / (1 - p)) ^ s * (((2 * w) ^ s : ℕ) : ℚ) :=
    mul_nonneg (pow_nonneg hbase s) (by positivity)
  have hshort : ∑ τ ∈ Short, pweight p τ ≤ 1 := pweight_le_one hp0 (by linarith) Short
  calc ∑ σ ∈ Bad, pweight p σ
      ≤ (2 * p / (1 - p)) ^ s * (((2 * w) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ :=
        tight_descent_switching_prob hp0 hp3 hmem hdepth hrec
    _ ≤ (2 * p / (1 - p)) ^ s * (((2 * w) ^ s : ℕ) : ℚ) * 1 :=
        mul_le_mul_of_nonneg_left hshort hcoef
    _ = (4 * p * (w : ℚ) / (1 - p)) ^ s := by
        rw [mul_one]
        push_cast
        rw [← mul_pow]
        congr 1
        field_simp
        ring

/-- **The switching tail with reconstruction discharged (proved).**  Combining `hastad_switching_prob_tail` with the
proved `reconstructionCorrect_fullpath`: for the canonical deepest‑descent bad set of a width‑`w` DNF/CNF
(`hnf`/`hleaf`/`hlen`/`hpos`), the depth‑`≥ s` probability mass is `≤ (4·p·w/(1-p))^s` — no clause‑count factor and
no remaining reconstruction hypothesis. -/
theorem hastad_switching_prob_tail_fullpath {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w s F : ℕ} [NeZero w] {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hdepth : ∀ ρ ∈ Bad, s ≤ (canonicalDT cs F ρ).depth)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, anyTermSat cs (deepestEnd cs F ρ) = false)
    (hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s)
    (hpos : ∀ ρ ∈ Bad, ∀ q ∈ deepestFullSeq cs F ρ, q.1 < w) :
    ∑ σ ∈ Bad, pweight p σ ≤ (4 * p * (w : ℚ) / (1 - p)) ^ s :=
  hastad_switching_prob_tail hp0 hp3 hmem hdepth
    (reconstructionCorrect_fullpath cs w s F hnf hleaf hlen hpos)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweight_total
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hastad_switching_prob_tail
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hastad_switching_prob_tail_fullpath
