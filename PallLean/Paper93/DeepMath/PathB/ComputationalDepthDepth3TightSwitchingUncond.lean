import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSwitchingProb
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PNormalize

/-!
# Tight switching, step 31: the unconditional tight weighted bound — `hnf`/`hleaf`/`hpos` DROPPED (branch `razborov-recoverRho-wip`)

The mechanical substitution.  `descent_switching_le_tight` (brick 09) proved
`∑_{Bad} pweight ≤ (2p/(1-p))^s·(2w)^s` but required `hnf` (alive), `hleaf`, `hpos` — the empty-skip wall.
Replacing its `ReconstructionCorrect`/`PathLabel` injection by the witnessed one (`WitLabel w s m`,
discharged with **no `hnf`/`hleaf`/`hpos`** by the active-clause+position witness, bricks 63–70) gives the
unconditional bound

```
  ∑_{Bad} pweight p σ ≤ (2p/(1-p))^s · (2·w·m)^s,
```

over `Bad = {depth = s}`, needing only the width bound `hw` and the clause-count bound `hm` (`m ≥ |cs|`).
`F`-independent; the empty-skip wall is gone.

* `witnessReconstructionCorrect_of_depth` — the `hnf`-free witnessed reconstruction (extracted).
* `deepest_switching_weighted_of_witness` — the weighted label half over `WitLabel` (`(2wm)^s`).
* `tight_descent_switching_prob_witness` — the witnessed tight p-biased bound.
* `descent_switching_le_tight_uncond` — the unconditional tight weighted cap.

## Honest scope

This is `descent_switching_le_tight` with the empty-skip hypotheses removed, at cap `(2wm)^s` (vs `(2w)^s`;
`m^s` overhead, `F`-independent).  Propagating it through `tight_switching_budget` / `exists_shallow_all_tight`
/ the collapse + parity arc (bricks 50–62) — each a rewrite of the cap and a drop of the alive hypotheses —
makes the depth-`d` `parity ∉ AC⁰` unconditional (the AC⁰ ceiling).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The `hnf`-free witnessed reconstruction (the `⟨lab, D, correct⟩` of brick 70, extracted). -/
theorem witnessReconstructionCorrect_of_depth {w F s m : ℕ} [NeZero w] [NeZero m]
    {cs : List (Clause n)} {Bad : Finset (Restriction n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s) :
    WitnessReconstructionCorrect cs w s F m Bad := by
  refine ⟨fun ρ => flatToWitLabel w s m (deepestWitSeq cs F ρ),
    fun _ wl => witDecode cs ((List.ofFn wl).map finToWit), ?_⟩
  intro ρ hρ
  show witDecode cs (List.map finToWit (List.ofFn
    (flatToWitLabel w s m (deepestWitSeq cs F ρ)))) = deepestSel cs F ρ
  have hlen : (deepestWitSeq cs F ρ).length = s :=
    (deepestWitSeq_length_eq_depth cs F ρ).trans (hdepth ρ hρ)
  have hb : ∀ pc ∈ deepestWitSeq cs F ρ, pc.1 < w ∧ pc.2 < m := fun pc hpc =>
    ⟨(deepestWitSeq_bounds cs hw F ρ pc hpc).1,
     lt_of_lt_of_le (deepestWitSeq_bounds cs hw F ρ pc hpc).2 hm⟩
  rw [map_finToWit_flatToWitLabel (deepestWitSeq cs F ρ) hlen hb, witDecode_deepestWitSeq]

/-- **The weighted label half over the witness label.**  The deepest-end weight over `Bad` is at most
`(2wm)^s` times the weight over `Short`, via the witnessed injection `σ ↦ (deepestEnd σ, lab σ)`. -/
theorem deepest_switching_weighted_of_witness {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {w s F m : ℕ} {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hrec : WitnessReconstructionCorrect cs w s F m Bad) :
    (∑ σ ∈ Bad, pweight p (deepestEnd cs F σ))
      ≤ (((2 * w * m) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ := by
  classical
  obtain ⟨lab, D, hdec⟩ := hrec
  set g : Restriction n → (Restriction n × WitLabel w s m) :=
    fun σ => (deepestEnd cs F σ, lab σ) with hg
  have hginj : Set.InjOn g Bad := by
    intro ρ hρ σ hσ heq
    simp only [hg, Prod.mk.injEq] at heq
    obtain ⟨hE, hlab⟩ := heq
    have h1 : D (deepestEnd cs F ρ) (lab ρ) = D (deepestEnd cs F σ) (lab σ) := by rw [hE, hlab]
    rw [hdec ρ hρ, hdec σ hσ] at h1
    exact deepestEnd_inj cs F hE h1
  have heq1 : (∑ σ ∈ Bad, pweight p (deepestEnd cs F σ)) = ∑ q ∈ Bad.image g, pweight p q.1 := by
    rw [Finset.sum_image hginj]
  rw [heq1]
  calc (∑ q ∈ Bad.image g, pweight p q.1)
      ≤ ∑ q ∈ Short ×ˢ (Finset.univ : Finset (WitLabel w s m)), pweight p q.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rw [Finset.mem_image] at hq
          obtain ⟨σ, hσ, rfl⟩ := hq
          rw [Finset.mem_product]
          exact ⟨hmem σ hσ, Finset.mem_univ _⟩
        · exact fun q _ _ => pweight_nonneg hp0 hp1 q.1
    _ = (((2 * w * m) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ := by
        rw [Finset.sum_product]
        have hcard : (Finset.univ : Finset (WitLabel w s m)).card = (2 * w * m) ^ s := by
          rw [Finset.card_univ, card_witLabels]
        simp only [Finset.sum_const, hcard, nsmul_eq_mul]
        rw [← Finset.mul_sum]

/-- **The witnessed tight p-biased bound.**  As `tight_descent_switching_prob`, but over the witness label
`(2wm)^s` — no `hnf`/`hleaf`/`hpos`. -/
theorem tight_descent_switching_prob_witness {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w s F m : ℕ} {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hdepth : ∀ ρ ∈ Bad, s ≤ (canonicalDT cs F ρ).depth)
    (hrec : WitnessReconstructionCorrect cs w s F m Bad) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s * (((2 * w * m) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ := by
  have hp1 : p ≤ 1 := by linarith
  have hr_nonneg : 0 ≤ (2 * p / (1 - p)) ^ s := by
    have : (0 : ℚ) < 1 - p := by linarith
    positivity
  calc (∑ σ ∈ Bad, pweight p σ)
      ≤ ∑ σ ∈ Bad, (2 * p / (1 - p)) ^ s * pweight p (deepestEnd cs F σ) := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact pweight_le_ratio_pow_deepestEnd hp0 hp3 cs F s σ (hdepth σ hσ)
    _ = (2 * p / (1 - p)) ^ s * ∑ σ ∈ Bad, pweight p (deepestEnd cs F σ) := by rw [Finset.mul_sum]
    _ ≤ (2 * p / (1 - p)) ^ s * ((((2 * w * m) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ) := by
        exact mul_le_mul_of_nonneg_left
          (deepest_switching_weighted_of_witness hp0 hp1 hmem hrec) hr_nonneg
    _ = (2 * p / (1 - p)) ^ s * (((2 * w * m) ^ s : ℕ) : ℚ) * ∑ τ ∈ Short, pweight p τ := by
        ring

/-- **The unconditional tight weighted switching bound.**  `descent_switching_le_tight` with the empty-skip
hypotheses (`hnf`/`hleaf`/`hpos`) dropped: for `Bad` of depth exactly `s`, with active terms width-`≤ w` and
clause count `≤ m`, the p-biased weight is at most `(2p/(1-p))^s·(2wm)^s`. -/
theorem descent_switching_le_tight_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] {cs : List (Clause n)} {Bad : Finset (Restriction n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s) :
    (∑ σ ∈ Bad, pweight p σ) ≤ (2 * p / (1 - p)) ^ s * (((2 * w * m) ^ s : ℕ) : ℚ) := by
  have hbound := tight_descent_switching_prob_witness
    (Short := (Finset.univ : Finset (Restriction n))) hp0 hp3
    (fun ρ _ => Finset.mem_univ _) (fun ρ hρ => le_of_eq (hdepth ρ hρ).symm)
    (witnessReconstructionCorrect_of_depth hw hm hdepth)
  rwa [pweight_sum_eq_one, mul_one] at hbound

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_le_tight_uncond
