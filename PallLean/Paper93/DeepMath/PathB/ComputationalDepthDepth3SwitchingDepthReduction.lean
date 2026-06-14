import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingProbTail

/-!
# Depth reduction whp: the complement of the switching tail

`hastad_switching_prob_tail` bounds the `pweight`-mass of the **bad** restrictions (canonical decision tree of depth
`≥ s`) by `(4pw/(1-p))^s`.  Since `pweight` is a probability distribution (`pweight_total`), the **complement** —
the restrictions whose canonical decision tree has depth `< s` — carries the rest of the mass:
\[
   \sum_{\sigma\notin\mathrm{Bad}} \mathrm{pweight}\,\sigma \;\ge\; 1 - \Bigl(\tfrac{4pw}{1-p}\Bigr)^{s}.
\]
A depth-`<s` decision tree is computable by both a width-`<s` DNF and a width-`<s` CNF, so on a
`1 - (4pw/(1-p))^s` fraction of restrictions the width-`w` DNF **depth-collapses to a depth-≤2 (width-`<s`) circuit**
— the single-layer depth reduction `depth 3 → depth 2` of the switching lemma, now as a probability statement.

## What is proved (clean axioms, no `sorry`)

* `switching_depth_reduction` — `1 - (4pw/(1-p))^s ≤ ∑_{σ∈Badᶜ} pweight p σ` (complement of the tail), conditional on
  the reconstruction invariant.
* `switching_depth_reduction_fullpath` — the same with `ReconstructionCorrect` discharged by the proved
  `reconstructionCorrect_fullpath`.
* `depth_collapse_mass_ge` — the explicit form: the restrictions with `(canonicalDT …).depth < s` carry mass
  `≥ 1 - (4pw/(1-p))^s`.

## Honest scope, and the `switch_step` relationship

This is the genuine probabilistic depth reduction **in the DNF model** (`canonicalDT`, `pweight`): whp the restricted
function collapses to a shallow decision tree.  `ACCDepth3Switch.switch_step` is the *deterministic* atom of the
**sibling `MOD` model** (a forced `MOD`-gate makes its clause drop from a CNF-of-`MOD`); it realises the same
"a clause/term collapses" phenomenon but in the modular layer.  A *literal* composition of the two would require a
bridge identifying `canonicalDT` depth with `MOD`-gate forcing across the two models — that bridge is separate work
and is **not** done here; I do not fake it.  The full `NEXP ⊄ ACC⁰` programme iterates this depth reduction across
all layers and composes with the `MOD` step and the Williams method.  Proves nothing about `NEXP/NP ⊄ ACC⁰` or
`P ≠ NP` on its own.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open scoped Classical
open SwitchingCounting

variable {n : ℕ}

/-- **Depth reduction whp (proved, conditional on reconstruction).**  The complement of the switching tail: the
restrictions *not* in the depth-`≥ s` bad set carry mass `≥ 1 - (4pw/(1-p))^s`. -/
theorem switching_depth_reduction {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w s F : ℕ} {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hdepth : ∀ ρ ∈ Bad, s ≤ (canonicalDT cs F ρ).depth)
    (hrec : ReconstructionCorrect cs w s F Bad) :
    1 - (4 * p * (w : ℚ) / (1 - p)) ^ s ≤ ∑ σ ∈ Badᶜ, pweight p σ := by
  have htail := hastad_switching_prob_tail hp0 hp3 hmem hdepth hrec
  have hsplit : (∑ σ ∈ Bad, pweight p σ) + ∑ σ ∈ Badᶜ, pweight p σ = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact pweight_total p
  linarith

/-- **Depth reduction whp with reconstruction discharged (proved).** -/
theorem switching_depth_reduction_fullpath {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w s F : ℕ} [NeZero w] {cs : List (Clause n)} {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hdepth : ∀ ρ ∈ Bad, s ≤ (canonicalDT cs F ρ).depth)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, anyTermSat cs (deepestEnd cs F ρ) = false)
    (hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s)
    (hpos : ∀ ρ ∈ Bad, ∀ q ∈ deepestFullSeq cs F ρ, q.1 < w) :
    1 - (4 * p * (w : ℚ) / (1 - p)) ^ s ≤ ∑ σ ∈ Badᶜ, pweight p σ :=
  switching_depth_reduction hp0 hp3 hmem hdepth
    (reconstructionCorrect_fullpath cs w s F hnf hleaf hlen hpos)

/-- **The explicit depth-collapse mass (proved, conditional on reconstruction).**  Taking the bad set to be exactly
`{ρ : depth ≥ s}`, the restrictions whose canonical decision tree has depth `< s` carry mass
`≥ 1 - (4pw/(1-p))^s` — the width-`w` DNF depth-collapses to a depth-`<s` tree (depth `≤ 2`) on almost every
restriction. -/
theorem depth_collapse_mass_ge {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w s F : ℕ} {cs : List (Clause n)}
    (hrec : ReconstructionCorrect cs w s F
      (Finset.univ.filter (fun ρ => s ≤ (canonicalDT cs F ρ).depth))) :
    1 - (4 * p * (w : ℚ) / (1 - p)) ^ s
      ≤ ∑ σ ∈ Finset.univ.filter (fun ρ => ¬ s ≤ (canonicalDT cs F ρ).depth), pweight p σ := by
  have htail := hastad_switching_prob_tail hp0 hp3
    (Bad := Finset.univ.filter (fun ρ => s ≤ (canonicalDT cs F ρ).depth)) (Short := Finset.univ)
    (fun ρ _ => Finset.mem_univ _) (fun ρ hρ => (Finset.mem_filter.mp hρ).2) hrec
  have hsplit : (∑ σ ∈ Finset.univ.filter (fun ρ => s ≤ (canonicalDT cs F ρ).depth), pweight p σ)
      + ∑ σ ∈ Finset.univ.filter (fun ρ => ¬ s ≤ (canonicalDT cs F ρ).depth), pweight p σ
      = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact pweight_total p
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.switching_depth_reduction
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.switching_depth_reduction_fullpath
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.depth_collapse_mass_ge
