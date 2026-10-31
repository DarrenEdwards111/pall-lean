import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSwitchingProb
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PNormalize

/-!
# Tight switching, step 5: the tight weighted switching bound (branch `razborov-recoverRho-wip`)

The tight analogue of `descent_switching_le` (brick 60), with the cap `(4^w+1)^F` replaced by `(2w)^s`.
For a "good" bad set — restrictions of canonical-tree depth exactly `s` that falsify no term (`hnf`),
whose deepest leaf rejects (`hleaf`), with positions `< w` (`hpos`) — the p-biased weight is at most
`(2p/(1-p))^s · (2w)^s`.  This is `tight_descent_switching_prob` (step 2) with `Short = univ` (so the
boundary sum is `1`) and the reconstruction discharged by the sorry-free `reconstructionCorrect_fullpath`.

* `descent_switching_le_tight` — `∑_{Bad} pweight σ ≤ (2p/(1-p))^s · (2w)^s`.

This is the per-shell weighted count `exists_shallow_all_tight` consumes (summed over depth shells and
union-bounded over gates), with the depth-indexed `(2w)^s` cap that makes the depth-3 budget satisfiable.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The tight weighted switching bound.**  For a depth-`s`, term-alive, leaf-rejecting bad set with
positions `< w`, the p-biased weight is at most `(2p/(1-p))^s · (2w)^s`. -/
theorem descent_switching_le_tight {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w s F : ℕ} [NeZero w] {cs : List (Clause n)} {Bad : Finset (Restriction n)}
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ q ∈ deepestFullSeq cs F ρ, q.1 < w) :
    (∑ σ ∈ Bad, pweight p σ) ≤ (2 * p / (1 - p)) ^ s * (((2 * w) ^ s : ℕ) : ℚ) := by
  have hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s :=
    fun ρ hρ => (deepestFullSeq_length_eq_depth cs F ρ).trans (hdepth ρ hρ)
  have hrec := reconstructionCorrect_fullpath cs w s F hnf hleaf hlen hpos
  have hbound := tight_descent_switching_prob (Short := (Finset.univ : Finset (Restriction n)))
    hp0 hp3 (fun ρ _ => Finset.mem_univ _) (fun ρ hρ => le_of_eq (hdepth ρ hρ).symm) hrec
  rwa [pweight_sum_eq_one, mul_one] at hbound

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_le_tight
