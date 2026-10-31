import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSwitchingUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestExtends
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PWeightExtends

/-!
# Tight switching, step 79: the subcube-relative binary descent bound (branch `razborov-recoverRho-wip`)

`descent_switching_le_tight_uncond` (the binary, `canonicalDT` descent bound) was proved with `Short := univ`,
giving the **absolute** bound (mass `1`).  Instantiating the underlying witnessed bound
(`tight_descent_switching_prob_witness`) with `Short := extBox τ` instead gives the **subcube-relative** bound,
scaled by the box mass `((1-p)/2)^(n - stars τ)` — because the deepest leaf of a `σ` extending `τ` again extends
`τ` (step 78), so it lands in `extBox τ`.  This is the relative deep-gate mass the union bound `h2_rel_clean`
(step 74) needs, finally for the *binary* `canonicalDT` the rest of the arc uses.

* `descent_switching_le_tight_extends_uncond` — `∑_{Bad ⊆ extBox τ} pweight ≤ rate^s · (2wm)^s · box`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The subcube-relative binary descent bound.**  For `Bad` extending `τ` with `canonicalDT`-depth exactly
`s`, the weight is bounded by the absolute rate times the **box mass** `((1-p)/2)^(n - stars τ)`. -/
theorem descent_switching_le_tight_extends_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] {cs : List (Clause n)} {Bad : Finset (Restriction n)}
    (τ : Fin n → Option Bool)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hext : ∀ ρ ∈ Bad, Extends τ ρ)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s * (((2 * w * m) ^ s : ℕ) : ℚ)
        * ((1 - p) / 2) ^ (n - SwitchingCounting.stars τ) := by
  have hbound := tight_descent_switching_prob_witness (Short := extBox τ) hp0 hp3
    (fun ρ hρ => mem_extBox.mpr (Extends_trans (hext ρ hρ) (deepestEnd_extends cs F ρ)))
    (fun ρ hρ => le_of_eq (hdepth ρ hρ).symm)
    (witnessReconstructionCorrect_of_depth hw hm hdepth)
  rwa [pweight_sum_extends] at hbound

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_le_tight_extends_uncond
