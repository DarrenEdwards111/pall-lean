import PallLean.ProfileCompression
import PallLean.GodMoveReal

/-!
# The requested common-span target for the existing product compiler

This checks the actual named Lean frontier, not only a vector-space example.
For the present raw product-form compiler, the template-collapse premise
would give rank at most n^200. The existing independently proved lower bound
is strictly larger at paper scale, for every machine with the stated bounds.
Thus this particular premise cannot be discharged for this compiler.

There is no SAT-decider hypothesis in this result. It does not assert that
a different, semantically justified God-Move compiler is impossible, nor
mistake a contradiction under a hypothetical SAT decider for a refutation
of proof by contradiction. No P-versus-NP conclusion is claimed.
-/

namespace GodMoveExistingCompilerVerdict

theorem existing_product_template_collapse_false
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ WithinProfileBound.CookLevinProfileTemplateCollapseLemma M n hn2 htb hns := by
  intro hcollapse
  have hupper := ProfileCompression.p_side_rank_bound_for_cook_levin_of_templateCollapse
    M n hn2 htb hns hcollapse
  have hlower := GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n M n hn htb hns
  exact (not_le_of_gt hlower) hupper

end GodMoveExistingCompilerVerdict

#print axioms GodMoveExistingCompilerVerdict.existing_product_template_collapse_false
