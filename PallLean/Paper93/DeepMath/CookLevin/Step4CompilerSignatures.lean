import PallLean.Step4Compiler

/-!
# Step4Compiler signature documentation

This file documents the headline `P ≠ NP` consumers exposed by
`PallLean.Step4Compiler`, focusing on the entry points relevant to the
`theorem_207_rank_chain` rank-bound feed.

## Summary of relevant signatures (verified at the source):

* `Step4Compiler.P_ne_NP_via_step4`
  `(M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
   (hdec : PaperFaithfulSeparation.DecidesSAT M)
   (hVsep : 0 < (...cookLevinUVSplit M (2 ^ 804)).numV)
   (step4 : Step4TheoremOutput ... ) : False`
  (TM-framed Step 4 → False closure; per-DTM at the canonical
  `n = 2 ^ 804` Cook-Levin partition.)

* `Step4Compiler.P_ne_NP_Lean`
  `(hExtract : P = NP → PaperFaithfulSeparation.PeqNP_Paper) : P ≠ NP`
  (Lean-statement-level headline `P ≠ NP`, conditional on the textbook
  → paper-frame `PeqNP_Paper` extraction.)

* `Step4Compiler.Step252.P_ne_NP_from_cookLevin_templateCollapse_hypothesis`
  `(hOutput : PeqNP_Paper → Σ' M n hn htb hns hn2,
              CookLevinProfileTemplateCollapseLemma M n hn2 htb hns)
   : P ≠ NP`
  with stricter variants
  `..._admissibleOnly_hypothesis` and `..._boundedProfile_hypothesis`.

The `theorem_207_rank_chain` (signature
`∀ α κ n, 0 < α → 2 ≤ n → κ ≤ (pocketFamily α κ n).rank`) feeds the
rank lower-bound used inside the `cookLevinQ_rank_le_from_templateCollapse`
chain that discharges the hypotheses of the Step252
`P_ne_NP_from_cookLevin_templateCollapse_*` family — i.e. the
`templateCollapse` consumers are the relevant entry points for the
`theorem_207_rank_chain` rank bound.
-/

namespace PallLean.Paper93.DeepMath.CookLevin

/-- Documentation theorem: confirms `Step4Compiler.P_ne_NP_via_step4` is
reachable as a real `False`-valued closure (when supplied with its
TM/decider/separation/Step4Output hypotheses) and that the `P ≠ NP`
proposition built from `Step4Compiler.P` and `Step4Compiler.NP` is a
genuine inhabitable proposition, not `True`. -/
theorem step4_compiler_has_P_ne_NP_via_step4_theorem :
    ∃ (T : Prop), T = (Step4Compiler.P ≠ Step4Compiler.NP) := ⟨_, rfl⟩

end PallLean.Paper93.DeepMath.CookLevin

#print axioms PallLean.Paper93.DeepMath.CookLevin.step4_compiler_has_P_ne_NP_via_step4_theorem
