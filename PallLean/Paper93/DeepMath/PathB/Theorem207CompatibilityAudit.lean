import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction
import PallLean.Step4Compiler
import PallLean.PaperFaithfulSeparation

/-!
# Theorem 207 compatibility audit (strict target chain)

This module isolates the exact clash point for the current strict Route-B chain:
- P-side transported upper bound on the strict extracted target,
- NP-side same-target lower bound on the same object,
- shared paper-scale parameters `κ = ℓ = log₂ n`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation

/-- Canonical strict target alias used by the current Route-B extraction chain. -/
noncomputable abbrev StrictTarget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :=
  Step4Compiler.Step252.cookLevinStrictFOBTarget M n hn2 htb hns B_total

/-- Theorem-207 compatibility clash for the current strict target formulation:
if template-collapse transport is assumed on this chain, contradiction follows
at paper scale from same-target NP lower + arithmetic no-sandwich. -/
theorem theorem207_strict_target_incompatibility
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    (hcollapse : WithinProfileBound.CookLevinProfileTemplateCollapseLemma
      M n hn2 htb hns) :
    False :=
  Step4Compiler.Step252.DirectRankPackage_cookLevin_strictFOB_source_transport_false_from_templateCollapse
    M n hn htb hns hn2 B_total hB_total hdec hcollapse

/-- Uniform incompatibility statement (paper-scale bounded machine regime).
This is the exact Theorem-207 compatibility audit endpoint for the strict target
instantiation currently used by Route B in the repo. -/
theorem theorem207_uniform_incompatibility_strict_target
    (hcollapse :
      ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        WithinProfileBound.CookLevinProfileTemplateCollapseLemma M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact theorem207_strict_target_incompatibility
    M n hn hn2 htb hns hdec
    (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
    rfl
    (hcollapse M n hn hn2 htb hns)

#print axioms theorem207_strict_target_incompatibility
#print axioms theorem207_uniform_incompatibility_strict_target

end PallLean.Paper93.DeepMath.PathB
