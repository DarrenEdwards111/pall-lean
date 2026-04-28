import PallLean.Step4Compiler

/-!
# Route B paper-faithful `TΦ` extraction

The paper's Route B extraction is not the broad multilinear-tail complement.
It is the explicit coupled-sheet map

`TΦ = basis ◦ affine relabel ◦ restriction ◦ projection`.

In the current formal development, the concrete checked instance of that
pipeline is the strict first-of-block coupled-sheet extraction from
`Step4Compiler`: restrict the ambient `embedded_Q` sheet along the strict
first-of-block map, identify it with the flat Cook-Levin restriction, and use
the canonical projection/relabel rank comparison.  This file gives that object
the Route B `TΦ` names and packages the two facts Route B actually needs:

* extraction/rank transfer to the coupled target;
* same-target identity-minor data on that target.

It deliberately does not route through the old broad head-span complement.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler.Step252

attribute [local instance] Classical.dec

/-- The concrete paper-faithful `TΦ` coordinate map used by the strict
coupled-sheet extraction. -/
noncomputable abbrev routeBPaperFaithfulTPhiMap
    (M : DTM) (n : ℕ) :
    Fin (n / 3) → Fin (PaperFaithfulCompilation.cookLevinUVSplit M n).total :=
  cookLevinStrictFOBMap M n

/-- The `TΦ` coordinate map is injective, so it defines an honest restriction
and pullback partition. -/
theorem routeBPaperFaithfulTPhiMap_injective
    (M : DTM) (n : ℕ) :
    Function.Injective (routeBPaperFaithfulTPhiMap M n) :=
  cookLevinStrictFOBMap_injective M n

/-- The paper-faithful coupled-sheet target extracted by `TΦ`. -/
noncomputable def routeBPaperFaithfulTPhiTarget
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    GodMoveExtractionTarget M n hn2 htb hns :=
  cookLevinStrictFOBTarget M n hn2 htb hns B_total

/-- The strict `TΦ` target polynomial is exactly the strict restriction of the
ambient embedded coupled sheet. -/
theorem routeBPaperFaithfulTPhiTarget_coupledPoly_eq
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total) :
    (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total).coupledPoly =
      MultilinearSPDP.restrictPoly ℚ (routeBPaperFaithfulTPhiMap M n)
        (routeBPaperFaithfulTPhiMap_injective M n)
        (Step4Compiler.Step247.partitioned_output_cookLevin
          M n hn2 htb hns).embedded_Q := by
  rfl

/-- The strict embedded-sheet restriction agrees with the flat Cook-Levin
first-of-block restriction.  This is the pointwise polynomial identity behind
the projected P-window row identity for this concrete `TΦ` target. -/
theorem routeBPaperFaithfulTPhi_restrict_embedded_Q_eq_restrict_compiledPoly
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MultilinearSPDP.restrictPoly ℚ (routeBPaperFaithfulTPhiMap M n)
        (routeBPaperFaithfulTPhiMap_injective M n)
        (Step4Compiler.Step247.partitioned_output_cookLevin M n hn2 htb hns).embedded_Q =
      MultilinearSPDP.restrictPoly ℚ (cookLevinStrictFOBFlatMap n)
        (cookLevinStrictFOBFlatMap_injective n)
        (PaperFaithfulSeparation.compiledPoly
          (PaperFaithfulSeparation.cook_levin_compilation
            M n hn2 htb hns)) := by
  simpa [routeBPaperFaithfulTPhiMap] using
    cookLevinStrictFOB_restrict_embedded_Q_eq_restrict_compiledPoly
      M n hn2 htb hns

/-- Canonical projection/relabel rank monotonicity for the paper-faithful
`TΦ` target. -/
theorem routeBPaperFaithfulTPhi_canonical_projection_stage
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    CookLevinStrictFOBCanonicalProjectionStage
      M n hn2 htb hns B_total hB_total :=
  cookLevinStrictFOBCanonicalProjectionStage
    M n hn2 htb hns B_total hB_total

/-- The concrete `TΦ` extraction gives the Route B extraction/rank transfer
for the strict coupled-sheet target. -/
theorem routeBPaperFaithfulTPhi_extraction_transfer
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    PaperFaithfulSeparation.GodMoveRouteB_ExtractionObligation
      M n hn2 htb hns hdec
      (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) := by
  change
    PaperFaithfulSeparation.GodMoveRouteB_ExtractionObligation
      M n hn2 htb hns hdec
      (cookLevinStrictFOBTarget M n hn2 htb hns B_total)
  exact
    cookLevinStrictFOB_routeB_extraction_transfer
      M n hn2 htb hns hdec B_total hB_total

/-- The same strict `TΦ` target carries the Route B identity-minor lower-bound
data. -/
def routeBPaperFaithfulTPhi_identity_minor_data
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    PaperFaithfulSeparation.RouteBIdentityMinorSameTargetData
      (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) :=
  cookLevinStrictFOBTarget_identity_minor_data
    M n hn hn2 htb hns B_total hB_total

/-- The strict `TΦ` target provides both corrected Route B target facts on the
same coupled sheet: extraction transfer and identity-minor data. -/
theorem routeBPaperFaithfulTPhi_extraction_and_identity_minor
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (B_total : SPDP.BlockPartition
      (PaperFaithfulCompilation.cookLevinUVSplit M n).total)
    (hB_total : B_total =
      PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) :
    PaperFaithfulSeparation.GodMoveRouteB_ExtractionObligation
        M n hn2 htb hns hdec
        (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total) ∧
      Nonempty
        (PaperFaithfulSeparation.RouteBIdentityMinorSameTargetData
          (routeBPaperFaithfulTPhiTarget M n hn2 htb hns B_total)) :=
  ⟨routeBPaperFaithfulTPhi_extraction_transfer
      M n hn2 htb hns hdec B_total hB_total,
    ⟨routeBPaperFaithfulTPhi_identity_minor_data
      M n hn hn2 htb hns B_total hB_total⟩⟩

/-! ## Axiom audit anchors -/

#print axioms routeBPaperFaithfulTPhiMap_injective
#print axioms routeBPaperFaithfulTPhi_restrict_embedded_Q_eq_restrict_compiledPoly
#print axioms routeBPaperFaithfulTPhi_canonical_projection_stage
#print axioms routeBPaperFaithfulTPhi_extraction_transfer
#print axioms routeBPaperFaithfulTPhi_identity_minor_data
#print axioms routeBPaperFaithfulTPhi_extraction_and_identity_minor

end PallLean.Paper93.Paper283
