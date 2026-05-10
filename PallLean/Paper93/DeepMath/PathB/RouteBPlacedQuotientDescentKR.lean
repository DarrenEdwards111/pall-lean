import PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiExtraction

/-!
# Route B placed quotient descent exposure

This file is the paper-faithful replacement for the broken atom-trace/global
chart target.  The §9.3 object is not an unplaced `X₀/X₁` chart containing the
full untouched Cook--Levin product; it is a placed local-interface expansion,
followed by quotient/descent to the interface-anonymous profile subspace
`⊗_σ Sym^{h σ}(W_σ)`.

The adapters below expose that exact surface at Step 247 scale and route it
through the already checked Paper283 placed-local quotient machinery.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Uniform paper-faithful placed quotient/descent data for strict `TΦ`.

This is the replacement theorem surface for the false unplaced background-chart
claim.  For every paper-scale Cook--Levin verifier, the row is first expanded in
actual placed local interface templates, and only then descended through the
compiled-coordinate quotient into the selected anonymous profile subspace. -/
def Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Nonempty
      (PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceSelectedRowPlacedLocalInterfaceQuotientDescentData
        M n hn2 htb hns)

/-- Uniform placed quotient/descent data gives the strict source selected
profile-subspace datum.

This is the core replacement step: placed local interface expansion plus
slotwise/product quotient descent is assembled into the selected source
`V_h = profileSubspace h W` row membership, with no fixed global chart and no
all-profile/common-span shortcut. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictSourceConstraintTypeProfileSubspaceData
        M n hn2 htb hns := by
  intro M n hn hn2 htb hns
  let D := Classical.choice (hData M n hn hn2 htb hns)
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceProfileSubspaceData_of_localCompiledProfileSubspaceRowData
      M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictSourceSelectedLocalCompiledProfileSubspaceRowData_of_placedLocalInterfaceQuotientDescentData
        M n hn2 htb hns D)

/-- Uniform placed quotient/descent data also gives the ambient strict
`ConstraintType` profile-subspace datum by the checked first-of-block rename
transport.

This is the faithful `raw traces → placed slots → quotient/profile subspace →
strict TΦ row` route.  It replaces the previous atom-trace exact chart target,
which attempted to force exact placed factors into an unplaced canonical chart. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
        M n hn2 htb hns := by
  intro M n hn hn2 htb hns
  exact
    PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictConstraintTypeProfileSubspaceData_of_sourceProfileSubspaceData
      M n hn2 htb hns
      (step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_placedQuotientDescent
        hData M n hn hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_placedQuotientDescent
#print axioms step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent

end PallLean.Paper93.DeepMath.PathB
