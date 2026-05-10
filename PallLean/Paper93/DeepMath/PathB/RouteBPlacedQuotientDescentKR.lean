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

/-- A selected strict `ConstraintType` profile-subspace datum gives the actual
paper `TΦ` P-side bound.

This is the close-out from the new placed route to the landed Route-B rank
surface: convert the selected subspace data to interface-profile data, then to
the finite local-monoid/profile package, and finally use the checked global
profile-span assembly. -/
noncomputable def routeBPaperFaithfulTPhi_pSideBound_of_strictConstraintTypeProfileSubspaceData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PallLean.Paper93.Paper283.RouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData
      M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
        M n hn2 htb hns) :=
  PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_pSideBound_of_strictCanonicalWindowLocalMonoidProfileData
    M n hn2 htb hns
    (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictCanonicalWindowLocalMonoidProfileData_of_interfaceAnonymousLocalMonoidProfileData
      M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictInterfaceAnonymousLocalMonoidProfileData_of_boundedInterfaceAnonymousLocalMonoidProfileData
        M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictBoundedInterfaceAnonymousLocalMonoidProfileData_of_constraintTypeInterfaceProfileData
          M n hn2 htb hns
          (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_strictConstraintTypeInterfaceProfileData_of_profileSubspaceData
            M n hn2 htb hns D))))

/-- The ambient strict-`TΦ` gauge P-side bound also bounds the strict coupled
same-target sheet.

The proof uses only the verified first-of-block identification and injective
rename rank preservation: the target is the unrenamed restricted sheet at the
pullback partition, while the ambient gauge is its re-expansion by the same
first-of-block rename. -/
theorem routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hP : SATDeciderGaugePSideBound M n hn2 htb hns
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
        M n hn2 htb hns)) :
    MultilinearSPDP.mlBlockedSpdpRank
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
        M n hn2 htb hns
        (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)).coupledPartition
      (Nat.log 2 n) (Nat.log 2 n)
      (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
        M n hn2 htb hns
        (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)).coupledPoly ≤
      n ^ 200 := by
  let p : MvPolynomial (Fin (n / 3)) ℚ :=
    MultilinearSPDP.restrictPoly ℚ (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n)
      (Step4Compiler.Step252.cookLevinStrictFOBFlatMap_injective n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns))
  have hrename :
      MultilinearSPDP.mlBlockedSpdpRank
          (MultilinearSPDP.pullbackPartition
            (cook_levin_compilation M n hn2 htb hns).partition
            (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n))
          (Nat.log 2 n) (Nat.log 2 n) p ≤
        MultilinearSPDP.mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n) p) :=
    PaperFaithfulCompilation.mlBlockedSpdpRank_rename_ge
      (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n) (Step4Compiler.Step252.cookLevinStrictFOBFlatMap_injective n)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) p
  have hambient :
      MultilinearSPDP.mlBlockedSpdpRank
          (cook_levin_compilation M n hn2 htb hns).partition
          (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename (Step4Compiler.Step252.cookLevinStrictFOBFlatMap n) p) ≤ n ^ 200 := by
    simpa [SATDeciderGaugePSideBound, p,
      PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge_compiledPoly_eq_reexpandedStrictFOB]
      using hP
  have hflat := hrename.trans hambient
  simpa [PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget,
    Step4Compiler.Step252.cookLevinStrictFOBTarget, p,
    Step4Compiler.Step252.cookLevinStrictFOB_pullbackPartition_eq_flat M n hn2 htb hns
      (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) rfl,
    Step4Compiler.Step252.cookLevinStrictFOB_restrict_embedded_Q_eq_restrict_compiledPoly M n hn2 htb hns]
    using hflat

/-- Target P-side rank plus the strict same-target NP lower bound closes the
paper-scale contradiction, using the target itself as the paper source in the
Theorem-207 transport inequality. -/
theorem false_of_routeBPaperFaithfulTPhi_targetPSideBound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804)
    (hn2 : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hTarget :
      MultilinearSPDP.mlBlockedSpdpRank
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
          M n hn2 htb hns
          (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)).coupledPartition
        (Nat.log 2 n) (Nat.log 2 n)
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
          M n hn2 htb hns
          (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)).coupledPoly ≤
        n ^ 200) :
    False := by
  let target := PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiTarget
    M n hn2 htb hns
    (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
  let source : GlobalGodMoveGauge.Theorem207PaperSource M n hn hn2 htb hns :=
    { sourceVars := target.coupledVars
      sourcePartition := target.coupledPartition
      sourcePoly := target.coupledPoly }
  exact
    GlobalGodMoveGauge.theorem207PaperSource_transport_false
      M n hn hn2 htb hns target source
      (by
        refine ⟨?_⟩
        simpa [source, target, GlobalGodMoveGauge.Theorem207PaperSource.spdpRank]
          using hTarget)
      (by
        refine ⟨?_⟩
        simp [source, target, GlobalGodMoveGauge.Theorem207PaperSource.spdpRank])
      (routeB_strong_np_from_same_target_identity_minor
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhi_identity_minor_data
          M n hn hn2 htb hns
          (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2) rfl))

/-- Uniform placed quotient/descent data closes the strict paper `TΦ` P-side
rank surface, without routing through the old unplaced atom-trace chart. -/
noncomputable def step247UniformRouteBPaperFaithfulTPhiPSideBound_of_placedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      SATDeciderGaugePSideBound M n hn2 htb hns
        (PallLean.Paper93.Paper283.routeBPaperFaithfulTPhiAmbientGauge
          M n hn2 htb hns) := by
  intro M n hn hn2 htb hns
  exact
    routeBPaperFaithfulTPhi_pSideBound_of_strictConstraintTypeProfileSubspaceData
      M n hn2 htb hns
      (step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
        hData M n hn hn2 htb hns)

/-- Uniform placed quotient/descent data closes the full paper-scale SAT
contradiction for the strict `TΦ` Route-B path. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent
    (hData : Step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescentData) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBPaperFaithfulTPhi_targetPSideBound M n hn hn2 htb hns
      (routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
        M n hn2 htb hns
        (step247UniformRouteBPaperFaithfulTPhiPSideBound_of_placedQuotientDescent
          hData M n hn hn2 htb hns))

/-! ## Axiom audit anchors -/

#print axioms step247UniformRouteBPaperFaithfulTPhiStrictSourceProfileSubspaceData_of_placedQuotientDescent
#print axioms step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData_of_placedQuotientDescent
#print axioms routeBPaperFaithfulTPhi_pSideBound_of_strictConstraintTypeProfileSubspaceData
#print axioms routeBPaperFaithfulTPhi_targetRank_le_of_ambientGaugePSideBound
#print axioms false_of_routeBPaperFaithfulTPhi_targetPSideBound
#print axioms step247UniformRouteBPaperFaithfulTPhiPSideBound_of_placedQuotientDescent
#print axioms noBoundedSATDeciderAtPaperScale_of_step247UniformRouteBPaperFaithfulTPhiPlacedQuotientDescent

end PallLean.Paper93.DeepMath.PathB
