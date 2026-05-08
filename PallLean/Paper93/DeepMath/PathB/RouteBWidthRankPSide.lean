import PallLean.Paper93.DeepMath.PathB.RouteBExtractionMove
import PallLean.Paper93.DeepMath.PathB.ProjectedPSideBoundFrontier

/-!
# Route B P-side Width⇒Rank closure surface

This file isolates the paper-faithful P-side move needed after the `T_Φ`
extraction sandwich:

* the P-side bound is on the **full Step247 compiler output**;
* it is discharged by a genuine §40.2 Theorem 216 Khatri--Rao spanning-set
  witness (`Theorem216SpanningSet`) plus the paper's absolute-constant
  digitisation `C₃ ≤ 2^199`;
* no `ProfileMatches` reverse bridge, additive clause sheet, global `Wσ`
  collapse, or `spdp_profile_generators` axiom is used.

The remaining mathematical content is now exactly the construction of the
`Theorem216SpanningSet` witness for the Step247 Cook--Levin full output.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open TuringMachine
open Step4Compiler
open Step4Compiler.Step245 (Theorem216SpanningSet)

/-- Pointwise paper §40.2 Width⇒Rank data for the concrete Step247 Cook-Levin
compiler output.

This is the honest P-side object: a Khatri--Rao spanning-set witness for the
full compiler polynomial at `(κ,ℓ) = (log n, log n)`, together with a concrete
absolute-constant digitisation of its `C₃`. It is a `Prop` (not a data-carrying
structure in the target theorem) because the Route B closure only needs the
existence of the witness. -/
def Step247CookLevinWidthRankData
    (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (S : Theorem216SpanningSet
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output),
    S.C_3 ≤ 2 ^ 199

/-- Uniform paper §40.2 Width⇒Rank data for every bounded Cook-Levin compiler
instance at the paper scale. -/
def Step247UniformWidthRankData : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Step247CookLevinWidthRankData M n hn hn2 htb hns

/-- The §40.2 Khatri--Rao spanning-set data implies the concrete projected
P-side bound used by the Route B extraction sandwich. -/
theorem cookLevinProjectedPSideBound_of_widthRankData
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hWR : Step247CookLevinWidthRankData M n hn hn2 htb hns) :
    ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
      M n hn2 htb hns := by
  obtain ⟨S, hC3⟩ := hWR
  unfold ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
  unfold PaperFaithfulCompilerPSideBound
  exact Step245.hP_upper_from_spanning_set S
    (Step249.hEnv_from_digitisation S hC3 n hn)

/-- Uniform Width⇒Rank data discharges the named uniform Step247 projected
P-side theorem. -/
theorem step247UniformProjectedPSideTheorem_of_widthRankData
    (hWR : Step247UniformWidthRankData) :
    Step247UniformProjectedPSideTheorem := by
  intro M n hn hn2 htb hns
  exact cookLevinProjectedPSideBound_of_widthRankData
    M n hn hn2 htb hns (hWR M n hn hn2 htb hns)

/-- Uniform Width⇒Rank data closes the Route B no-bounded-SAT-decider surface
through the actual `T_Φ` extraction sandwich. -/
theorem noBoundedSATDeciderAtPaperScale_of_widthRankData_TPhi
    (hWR : Step247UniformWidthRankData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_cookLevin_TPhi_projectedPSideBound
    (step247UniformProjectedPSideTheorem_of_widthRankData hWR)

/-- Uniform Width⇒Rank data also discharges the existing rich-projection
frontier, but only through the no-decider equivalence; no flat gauge witness is
constructed here. -/
theorem cookLevinRichProjectionDischarge_of_widthRankData_TPhi
    (hWR : Step247UniformWidthRankData) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_widthRankData_TPhi hWR)

/-! ## Axiom audit anchors -/

#print axioms cookLevinProjectedPSideBound_of_widthRankData
#print axioms step247UniformProjectedPSideTheorem_of_widthRankData
#print axioms noBoundedSATDeciderAtPaperScale_of_widthRankData_TPhi
#print axioms cookLevinRichProjectionDischarge_of_widthRankData_TPhi

end PallLean.Paper93.DeepMath.PathB
