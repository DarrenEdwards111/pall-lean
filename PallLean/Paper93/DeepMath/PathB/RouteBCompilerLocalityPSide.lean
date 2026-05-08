import PallLean.Paper93.DeepMath.PathB.RouteBExtractionMove
import PallLean.Paper93.DeepMath.PathB.ProjectedPSideBoundFrontier

/-!
# Route B P-side from compiler locality / CEW / Khatri--Rao data

This file moves one layer below `RouteBWidthRankPSide`: instead of assuming an
opaque `Theorem216SpanningSet`, it exposes the exact paper §40.2 Width⇒Rank
inputs for the **full Step247 compiler output**:

* CEW bound `≤ C log n`;
* polynomial variable support `≤ n^k`;
* an explicit Khatri--Rao finite spanning family `G` for the SPDP row space;
* the paper arithmetic envelope `(n^k+1)^(C log n+1) ≤ n^200`.

These are then fed through the landed §224.2 Width⇒Rank theorem and into the
Route B `T_Φ` extraction sandwich. This deliberately avoids the older
profile/template-collapse shortcuts and never changes the multiplicative
coupled-sheet target.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open TuringMachine
open Step4Compiler

/-- Pointwise compiler-locality / CEW / Khatri--Rao data for the full Step247
Cook-Levin compiler output.

This is the paper §40.2 input package before it is compressed into a rank
bound. The polynomial is exactly
`(Step247.partitioned_output_cookLevin ...).full_output`, not a projected,
additive, flat, or profile-collapsed surrogate. -/
def Step247CookLevinCompilerLocalityData
    (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (C k : ℕ) (G : Finset (MvPolynomial
      (Fin (cookLevinUVSplit M n).total) ℚ)),
    HasCEWBound
      (Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output
      (C * Nat.log 2 n) ∧
    (Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output.vars.card
      ≤ n ^ k ∧
    MultilinearSPDP.mlBlockedSpdpSubspace
      (extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n)
      (Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output ≤
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinUVSplit M n).total) ℚ)) ∧
    G.card ≤ (n ^ k + 1) ^ (C * Nat.log 2 n + 1) ∧
    (n ^ k + 1) ^ (C * Nat.log 2 n + 1) ≤ n ^ 200

/-- Uniform compiler-locality / CEW / Khatri--Rao data for all bounded
Cook-Levin compiler instances at the paper scale. -/
def Step247UniformCompilerLocalityData : Prop :=
  ∀ (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    Step247CookLevinCompilerLocalityData M n hn hn2 htb hns

/-- Paper §40.2 compiler-locality data implies the concrete projected P-side
bound consumed by the Route B extraction sandwich. -/
theorem cookLevinProjectedPSideBound_of_compilerLocalityData
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hCL : Step247CookLevinCompilerLocalityData M n hn hn2 htb hns) :
    ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
      M n hn2 htb hns := by
  rcases hCL with ⟨C, k, G, hCEW, hVars, hSpan, hCard, hEnv⟩
  unfold ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
  unfold PaperFaithfulCompilerPSideBound
  exact Step224.theorem_216_via_cew_and_locality
    (extendedCookLevinPartition M n hn2)
    (Nat.log 2 n) (Nat.log 2 n)
    (Step247.partitioned_output_cookLevin M n hn2 htb hns).full_output
    n C k hCEW hVars G hSpan hCard hEnv

/-- Uniform paper §40.2 compiler-locality data discharges the named uniform
Step247 projected P-side theorem. -/
theorem step247UniformProjectedPSideTheorem_of_compilerLocalityData
    (hCL : Step247UniformCompilerLocalityData) :
    Step247UniformProjectedPSideTheorem := by
  intro M n hn hn2 htb hns
  exact cookLevinProjectedPSideBound_of_compilerLocalityData
    M n hn hn2 htb hns (hCL M n hn hn2 htb hns)

/-- Uniform compiler-locality data closes the Route B no-bounded-SAT-decider
surface through the actual `T_Φ` extraction sandwich. -/
theorem noBoundedSATDeciderAtPaperScale_of_compilerLocalityData_TPhi
    (hCL : Step247UniformCompilerLocalityData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_cookLevin_TPhi_projectedPSideBound
    (step247UniformProjectedPSideTheorem_of_compilerLocalityData hCL)

/-- Same result phrased at the rich-projection discharge frontier, routed only
through the no-bounded-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_compilerLocalityData_TPhi
    (hCL : Step247UniformCompilerLocalityData) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_compilerLocalityData_TPhi hCL)

/-! ## Axiom audit anchors -/

#print axioms cookLevinProjectedPSideBound_of_compilerLocalityData
#print axioms step247UniformProjectedPSideTheorem_of_compilerLocalityData
#print axioms noBoundedSATDeciderAtPaperScale_of_compilerLocalityData_TPhi
#print axioms cookLevinRichProjectionDischarge_of_compilerLocalityData_TPhi

end PallLean.Paper93.DeepMath.PathB
