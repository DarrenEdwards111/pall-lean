import PallLean.Paper93.DeepMath.PathB.RouteBExtractionMove
import PallLean.Paper93.DeepMath.PathB.ProjectedPSideBoundFrontier

/-!
# Route B P-side at the plain Cook--Levin product target

The current paper-faithful correction is that the CEW/locality theorem must be
proved at the **factor/product** level for the Cook--Levin product, not by
pretending the fully-expanded polynomial has small `HasCEWBound`.

This file therefore exposes the exact no-shortcut target immediately before the
`rename σ.inlU` embedding:

`Γ(pullbackPartition extendedCookLevinPartition inlU, log n, log n,
   cookLevinQ M n) ≤ n^200`.

A proof of this plain-product rank bound can come from the real factor-local
Khatri--Rao argument. Once it is available, the existing block-local-basis
invariance theorem transports it to the Step247 `full_output`, and the Route B
`T_Φ` extraction sandwich closes.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open TuringMachine
open Step4Compiler

/-- The honest plain-product P-side rank target for the Cook--Levin polynomial
before embedding into the `u/v` split. This is the object to discharge by the
factor-local Theorem216/Khatri--Rao argument. -/
def PlainCookLevinQPSideBound
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  MultilinearSPDP.mlBlockedSpdpRank
    (MultilinearSPDP.pullbackPartition
      (extendedCookLevinPartition M n hn2)
      (cookLevinUVSplit M n).inlU)
    (Nat.log 2 n) (Nat.log 2 n)
    (show MvPolynomial (Fin n) ℚ from cookLevinQ M n hn2 htb hns) ≤ n ^ 200

/-- Uniform plain-product P-side rank target at the paper scale. -/
def Step247UniformPlainCookLevinQPSideBound : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    PlainCookLevinQPSideBound M n hn2 htb hns

/-- The plain Cook--Levin product rank bound transports through `rename σ.inlU`
to the concrete Step247 `full_output`, giving the projected P-side bound used
by Route B. -/
theorem cookLevinProjectedPSideBound_of_plainCookLevinQPSideBound
    (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hQ : PlainCookLevinQPSideBound M n hn2 htb hns) :
    ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
      M n hn2 htb hns := by
  unfold ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
  unfold PaperFaithfulCompilerPSideBound
  exact Step252.cookLevin_full_output_rank_le_of_pullback_rank_le
    M n hn2 htb hns hQ

/-- Uniform plain-product rank bounds discharge the named uniform Step247
projected P-side theorem. -/
theorem step247UniformProjectedPSideTheorem_of_plainCookLevinQPSideBound
    (hQ : Step247UniformPlainCookLevinQPSideBound) :
    Step247UniformProjectedPSideTheorem := by
  intro M n hn hn2 htb hns
  exact cookLevinProjectedPSideBound_of_plainCookLevinQPSideBound
    M n hn hn2 htb hns (hQ M n hn hn2 htb hns)

/-- Uniform plain-product rank bounds close the Route B no-bounded-SAT-decider
surface through the actual `T_Φ` extraction sandwich. -/
theorem noBoundedSATDeciderAtPaperScale_of_plainCookLevinQPSideBound_TPhi
    (hQ : Step247UniformPlainCookLevinQPSideBound) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_cookLevin_TPhi_projectedPSideBound
    (step247UniformProjectedPSideTheorem_of_plainCookLevinQPSideBound hQ)

/-- Same closure at the rich-projection discharge frontier, routed via the
no-bounded-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_plainCookLevinQPSideBound_TPhi
    (hQ : Step247UniformPlainCookLevinQPSideBound) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_plainCookLevinQPSideBound_TPhi hQ)

/-! ## Axiom audit anchors -/

#print axioms cookLevinProjectedPSideBound_of_plainCookLevinQPSideBound
#print axioms step247UniformProjectedPSideTheorem_of_plainCookLevinQPSideBound
#print axioms noBoundedSATDeciderAtPaperScale_of_plainCookLevinQPSideBound_TPhi
#print axioms cookLevinRichProjectionDischarge_of_plainCookLevinQPSideBound_TPhi

end PallLean.Paper93.DeepMath.PathB
