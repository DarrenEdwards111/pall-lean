import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorPaperFaithful
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNPBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeMapPiPhi

/-!
# Adapter from paper-faithful projected identity minors to the flat NP field

This file is deliberately only an adapter.  It does not construct a final
SAT-decider gauge, does not assert the P-side bound, and does not use the
legacy profile-generator route.  The sole content is that, once the
paper-faithful projected compiler identity-minor lower bound is instantiated
on the degenerate flat Cook-Levin split, its lower-bound field is the same raw
rank inequality needed by the existing flat
`SATDeciderGaugeNPIdentityMinorPreservation` vocabulary.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

/-- A flat instance of the paper-faithful projected compiler lower-bound
surface gives the raw lower bound on the flat gauged compiled polynomial.

This is only a vocabulary adapter: the hypothesis already contains the lower
bound for `gauge (compiledPoly ...)` at the Cook-Levin identity-minor
parameters. -/
theorem flatProjectedCompiledLowerBound_of_paperFaithfulProjectedCompiler
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hpaper :
      PaperFaithfulProjectedCompilerIdentityMinorLowerBound
        n (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))
        gauge) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation M n hn2 htb hns))) :=
  hpaper.2

/-- A flat instance of the paper-faithful projected compiler identity-minor
surface supplies the existing flat SAT-decider NP-preservation field.

The `DecidesSAT` hypothesis remains a hypothesis of the target field; this
adapter does not assert any gauge existence or final contradiction. -/
theorem satDeciderGaugeNPIdentityMinorPreservation_of_flat_paperFaithfulProjectedCompiler
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hpaper :
      PaperFaithfulProjectedCompilerIdentityMinorLowerBound
        n (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q
        (compiledPoly (cook_levin_compilation M n hn2 htb hns))
        gauge) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge := by
  exact satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns gauge
    (flatProjectedCompiledLowerBound_of_paperFaithfulProjectedCompiler
      M n hn2 htb hns Q gauge hpaper)

/-!
## Axiom audit anchors
-/
#print axioms flatProjectedCompiledLowerBound_of_paperFaithfulProjectedCompiler
#print axioms satDeciderGaugeNPIdentityMinorPreservation_of_flat_paperFaithfulProjectedCompiler

end PallLean.Paper93.DeepMath.PathB
