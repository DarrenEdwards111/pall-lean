import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailNoGo
import PallLean.Paper93.Paper283.BridgeAMlProjLinear

/-!
# Empty-generator escape reductions for the head-span tail

This file sharpens the head-span-tail projection-escape route by reducing the
log-window witness to the smallest admissible SPDP generator: empty derivative
list and constant shift `1`.  In that case the generator row is just `mlProj p`.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Empty-generator `mlProj` projection escape for the head-span tail.

This is the concrete remaining exhibit after fixing the finite projection's
chosen complement: a complement vector whose multilinear projection has
nonzero component along the finite head-span rows. -/
def RouteBRicherSPDPStableCandidateHeadSpanTailMlProjProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists p : SATDeciderGaugeSpace M n hn2 htb hns,
    p ∈ routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
      M n hn2 htb hns ∧
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      (mlProj p) ≠ 0

/-- Kernel-vector form of the empty-generator escape: `p` is killed by the
chosen finite projection, but `mlProj p` is not. -/
def RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists p : SATDeciderGaugeSpace M n hn2 htb hns,
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      p = 0 ∧
    routeBRicherSPDPStableCandidateProjectionWithComplement
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      (mlProj p) ≠ 0

/-- The empty-generator `mlProj` escape produces the requested log-window
projection-escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns := by
  obtain ⟨p, hpComplement, hprojNe⟩ := hbad
  refine ⟨0, 0, p,
    ([] : List (Fin (RouteBCookLevinDim M n hn2 htb hns))),
    (1 : SATDeciderGaugeSpace M n hn2 htb hns),
    by simp,
    by simp [MvPolynomial.totalDegree_one],
    by simp,
    by simp [MvPolynomial.totalDegree_one],
    by simp [MvPolynomial.vars_one],
    ?_,
    hpComplement,
    ?_⟩
  · constructor
    · simp
    · intro b
      simp
  · simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_one] using
      hprojNe

/-- Kernel-vector `mlProj` projection escape implies the complement-vector
empty-generator escape. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailMlProjProjectionEscape_of_kernelMlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailMlProjProjectionEscapeWitness
      M n hn2 htb hns := by
  obtain ⟨p, hpZero, hprojNe⟩ := hbad
  refine ⟨p, ?_, hprojNe⟩
  exact
    (routeBRicherSPDPStableCandidateProjectionWithComplement_apply_eq_zero_iff
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
        M n hn2 htb hns)
      (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement_isCompl
        M n hn2 htb hns)
      p).mp hpZero

/-- Kernel-vector `mlProj` projection escape produces the requested log-window
projection-escape witness. -/
theorem routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelMlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjProjectionEscape
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailMlProjProjectionEscape_of_kernelMlProjProjectionEscape
      M n hn2 htb hns hbad)

/-- Empty-generator `mlProj` escape refutes the head-span-tail
explicit-complement invariant through the existing no-go wrapper. -/
theorem routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_mlProjProjectionEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbad :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjProjectionEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateExplicitComplementInvariant
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)
        (routeBRicherSPDPStableCandidateHeadSpanTailProjectionComplement
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_projectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailProjectionEscapeWitness_of_logWindow
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjProjectionEscape
        M n hn2 htb hns hbad))

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailMlProjProjectionEscapeWitness
#print axioms RouteBRicherSPDPStableCandidateHeadSpanTailKernelMlProjProjectionEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjProjectionEscape
#print axioms routeBRicherSPDPStableCandidate_headSpanTailMlProjProjectionEscape_of_kernelMlProjProjectionEscape
#print axioms routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_kernelMlProjProjectionEscape
#print axioms routeBRicherSPDPStableCandidate_headSpanTail_explicitComplementInvariant_noGo_of_mlProjProjectionEscape

end PallLean.Paper93.Paper283
