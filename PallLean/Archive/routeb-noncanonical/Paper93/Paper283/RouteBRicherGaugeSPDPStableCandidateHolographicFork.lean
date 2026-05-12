import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadSpanStableMapsProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailKernelCriterionProof
import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailConcreteEscapeWitness
import PallLean.PACLeibniz

/-!
# Route B head-tail holographic fork

This module is the roll-up for the Section 39 head-tail fork exposed by the
canonical log-window head-span tail.

The positive branch is now stated through the sharper proof interfaces:

* second-pass closure of finite head-span generators;
* stability of the chosen-projection kernel, or the stronger residual-row
  annihilation condition.

The negative branch is the concrete coordinate obstruction:

* a visible monomial coefficient after the selected projection refutes the
  same holographic-invariance interface.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-! ## Checked boundary cases -/

/-- Multilinear projection is idempotent.  This is the algebra used by the
empty second-pass generator boundary case below. -/
theorem mlProj_idempotent {σ : Type*} [DecidableEq σ] {F : Type*}
    [CommRing F] (p : MvPolynomial σ F) :
    mlProj (mlProj p) = mlProj p := by
  change Finsupp.filter _ (Finsupp.filter _ p) = Finsupp.filter _ p
  ext α
  simp only [Finsupp.filter_apply]
  split <;> rfl

/-- Boundary case for finite head-span second-pass closure: if the second
generator is the empty derivative with unit shift, the row is just `mlProj`
again, hence already lies in the log-window head span by idempotence. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanGeneratorSecondPassClosure_nil_one
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {headKappa headEll : Nat}
    (T : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (headShift : SATDeciderGaugeSpace M n hn2 htb hns)
    (hTlen : T.length = headKappa)
    (hheadShiftDegree : headShift.totalDegree <= headEll)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hTadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition T)
    (hheadKappaLog : headKappa <= Nat.log 2 n)
    (hheadEllLog : headEll <= Nat.log 2 n) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        [] 1 ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  have hgen :
      mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          headKappa headEll
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨T, headShift, hTlen, hheadShiftDegree, hheadShiftVars, hTadm, rfl⟩
  have hhead :
      mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ∈
        routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
    (routeBRicherSPDPStableCandidateLogWindowHeadSpan_contains
      M n hn2 htb hns headKappa headEll hheadKappaLog hheadEllLog) hgen
  simpa [routeBSPDPGeneratorRow, SPDP.iterDerivList, mlProj_idempotent]
    using hhead

/-- Direct finite head-span second-pass closure criterion: if the second
derivative list asks for a variable outside the already-projected head
generator support, the row is zero and therefore belongs to the head span.

This is the actual closure mechanism behind the cardinality/admissibility
boundary case below; the support-too-small hypothesis is only one way to
produce this non-containment. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportNotSubset
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hnotSub :
      ¬ S.toFinset ⊆
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  let q : SATDeciderGaugeSpace M n hn2 htb hns :=
    mlProj
      (headShift *
        SPDP.iterDerivList T
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  have hnotSubq : ¬ S.toFinset ⊆ q.vars := by
    simpa [q] using hnotSub
  have hex : ∃ v, v ∈ S.toFinset ∧ v ∉ q.vars := by
    by_contra h
    apply hnotSubq
    intro v hvS
    by_contra hvq
    exact h ⟨v, hvS, hvq⟩
  rcases hex with ⟨v, hvS, hvq⟩
  have hzero : SPDP.iterDerivList S q = 0 :=
    IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars
      S v q (by simpa using hvS) hvq
  change mlProj (shift * SPDP.iterDerivList S q) ∈
    routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns
  rw [hzero, mul_zero, mlProj_zero]
  exact Submodule.zero_mem _

/-- Membership criterion for the remaining contained-support branch.

If the second-pass row of a projected head generator has already been proved
to lie in any strict head SPDP subspace whose profile is inside the log window,
then it lies in the finite log-window head span.  This is the exact consumer
shape needed after a future product-rule/`mlProj` expansion of the contained
branch. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondPassMemHeadSubspace
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    {combinedKappa combinedEll : Nat}
    (hcombinedKappaLog : combinedKappa <= Nat.log 2 n)
    (hcombinedEllLog : combinedEll <= Nat.log 2 n)
    (hmem :
      routeBSPDPGeneratorRow M n hn2 htb hns
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
          S shift ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          combinedKappa combinedEll
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
  (routeBRicherSPDPStableCandidateLogWindowHeadSpan_contains
    M n hn2 htb hns combinedKappa combinedEll hcombinedKappaLog
    hcombinedEllLog) hmem

/-- Contained-support wrapper for the head-subspace membership criterion.

The contained-support hypothesis records that the zero-by-missing-variable
argument is unavailable; the mathematical work is exactly the supplied
`hmem`, a strict head-subspace membership proof for the second-pass row. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_secondPassMemHeadSubspace
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    {combinedKappa combinedEll : Nat}
    (_hsub :
      S.toFinset ⊆
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars)
    (hcombinedKappaLog : combinedKappa <= Nat.log 2 n)
    (hcombinedEllLog : combinedEll <= Nat.log 2 n)
    (hmem :
      routeBSPDPGeneratorRow M n hn2 htb hns
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
          S shift ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          combinedKappa combinedEll
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_secondPassClosure_of_secondPassMemHeadSubspace
    M n hn2 htb hns hcombinedKappaLog hcombinedEllLog hmem

/-- Single-generator collapse criterion for the contained-support branch.

If the second pass through a projected head generator can be rewritten as one
ordinary strict SPDP generator of the original compiled polynomial, with
combined derivative list `T ++ S` and combined shift `shift * headShift`, then
the result lies in the log-window head span.  The proof is just the existing
head-span inclusion for strict blocked-SPDP generators; the nontrivial
algebraic content is isolated in `hcollapse`. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondPassCollapse
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hshiftVars : shift.vars <= S.toFinset)
    (hcombinedDegreeLog : (shift * headShift).totalDegree <= Nat.log 2 n)
    (hcombinedLengthLog : (T ++ S).length <= Nat.log 2 n)
    (hcombinedAdm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition (T ++ S))
    (hcollapse :
      routeBSPDPGeneratorRow M n hn2 htb hns
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
          S shift =
        mlProj
          ((shift * headShift) *
            SPDP.iterDerivList (T ++ S)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  let P := compiledPoly (cook_levin_compilation M n hn2 htb hns)
  have hcombinedVars : (shift * headShift).vars <= (T ++ S).toFinset := by
    intro v hv
    have hv_or := MvPolynomial.vars_mul shift headShift hv
    rw [List.mem_toFinset, List.mem_append]
    rcases Finset.mem_union.mp hv_or with hvShift | hvHead
    · exact Or.inr (List.mem_toFinset.mp (hshiftVars hvShift))
    · exact Or.inl (List.mem_toFinset.mp (hheadShiftVars hvHead))
  have hgen :
      mlProj
          ((shift * headShift) *
            SPDP.iterDerivList (T ++ S) P) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (T ++ S).length (Nat.log 2 n) P := by
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨T ++ S, shift * headShift, rfl, hcombinedDegreeLog,
        hcombinedVars, hcombinedAdm, rfl⟩
  have hhead :
      mlProj
          ((shift * headShift) *
            SPDP.iterDerivList (T ++ S) P) ∈
        routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
    (routeBRicherSPDPStableCandidateLogWindowHeadSpan_contains
      M n hn2 htb hns (T ++ S).length (Nat.log 2 n)
      hcombinedLengthLog (le_rfl)) hgen
  rw [hcollapse]
  exact hhead

/-- Row-level collapse of the contained-support second pass.

This isolates the algebraic obstruction into two smaller obligations:

* `hcomm`: the requested second derivatives commute through the first
  multilinear projection for the specific head row;
* `hSHeadShift`: the second derivatives do not hit the first-pass shift.

Under those two facts, the second-pass row is a strict original-generator row
with derivative list `T ++ S` and combined shift `shift * headShift`. -/
theorem routeBSPDPGeneratorRow_secondPassCollapse_of_mlProjCommutes_headShift_const
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {P : SATDeciderGaugeSpace M n hn2 htb hns}
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hcomm :
      SPDP.iterDerivList S (mlProj (headShift * SPDP.iterDerivList T P)) =
        SPDP.iterDerivList S (headShift * SPDP.iterDerivList T P))
    (hSHeadShift : ∀ i ∈ S, i ∉ headShift.vars) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj (headShift * SPDP.iterDerivList T P)) S shift =
      mlProj ((shift * headShift) * SPDP.iterDerivList (T ++ S) P) := by
  unfold routeBSPDPGeneratorRow
  rw [hcomm]
  rw [IterDerivHelpers.iterDerivList_mul_left_const]
  · rw [IterDerivHelpers.iterDerivList_append T S P, mul_assoc]
  · intro i hi
    exact MvPolynomial.pderiv_eq_zero_of_notMem_vars (hSHeadShift i hi)

/-- Multilinear-head-row specialization of
`routeBSPDPGeneratorRow_secondPassCollapse_of_mlProjCommutes_headShift_const`.

If the unprojected first-pass row is already multilinear, then `mlProj` fixes
it, so the derivative-through-`mlProj` obligation is automatic. -/
theorem routeBSPDPGeneratorRow_secondPassCollapse_of_headRowMultilinear_headShift_const
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {P : SATDeciderGaugeSpace M n hn2 htb hns}
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hheadRowML : IsMultilinear (headShift * SPDP.iterDerivList T P))
    (hSHeadShift : ∀ i ∈ S, i ∉ headShift.vars) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj (headShift * SPDP.iterDerivList T P)) S shift =
      mlProj ((shift * headShift) * SPDP.iterDerivList (T ++ S) P) := by
  refine
    routeBSPDPGeneratorRow_secondPassCollapse_of_mlProjCommutes_headShift_const
      M n hn2 htb hns ?_ hSHeadShift
  rw [mlProj_of_isMultilinear _ hheadRowML]

/-- Contained-support version of the collapse criterion.

This is the currently hard second-pass branch:
`S.toFinset` is contained in the projected head-generator support, so the
already-proved missing-support zero argument cannot fire.  Under the explicit
single-generator collapse identity, the branch closes by
`routeBRicherSPDPStableCandidate_secondPassClosure_of_secondPassCollapse`. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_secondPassCollapse
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (_hsub :
      S.toFinset ⊆
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hshiftVars : shift.vars <= S.toFinset)
    (hcombinedDegreeLog : (shift * headShift).totalDegree <= Nat.log 2 n)
    (hcombinedLengthLog : (T ++ S).length <= Nat.log 2 n)
    (hcombinedAdm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition (T ++ S))
    (hcollapse :
      routeBSPDPGeneratorRow M n hn2 htb hns
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
          S shift =
        mlProj
          ((shift * headShift) *
            SPDP.iterDerivList (T ++ S)
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  exact
    routeBRicherSPDPStableCandidate_secondPassClosure_of_secondPassCollapse
      M n hn2 htb hns hheadShiftVars hshiftVars hcombinedDegreeLog
      hcombinedLengthLog hcombinedAdm hcollapse

/-- Contained-support closure after reducing `hcollapse` to the concrete
`mlProj`-commutation and shift-disjointness obligations.

Compared with
`routeBRicherSPDPStableCandidate_secondSupportSubset_of_secondPassCollapse`,
this theorem proves the single-generator collapse internally.  The remaining
nontrivial obstruction is exactly `hcomm`: differentiating the first-pass
multilinear projection must agree with differentiating the unprojected
head-shifted row for this `S`. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_mlProjCommutes_headShift_const
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (_hsub :
      S.toFinset ⊆
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars)
    (hcomm :
      SPDP.iterDerivList S
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        SPDP.iterDerivList S
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
    (hSHeadShift : ∀ i ∈ S, i ∉ headShift.vars)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hshiftVars : shift.vars <= S.toFinset)
    (hcombinedDegreeLog : (shift * headShift).totalDegree <= Nat.log 2 n)
    (hcombinedLengthLog : (T ++ S).length <= Nat.log 2 n)
    (hcombinedAdm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition (T ++ S)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  refine
    routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_secondPassCollapse
      M n hn2 htb hns _hsub hheadShiftVars hshiftVars hcombinedDegreeLog
      hcombinedLengthLog hcombinedAdm ?_
  exact
    routeBSPDPGeneratorRow_secondPassCollapse_of_mlProjCommutes_headShift_const
      M n hn2 htb hns hcomm hSHeadShift

/-- Contained-support closure when the unprojected head row is already
multilinear and the second derivative list avoids the first-pass shift.

This discharges the `mlProj`-commutation side of the contained-support
collapse by `mlProj_of_isMultilinear`; what remains is the concrete
multilinearity of `headShift * iterDerivList T P` and the support-disjointness
condition preventing derivatives in `S` from hitting `headShift`. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_headRowMultilinear_headShift_const
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (_hsub :
      S.toFinset ⊆
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars)
    (hheadRowML :
      IsMultilinear
        (headShift *
          SPDP.iterDerivList T
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
    (hSHeadShift : ∀ i ∈ S, i ∉ headShift.vars)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hshiftVars : shift.vars <= S.toFinset)
    (hcombinedDegreeLog : (shift * headShift).totalDegree <= Nat.log 2 n)
    (hcombinedLengthLog : (T ++ S).length <= Nat.log 2 n)
    (hcombinedAdm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition (T ++ S)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  refine
    routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_secondPassCollapse
      M n hn2 htb hns _hsub hheadShiftVars hshiftVars hcombinedDegreeLog
      hcombinedLengthLog hcombinedAdm ?_
  exact
    routeBSPDPGeneratorRow_secondPassCollapse_of_headRowMultilinear_headShift_const
      M n hn2 htb hns hheadRowML hSHeadShift

/-- Product-rule closure for the contained-support branch after the
`mlProj`-commutation step has been isolated.

This removes the earlier `hSHeadShift` restriction: derivatives in the second
pass may hit `headShift`.  The price is the exact Leibniz-term obligation
`hleibnizTerms`: every product-rule term, after the final `shift` and
`mlProj`, already lies in the log-window head span. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizTerms
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hcomm :
      SPDP.iterDerivList S
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        SPDP.iterDerivList S
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
    (hleibnizTerms :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        mlProj
          (shift *
            (SPDP.iterDerivList A headShift *
              SPDP.iterDerivList B
                (SPDP.iterDerivList T
                  (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) ∈
          routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  let P := compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let U := routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns
  let L : SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns :=
    (mlProjLinearMap (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat).comp
      (LinearMap.mulLeft Rat shift)
  have hleibniz :
      SPDP.iterDerivList S
          (headShift * SPDP.iterDerivList T P) ∈
        Submodule.span Rat
          (PACLeibniz.leibnizGenSetBounded S.length headShift
            (SPDP.iterDerivList T P)) :=
    PACLeibniz.iterDerivList_mul_mem_leibniz_span_bounded
      S headShift (SPDP.iterDerivList T P)
  change mlProj
      (shift *
        SPDP.iterDerivList S
          (mlProj (headShift * SPDP.iterDerivList T P))) ∈ U
  rw [hcomm]
  change L (SPDP.iterDerivList S (headShift * SPDP.iterDerivList T P)) ∈ U
  refine Submodule.span_induction
    (p := fun q (_hq : q ∈ Submodule.span Rat
        (PACLeibniz.leibnizGenSetBounded S.length headShift
          (SPDP.iterDerivList T P))) =>
      L q ∈ U)
    ?gen ?zero ?add ?smul hleibniz
  · rintro q ⟨A, B, hlen, rfl⟩
    change mlProj
        (shift *
          (SPDP.iterDerivList A headShift *
            SPDP.iterDerivList B (SPDP.iterDerivList T P))) ∈ U
    exact hleibnizTerms A B hlen
  · change L 0 ∈ U
    rw [map_zero]
    exact Submodule.zero_mem U
  · intro q r _hq _hr hq hr
    change L (q + r) ∈ U
    rw [map_add]
    exact Submodule.add_mem U hq hr
  · intro c q _hq hq
    change L (c • q) ∈ U
    rw [map_smul]
    exact Submodule.smul_mem U c hq

/-- Concrete strict-head-generator form of the product-rule closure.

Each Leibniz term is certified directly as a strict blocked-SPDP generator of
the original compiled polynomial with derivative list `T ++ B` and shift
`shift * iterDerivList A headShift`.  This is the product-rule branch where
some derivatives may land on `headShift`; such hits are absorbed into the new
multiplier rather than forcing `headShift` to be derivative-constant. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizHeadGenerators
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hcomm :
      SPDP.iterDerivList S
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        SPDP.iterDerivList S
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
    (htermDegreeLog :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        (shift * SPDP.iterDerivList A headShift).totalDegree <= Nat.log 2 n)
    (htermLengthLog :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        (T ++ B).length <= Nat.log 2 n)
    (htermVars :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        (shift * SPDP.iterDerivList A headShift).vars <= (T ++ B).toFinset)
    (htermAdm :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition (T ++ B)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  refine
    routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizTerms
      M n hn2 htb hns hcomm ?_
  intro A B hlen
  let P := compiledPoly (cook_levin_compilation M n hn2 htb hns)
  have hgen :
      mlProj
          ((shift * SPDP.iterDerivList A headShift) *
            SPDP.iterDerivList (T ++ B) P) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          (T ++ B).length (Nat.log 2 n) P := by
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨T ++ B, shift * SPDP.iterDerivList A headShift, rfl,
        htermDegreeLog A B hlen, htermVars A B hlen, htermAdm A B hlen, rfl⟩
  have hhead :
      mlProj
          ((shift * SPDP.iterDerivList A headShift) *
            SPDP.iterDerivList (T ++ B) P) ∈
        routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
    (routeBRicherSPDPStableCandidateLogWindowHeadSpan_contains
      M n hn2 htb hns (T ++ B).length (Nat.log 2 n)
      (htermLengthLog A B hlen) (le_rfl)) hgen
  have happend :
      SPDP.iterDerivList B (SPDP.iterDerivList T P) =
        SPDP.iterDerivList (T ++ B) P := by
    rw [IterDerivHelpers.iterDerivList_append T B P]
  simpa [P, happend, mul_assoc] using hhead

/-- The Leibniz generator set with the split lists constrained to be sublists
of the original derivative list.  This is sharper than
`PACLeibniz.leibnizGenSetBounded`: it keeps the support/admissibility
information needed by Route B instead of quantifying over arbitrary lists of
the same total length. -/
noncomputable def routeBLeibnizGenSetSublist {N : Nat}
    (S : List (Fin N)) (g p : MvPolynomial (Fin N) Rat) :
    Set (MvPolynomial (Fin N) Rat) :=
  { r | ∃ A B : List (Fin N),
      A.Sublist S ∧ B.Sublist S ∧
      A.length + B.length = S.length ∧
      r = SPDP.iterDerivList A g * SPDP.iterDerivList B p }

private theorem routeBLeibnizGenSetSublist_pderiv_g_subset {N : Nat}
    (a : Fin N) (S : List (Fin N))
    (g p : MvPolynomial (Fin N) Rat) :
    routeBLeibnizGenSetSublist S (MvPolynomial.pderiv a g) p ⊆
      routeBLeibnizGenSetSublist (a :: S) g p := by
  rintro r ⟨A, B, hAsub, hBsub, hlen, hr⟩
  refine ⟨a :: A, B, ?_, ?_, ?_, ?_⟩
  · exact hAsub.cons₂ a
  · exact hBsub.cons a
  · simp only [List.length_cons]
    omega
  · rw [hr]
    rfl

private theorem routeBLeibnizGenSetSublist_pderiv_p_subset {N : Nat}
    (a : Fin N) (S : List (Fin N))
    (g p : MvPolynomial (Fin N) Rat) :
    routeBLeibnizGenSetSublist S g (MvPolynomial.pderiv a p) ⊆
      routeBLeibnizGenSetSublist (a :: S) g p := by
  rintro r ⟨A, B, hAsub, hBsub, hlen, hr⟩
  refine ⟨A, a :: B, ?_, ?_, ?_, ?_⟩
  · exact hAsub.cons a
  · exact hBsub.cons₂ a
  · simp only [List.length_cons]
    omega
  · rw [hr]
    rfl

/-- Sublist-bounded Leibniz expansion for `iterDerivList`.

Every term in the span has both split lists as sublists of the original
second-pass list.  This is the missing bookkeeping needed to inherit block
admissibility from an admissible combined list `T ++ S`. -/
theorem routeB_iterDerivList_mul_mem_leibniz_span_sublist {N : Nat}
    (S : List (Fin N)) (g p : MvPolynomial (Fin N) Rat) :
    SPDP.iterDerivList S (g * p) ∈
      Submodule.span Rat (routeBLeibnizGenSetSublist S g p) := by
  induction S generalizing g p with
  | nil =>
      apply Submodule.subset_span
      refine ⟨[], [], ?_, ?_, ?_, ?_⟩
      · exact List.Sublist.refl []
      · exact List.Sublist.refl []
      · simp
      · simp [SPDP.iterDerivList]
  | cons a rest ih =>
      have h_pderiv :
          (MvPolynomial.pderiv a) (g * p) =
            (MvPolynomial.pderiv a) g * p + g * (MvPolynomial.pderiv a) p := by
        have hl := (MvPolynomial.pderiv a).leibniz g p
        simp only [smul_eq_mul] at hl
        rw [hl]
        ring
      have h_expand :
          SPDP.iterDerivList (a :: rest) (g * p) =
            SPDP.iterDerivList rest ((MvPolynomial.pderiv a) g * p) +
              SPDP.iterDerivList rest (g * (MvPolynomial.pderiv a) p) := by
        unfold SPDP.iterDerivList
        show
          rest.foldl (fun r i => (MvPolynomial.pderiv i) r)
              ((MvPolynomial.pderiv a) (g * p)) =
            rest.foldl (fun r i => (MvPolynomial.pderiv i) r)
                ((MvPolynomial.pderiv a) g * p) +
              rest.foldl (fun r i => (MvPolynomial.pderiv i) r)
                (g * (MvPolynomial.pderiv a) p)
        rw [h_pderiv]
        exact LowDeg.foldl_pderiv_add rest _ _
      rw [h_expand]
      apply Submodule.add_mem
      · have ih1 := ih ((MvPolynomial.pderiv a) g) p
        exact Submodule.span_mono
          (routeBLeibnizGenSetSublist_pderiv_g_subset a rest g p) ih1
      · have ih2 := ih g ((MvPolynomial.pderiv a) p)
        exact Submodule.span_mono
          (routeBLeibnizGenSetSublist_pderiv_p_subset a rest g p) ih2

private theorem routeB_pderiv_vars_subset {σ : Type*} [DecidableEq σ]
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (w : σ) (p : MvPolynomial σ R) :
    (MvPolynomial.pderiv w p).vars ⊆ p.vars := by
  intro v hv
  rw [MvPolynomial.mem_vars] at hv ⊢
  obtain ⟨d, hd_supp, hd_v⟩ := hv
  refine ⟨d + Finsupp.single w 1, ?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff]
    intro h_zero
    have hd_ne : MvPolynomial.coeff d (MvPolynomial.pderiv w p) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd_supp
    apply hd_ne
    conv_lhs => rw [MvPolynomial.as_sum p]
    rw [map_sum, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro t _
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
    split
    · rename_i heq
      by_cases htw : t w = 0
      · simp [htw]
      · have ht_eq : t = d + Finsupp.single w 1 := by
          ext j
          have hj := Finsupp.ext_iff.mp heq j
          simp only [Finsupp.tsub_apply, Finsupp.single_apply] at hj
          simp only [Finsupp.add_apply, Finsupp.single_apply]
          by_cases hjw : j = w
          · subst hjw
            simp only [ite_true] at hj ⊢
            omega
          · have hjw' : ¬ w = j := Ne.symm hjw
            simp only [hjw', ite_false, Nat.sub_zero] at hj ⊢
            omega
        rw [ht_eq, h_zero, zero_mul]
    · rfl
  · rw [Finsupp.mem_support_iff] at hd_v ⊢
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    omega

private theorem routeB_iterDerivList_vars_subset {N : Nat}
    (S : List (Fin N)) (p : MvPolynomial (Fin N) Rat) :
    (SPDP.iterDerivList S p).vars ⊆ p.vars := by
  induction S generalizing p with
  | nil =>
      unfold SPDP.iterDerivList
      exact Finset.Subset.refl _
  | cons a rest ih =>
      unfold SPDP.iterDerivList
      exact Finset.Subset.trans (ih (MvPolynomial.pderiv a p))
        (routeB_pderiv_vars_subset a p)

/-- Product-rule closure using the sublist-bounded Leibniz expansion.

This is the second-pass contained-support closure interface with the
per-Leibniz-split degree, length, and block-admissibility obligations
discharged from global budgets.  The only remaining split-sensitive support
condition is `hshiftSplitVars`: the second-pass shift support must be
available in the derivative list `T ++ B` for every Leibniz split that sends
the `B` derivatives to the compiled polynomial.  The commutation hypothesis is
row-level, after the final `shift` and `mlProj`, which is the exact equality
used by the proof. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_headRowMlProjRowCommutes_leibnizSublistHeadGenerators
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hrowComm :
      mlProj
          (shift *
            SPDP.iterDerivList S
              (mlProj
                (headShift *
                  SPDP.iterDerivList T
                    (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) =
        mlProj
          (shift *
            SPDP.iterDerivList S
              (headShift *
                SPDP.iterDerivList T
                  (compiledPoly (cook_levin_compilation M n hn2 htb hns)))))
    (hdegreeBudget :
      shift.totalDegree + headShift.totalDegree <= Nat.log 2 n)
    (hlengthBudget : T.length + S.length <= Nat.log 2 n)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hshiftSplitVars :
      ∀ B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        B.Sublist S -> shift.vars <= (T ++ B).toFinset)
    (hTSadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition (T ++ S)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  let P := compiledPoly (cook_levin_compilation M n hn2 htb hns)
  let U := routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns
  let L : SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
      SATDeciderGaugeSpace M n hn2 htb hns :=
    (mlProjLinearMap (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat).comp
      (LinearMap.mulLeft Rat shift)
  have hleibniz :
      SPDP.iterDerivList S
          (headShift * SPDP.iterDerivList T P) ∈
        Submodule.span Rat
          (routeBLeibnizGenSetSublist S headShift
            (SPDP.iterDerivList T P)) :=
    routeB_iterDerivList_mul_mem_leibniz_span_sublist
      S headShift (SPDP.iterDerivList T P)
  change mlProj
      (shift *
        SPDP.iterDerivList S
          (mlProj (headShift * SPDP.iterDerivList T P))) ∈ U
  rw [hrowComm]
  change L (SPDP.iterDerivList S (headShift * SPDP.iterDerivList T P)) ∈ U
  refine Submodule.span_induction
    (p := fun q (_hq : q ∈ Submodule.span Rat
        (routeBLeibnizGenSetSublist S headShift
          (SPDP.iterDerivList T P))) =>
      L q ∈ U)
    ?gen ?zero ?add ?smul hleibniz
  · rintro q ⟨A, B, _hAsub, hBsub, _hlen, rfl⟩
    change mlProj
        (shift *
          (SPDP.iterDerivList A headShift *
            SPDP.iterDerivList B (SPDP.iterDerivList T P))) ∈ U
    have htermDegree :
        (shift * SPDP.iterDerivList A headShift).totalDegree <= Nat.log 2 n := by
      exact le_trans (MvPolynomial.totalDegree_mul _ _)
        (le_trans
          (Nat.add_le_add_left
            (SPDP.totalDegree_iterDerivList_le A headShift) shift.totalDegree)
          hdegreeBudget)
    have htermLength :
        (T ++ B).length <= Nat.log 2 n := by
      rw [List.length_append]
      exact le_trans
        (Nat.add_le_add_left (List.Sublist.length_le hBsub) T.length)
        hlengthBudget
    have htermVars :
        (shift * SPDP.iterDerivList A headShift).vars <= (T ++ B).toFinset := by
      intro v hv
      have hv_or := MvPolynomial.vars_mul shift (SPDP.iterDerivList A headShift) hv
      rcases Finset.mem_union.mp hv_or with hvShift | hvHead
      · exact hshiftSplitVars B hBsub hvShift
      · have hvT : v ∈ T.toFinset :=
          hheadShiftVars (routeB_iterDerivList_vars_subset A headShift hvHead)
        rw [List.mem_toFinset] at hvT ⊢
        exact List.mem_append_left B hvT
    have hTBsub : (T ++ B).Sublist (T ++ S) :=
      List.Sublist.append (List.Sublist.refl T) hBsub
    have htermAdm : SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition (T ++ B) :=
      SPDP.isBlockAdmissible_of_sublist hTBsub hTSadm
    have hgen :
        mlProj
            ((shift * SPDP.iterDerivList A headShift) *
              SPDP.iterDerivList (T ++ B) P) ∈
          mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition
            (T ++ B).length (Nat.log 2 n) P := by
      unfold mlBlockedSpdpSubspace
      exact Submodule.subset_span
        ⟨T ++ B, shift * SPDP.iterDerivList A headShift, rfl,
          htermDegree, htermVars, htermAdm, rfl⟩
    have hhead :
        mlProj
            ((shift * SPDP.iterDerivList A headShift) *
              SPDP.iterDerivList (T ++ B) P) ∈ U :=
      (routeBRicherSPDPStableCandidateLogWindowHeadSpan_contains
        M n hn2 htb hns (T ++ B).length (Nat.log 2 n)
        htermLength (le_rfl)) hgen
    have happend :
        SPDP.iterDerivList B (SPDP.iterDerivList T P) =
          SPDP.iterDerivList (T ++ B) P := by
      rw [IterDerivHelpers.iterDerivList_append T B P]
    simpa [P, happend, mul_assoc] using hhead
  · change L 0 ∈ U
    rw [map_zero]
    exact Submodule.zero_mem U
  · intro q r _hq _hr hq hr
    change L (q + r) ∈ U
    rw [map_add]
    exact Submodule.add_mem U hq hr
  · intro c q _hq hq
    change L (c • q) ∈ U
    rw [map_smul]
    exact Submodule.smul_mem U c hq

/-- Raw derivative-through-`mlProj` commutation implies the row-level
commutation used by the sublist-bounded product-rule closure. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizSublistHeadGenerators
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hcomm :
      SPDP.iterDerivList S
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        SPDP.iterDerivList S
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
    (hdegreeBudget :
      shift.totalDegree + headShift.totalDegree <= Nat.log 2 n)
    (hlengthBudget : T.length + S.length <= Nat.log 2 n)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hshiftSplitVars :
      ∀ B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        B.Sublist S -> shift.vars <= (T ++ B).toFinset)
    (hTSadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition (T ++ S)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  refine
    routeBRicherSPDPStableCandidate_secondPassClosure_of_headRowMlProjRowCommutes_leibnizSublistHeadGenerators
      M n hn2 htb hns ?_ hdegreeBudget hlengthBudget hheadShiftVars
      hshiftSplitVars hTSadm
  rw [hcomm]

/-- Contained-support wrapper for the sublist-bounded product-rule closure.

Compared with the older `leibnizHeadGenerators` interface, this theorem no
longer asks for degree, length, variable support, and block admissibility for
every Leibniz split as four independent opaque hypotheses.  Degree, length,
head-shift variable support, and block admissibility are derived here; the
only split-indexed support obligation left is the genuine routing condition
for the second-pass shift. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_headRowMlProjRowCommutes_leibnizSublistHeadGenerators
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (_hsub :
      S.toFinset ⊆
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars)
    (hrowComm :
      mlProj
          (shift *
            SPDP.iterDerivList S
              (mlProj
                (headShift *
                  SPDP.iterDerivList T
                    (compiledPoly (cook_levin_compilation M n hn2 htb hns))))) =
        mlProj
          (shift *
            SPDP.iterDerivList S
              (headShift *
                SPDP.iterDerivList T
                  (compiledPoly (cook_levin_compilation M n hn2 htb hns)))))
    (hdegreeBudget :
      shift.totalDegree + headShift.totalDegree <= Nat.log 2 n)
    (hlengthBudget : T.length + S.length <= Nat.log 2 n)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hshiftSplitVars :
      ∀ B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        B.Sublist S -> shift.vars <= (T ++ B).toFinset)
    (hTSadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition (T ++ S)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_secondPassClosure_of_headRowMlProjRowCommutes_leibnizSublistHeadGenerators
    M n hn2 htb hns hrowComm hdegreeBudget hlengthBudget hheadShiftVars
    hshiftSplitVars hTSadm

/-- Contained-support sublist-bounded closure from raw derivative
commutation. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_mlProjCommutes_leibnizSublistHeadGenerators
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (_hsub :
      S.toFinset ⊆
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars)
    (hcomm :
      SPDP.iterDerivList S
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        SPDP.iterDerivList S
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
    (hdegreeBudget :
      shift.totalDegree + headShift.totalDegree <= Nat.log 2 n)
    (hlengthBudget : T.length + S.length <= Nat.log 2 n)
    (hheadShiftVars : headShift.vars <= T.toFinset)
    (hshiftSplitVars :
      ∀ B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        B.Sublist S -> shift.vars <= (T ++ B).toFinset)
    (hTSadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition (T ++ S)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizSublistHeadGenerators
    M n hn2 htb hns hcomm hdegreeBudget hlengthBudget hheadShiftVars
    hshiftSplitVars hTSadm

/-- Contained-support wrapper for the product-rule head-generator criterion.

The contained-support hypothesis records that the missing-variable zero branch
does not apply.  The actual work is delegated to the Leibniz split obligations,
which allow second-pass derivatives to hit `headShift`. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_mlProjCommutes_leibnizHeadGenerators
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (_hsub :
      S.toFinset ⊆
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars)
    (hcomm :
      SPDP.iterDerivList S
          (mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
        SPDP.iterDerivList S
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
    (htermDegreeLog :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        (shift * SPDP.iterDerivList A headShift).totalDegree <= Nat.log 2 n)
    (htermLengthLog :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        (T ++ B).length <= Nat.log 2 n)
    (htermVars :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        (shift * SPDP.iterDerivList A headShift).vars <= (T ++ B).toFinset)
    (htermAdm :
      ∀ A B : List (Fin (RouteBCookLevinDim M n hn2 htb hns)),
        A.length + B.length = S.length ->
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition (T ++ B)) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizHeadGenerators
    M n hn2 htb hns hcomm htermDegreeLog htermLengthLog htermVars htermAdm

/-- Boundary case for finite head-span second-pass closure: if the second
derivative list is longer than the variable support of the already-projected
head generator, admissibility forces some second-pass variable to be absent
from that support, so the second derivative pass is zero. -/
theorem routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportTooSmall
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {spdpKappa : Nat}
    {T S : List (Fin (RouteBCookLevinDim M n hn2 htb hns))}
    {headShift shift : SATDeciderGaugeSpace M n hn2 htb hns}
    (hSlen : S.length = spdpKappa)
    (hadm : SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S)
    (hsmall :
      (mlProj
        (headShift *
          SPDP.iterDerivList T
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))).vars.card <
        spdpKappa) :
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns := by
  let q : SATDeciderGaugeSpace M n hn2 htb hns :=
    mlProj
      (headShift *
        SPDP.iterDerivList T
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  have hsmallq : q.vars.card < S.length := by
    simpa [q, hSlen] using hsmall
  have hnotSub : ¬ S.toFinset ⊆ q.vars := by
    intro hsub
    have hcardS : S.toFinset.card = S.length :=
      List.toFinset_card_of_nodup hadm.1
    have hle : S.toFinset.card <= q.vars.card := Finset.card_le_card hsub
    have hlt : q.vars.card < S.toFinset.card := by
      simpa [hcardS] using hsmallq
    exact (Nat.not_lt_of_ge hle) hlt
  exact
    routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportNotSubset
      M n hn2 htb hns (by simpa [q] using hnotSub)

/-- Boundary case for the chosen-projection branch: if the selected projection
is the identity map, then the residual `p - Π p` is zero, so strict residual
generator annihilation holds. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_projection_eq_id
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hPi :
      routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns) =
        LinearMap.id) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
      M n hn2 htb hns := by
  intro spdpKappa ell p S shift hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm
  let tail := routeBRicherSPDPStableCandidateLogWindowHeadTail M n hn2 htb hns
  let Pi := routeBRicherSPDPStableCandidateProjection M n hn2 htb hns tail
  have hPiApply : Pi p = p := by
    have h :=
      congrArg
        (fun F : SATDeciderGaugeSpace M n hn2 htb hns →ₗ[Rat]
            SATDeciderGaugeSpace M n hn2 htb hns => F p)
        hPi
    simpa [Pi, tail] using h
  have hpSub : p - Pi p = 0 := by
    rw [hPiApply]
    simp
  change routeBSPDPGeneratorRow M n hn2 htb hns (p - Pi p) S shift = 0
  rw [hpSub, routeBSPDPGeneratorRow_zero]

/-! ## Head-span escape closure -/

/-- If the finite head-span generator second-pass closure fails, the failure is
already a concrete log-window generator-map escape from the canonical head
span. -/
theorem routeBRicherSPDPStableCandidate_headSpanGeneratorMapEscape_of_not_generatorSecondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hnot :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
      M n hn2 htb hns := by
  classical
  by_contra hnoEscape
  apply hnot
  intro headKappa headEll spdpKappa ell T headShift S shift
    hTlen hheadShiftDegree hheadShiftVars hTadm hheadKappaLog
    hheadEllLog hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
  let p :=
    mlProj
      (headShift *
        SPDP.iterDerivList T
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
  have hpGen :
      p ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          headKappa headEll
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨T, headShift, hTlen, hheadShiftDegree, hheadShiftVars,
        hTadm, by simp [p]⟩
  have hpHead :
      p ∈ routeBRicherSPDPStableCandidateLogWindowHeadSpan
        M n hn2 htb hns :=
    (routeBRicherSPDPStableCandidateLogWindowHeadSpan_contains
      M n hn2 htb hns headKappa headEll hheadKappaLog hheadEllLog) hpGen
  by_contra hrowNotHead
  exact hnoEscape
    ⟨spdpKappa, ell, p, S, shift, hpHead, hSlen, hshiftDegree,
      hSlog, hshiftLog, hshiftVars, hadm,
      by simpa [p] using hrowNotHead⟩

/-- Finite head-span generator second-pass closure is exactly absence of a
concrete log-window generator-map escape from the canonical head span. -/
theorem routeBRicherSPDPStableCandidate_generatorSecondPassClosure_iff_no_headSpanGeneratorMapEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns := by
  constructor
  · intro hhead
    exact
      routeBRicherSPDPStableCandidate_no_headSpanGeneratorMapEscape_of_stableGeneratorMaps
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
          M n hn2 htb hns hhead)
  · intro hnoEscape
    by_contra hnot
    exact hnoEscape
      (routeBRicherSPDPStableCandidate_headSpanGeneratorMapEscape_of_not_generatorSecondPassClosure
        M n hn2 htb hns hnot)

/-- Positive Route B head-tail fork package using the newest proof-facing
interfaces: finite head-span second-pass closure plus chosen-projection kernel
stability, together with the two existing P-side consumer fields. -/
structure RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  head_second_pass_closure :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
      M n hn2 htb hns
  projection_kernel_stable :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
      M n hn2 htb hns
  unprojected_preimage :
    RouteBRicherGaugeFiniteRowsSPDPLogWindowUnprojectedPreimage
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateRows M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns))
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns

/-- Second-pass head-span closure and chosen-projection kernel stability lower
to the existing row-closure/descent frontier. -/
def routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHeadTailRowClosureDescentFrontier
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_headSpanStableGeneratorMaps
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns frontier.head_second_pass_closure)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
      M n hn2 htb hns frontier.projection_kernel_stable)
    frontier.unprojected_preimage
    frontier.p_window_cover

/-- The positive fork package proves the Section 39-facing holographic
invariance interface for the canonical head-span tail. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns frontier.head_second_pass_closure)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
      M n hn2 htb hns frontier.projection_kernel_stable)

/-- The same positive fork package proves the projected P-side bound, once
the preimage and P-window consumer fields are supplied. -/
theorem routeBRicherSPDPStableCandidate_projectedPSideBound_of_secondPass_kernelStable
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (frontier :
      RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
        M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBRicherSPDPStableCandidateProjection M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns)) :=
  routeBRicherSPDPStableCandidate_projectedPSideBound_of_rowClosureDescentFrontier
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
      M n hn2 htb hns frontier)

/-- Second-pass head-span closure plus residual-row annihilation is a stronger
positive route to the same holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_residualGeneratorZero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns)
    (hzero :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailResidualGeneratorZero
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidateLogWindowHeadTail
        M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
      M n hn2 htb hns hhead)
    (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_residualGeneratorZero
      M n hn2 htb hns hzero)

/-- A visible projected monomial coefficient refutes the same Section 39
holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_visibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_visibleCoefficientEscapeObstruction
      M n hn2 htb hns hcoord)

/-- The empty-generator visible coefficient obstruction also refutes the same
Section 39 holographic-invariance interface. -/
theorem routeBRicherSPDPStableCandidate_not_holographicInvariance_of_mlProjVisibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcoord :
      RouteBRicherSPDPStableCandidateHeadSpanTailMlProjVisibleCoefficientEscapeWitness
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) :=
  routeBRicherSPDPStableCandidate_not_holographicInvariance_for_headSpanTail_of_logWindowProjectionEscapeWitness
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanTailLogWindowProjectionEscapeWitness_of_mlProjVisibleCoefficientEscape
      M n hn2 htb hns hcoord)

/-- The chosen-projection kernel-stability branch is exactly absence of the
visible monomial-coordinate escape branch for the same head-span-tail
projection. -/
theorem routeBRicherSPDPStableCandidate_projectionKernelStableGeneratorMaps_iff_no_visibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns := by
  constructor
  · intro hstable hcoord
    have hcriterion :
        RouteBRicherSPDPStableCandidateLogWindowHeadTailChosenProjectionKernelCriterion
          M n hn2 htb hns :=
      (routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
        M n hn2 htb hns).mp hstable
    have hnoEscape :
        ¬ RouteBRicherSPDPStableCandidateHeadSpanTailLogWindowProjectionEscapeWitness
          M n hn2 htb hns :=
      (routeBRicherSPDPStableCandidate_headSpanTailKernelCriterion_iff_no_logWindowProjectionEscapeWitness
        M n hn2 htb hns).mp hcriterion
    exact hnoEscape
      ((routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_logWindowProjectionEscapeWitness
        M n hn2 htb hns).mp hcoord)
  · intro hnoCoeff
    refine
      (routeBRicherSPDPStableCandidate_logWindowHeadTailProjectionKernelStableGeneratorMaps_iff_kernelCriterion
        M n hn2 htb hns).mpr ?_
    refine
      (routeBRicherSPDPStableCandidate_headSpanTailKernelCriterion_iff_no_logWindowProjectionEscapeWitness
        M n hn2 htb hns).mpr ?_
    intro hbad
    exact hnoCoeff
      ((routeBRicherSPDPStableCandidate_visibleCoefficientEscapeObstruction_iff_logWindowProjectionEscapeWitness
        M n hn2 htb hns).mpr hbad)

/-- Once the finite head span is stable under the log-window generator maps,
the remaining chosen-projection branch is exactly a dichotomy: either Section
39 holographic invariance holds for the canonical head-span tail, or the
chosen projection has a visible monomial-coefficient escape. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_headSpanStableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) ∨
      RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns := by
  classical
  by_cases hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadTailProjectionKernelStableGeneratorMaps
        M n hn2 htb hns
  · left
    exact
      routeBRicherSPDPStableCandidate_holographicInvariance_for_headSpanTail_of_headSpanStableGeneratorMaps_descent
        M n hn2 htb hns hhead
        (routeBRicherSPDPStableCandidate_logWindowHeadTailChosenProjectionDescent_of_projectionKernelStableGeneratorMaps
          M n hn2 htb hns hstable)
  · right
    by_contra hnoCoeff
    exact hstable
      ((routeBRicherSPDPStableCandidate_projectionKernelStableGeneratorMaps_iff_no_visibleCoefficientEscape
        M n hn2 htb hns).mpr hnoCoeff)

/-- Once the finite head-span second-pass closure is supplied, the remaining
chosen-projection branch is exactly a dichotomy: either Section 39
holographic invariance holds for the canonical head-span tail, or there is a
visible projected monomial coefficient escaping the selected complement. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_secondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) ∨
      RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns := by
  exact
    routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_headSpanStableGeneratorMaps
      M n hn2 htb hns
      (routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
        M n hn2 htb hns hhead)

/-- With finite head-span second-pass closure in hand, holographic invariance
is equivalent to the absence of a visible coefficient escape for the chosen
head-span-tail projection. -/
theorem routeBRicherSPDPStableCandidate_holographicInvariance_iff_no_visibleCoefficientEscape_of_secondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateHolographicInvariance
        M n hn2 htb hns
        (routeBRicherSPDPStableCandidateLogWindowHeadTail
          M n hn2 htb hns) ↔
      ¬ RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
        M n hn2 htb hns := by
  constructor
  · intro hinv hcoord
    exact
      (routeBRicherSPDPStableCandidate_not_holographicInvariance_of_visibleCoefficientEscape
        M n hn2 htb hns hcoord) hinv
  · intro hno
    cases
      routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_secondPassClosure
        M n hn2 htb hns hhead with
    | inl hinv => exact hinv
    | inr hcoord => exact False.elim (hno hcoord)

/-- Fully exposed Route B fork after the head-span reduction: either the
finite head span already has a concrete log-window generator-map escape, or
the Section 39 holographic interface holds for the canonical head-span tail,
or the chosen projection has a visible monomial-coefficient escape. -/
theorem routeBRicherSPDPStableCandidate_headSpanEscape_or_holographicInvariance_or_visibleCoefficientEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns ∨
      RouteBRicherSPDPStableCandidateHolographicInvariance
          M n hn2 htb hns
          (routeBRicherSPDPStableCandidateLogWindowHeadTail
            M n hn2 htb hns) ∨
        RouteBRicherSPDPStableCandidateHeadSpanTailVisibleCoefficientEscapeObstruction
          M n hn2 htb hns := by
  classical
  by_cases hhead :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns
  · right
    exact
      routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_secondPassClosure
        M n hn2 htb hns hhead
  · left
    exact
      routeBRicherSPDPStableCandidate_headSpanGeneratorMapEscape_of_not_generatorSecondPassClosure
        M n hn2 htb hns hhead

/-! ## Axiom audit anchors -/

#print axioms mlProj_idempotent
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanGeneratorSecondPassClosure_nil_one
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportNotSubset
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondPassMemHeadSubspace
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_secondPassMemHeadSubspace
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondPassCollapse
#print axioms routeBSPDPGeneratorRow_secondPassCollapse_of_mlProjCommutes_headShift_const
#print axioms routeBSPDPGeneratorRow_secondPassCollapse_of_headRowMultilinear_headShift_const
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_secondPassCollapse
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_mlProjCommutes_headShift_const
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_headRowMultilinear_headShift_const
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizTerms
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizHeadGenerators
#print axioms routeB_iterDerivList_mul_mem_leibniz_span_sublist
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_headRowMlProjRowCommutes_leibnizSublistHeadGenerators
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_mlProjCommutes_leibnizSublistHeadGenerators
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_headRowMlProjRowCommutes_leibnizSublistHeadGenerators
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_mlProjCommutes_leibnizSublistHeadGenerators
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportSubset_of_mlProjCommutes_leibnizHeadGenerators
#print axioms routeBRicherSPDPStableCandidate_secondPassClosure_of_secondSupportTooSmall
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadTailResidualGeneratorZero_of_projection_eq_id
#print axioms routeBRicherSPDPStableCandidate_headSpanGeneratorMapEscape_of_not_generatorSecondPassClosure
#print axioms routeBRicherSPDPStableCandidate_generatorSecondPassClosure_iff_no_headSpanGeneratorMapEscape
#print axioms RouteBRicherSPDPStableCandidateHeadTailSecondPassKernelFrontier
#print axioms routeBRicherSPDPStableCandidate_headTailRowClosureDescentFrontier_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_projectedPSideBound_of_secondPass_kernelStable
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_of_secondPass_residualGeneratorZero
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_visibleCoefficientEscape
#print axioms routeBRicherSPDPStableCandidate_not_holographicInvariance_of_mlProjVisibleCoefficientEscape
#print axioms routeBRicherSPDPStableCandidate_projectionKernelStableGeneratorMaps_iff_no_visibleCoefficientEscape
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_headSpanStableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_or_visibleCoefficientEscape_of_secondPassClosure
#print axioms routeBRicherSPDPStableCandidate_holographicInvariance_iff_no_visibleCoefficientEscape_of_secondPassClosure
#print axioms routeBRicherSPDPStableCandidate_headSpanEscape_or_holographicInvariance_or_visibleCoefficientEscape

end PallLean.Paper93.Paper283
