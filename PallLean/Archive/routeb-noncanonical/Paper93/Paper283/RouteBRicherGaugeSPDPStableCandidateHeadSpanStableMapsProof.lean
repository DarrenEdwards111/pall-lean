import PallLean.Paper93.Paper283.RouteBRicherGaugeSPDPStableCandidateHeadTailRowClosureProof

/-!
# Head-span stable-generator-map proof frontier

This module attacks the positive row-closure side for the canonical Route B
head span.  The current head span is the finite supremum of the concrete
head row's strict blocked-SPDP subspaces inside the log window.  To prove it
is stable under another log-window generator pass, it is enough to prove the
generator-level second-pass closure below.

The file also records the exact obstruction: failure of
`RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps` is
precisely a log-window generator row escaping the head span.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Generator-level second-pass closure for the log-window head span.

This is the concrete missing algebraic lemma: start with any strict
blocked-SPDP generator of the compiled head row whose profile lies in the log
window, then apply one more log-window Route B generator row.  The result must
land back in the same finite log-window head span.

The current `mlBlockedSpdpSubspace` definition alone does not prove this:
the second pass differentiates a previously multilinear-projected shifted
derivative, and no existing lemma rewrites that result into one of the
head-span summands without extra closure information. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (headKappa headEll spdpKappa ell : Nat)
    (T : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (headShift : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    T.length = headKappa ->
    headShift.totalDegree <= headEll ->
    headShift.vars <= T.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition T ->
    headKappa <= Nat.log 2 n ->
    headEll <= Nat.log 2 n ->
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns
        (mlProj
          (headShift *
            SPDP.iterDerivList T
              (compiledPoly (cook_levin_compilation M n hn2 htb hns))))
        S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns

/-- Pointwise constituent-subspace form of the same second-pass closure.

This version says every element of each strict head SPDP summand in the log
window remains in the total head span after a log-window generator pass. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadSpanConstituentSecondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  forall (headKappa headEll spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    p ∈
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        headKappa headEll
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ->
    headKappa <= Nat.log 2 n ->
    headEll <= Nat.log 2 n ->
    S.length = spdpKappa ->
    shift.totalDegree <= ell ->
    S.length <= Nat.log 2 n ->
    shift.totalDegree <= Nat.log 2 n ->
    shift.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns

/-- A concrete log-window escape from the canonical head span.  This is the
negative branch corresponding exactly to failure of stable generator maps. -/
def RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (spdpKappa ell : Nat)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (shift : SATDeciderGaugeSpace M n hn2 htb hns),
    p ∈ routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns ∧
    S.length = spdpKappa ∧
    shift.totalDegree <= ell ∧
    S.length <= Nat.log 2 n ∧
    shift.totalDegree <= Nat.log 2 n ∧
    shift.vars <= S.toFinset ∧
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ∧
    routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∉
      routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns

/-- The generator-level second-pass closure extends by linearity to every
element of each strict head SPDP summand. -/
theorem routeBRicherSPDPStableCandidate_headSpanConstituentSecondPassClosure_of_generatorSecondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hgen :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanConstituentSecondPassClosure
      M n hn2 htb hns := by
  intro headKappa headEll spdpKappa ell p S shift hpHead hheadKappaLog
    hheadEllLog hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
  let U := routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns
  change routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈ U
  unfold mlBlockedSpdpSubspace at hpHead
  refine Submodule.span_induction
    (s := { q |
      ∃ (T : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (headShift : SATDeciderGaugeSpace M n hn2 htb hns),
        T.length = headKappa ∧
        headShift.totalDegree <= headEll ∧
        headShift.vars <= T.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition T ∧
        q =
          mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))) })
    (p := fun q (_hq : q ∈ Submodule.span Rat { q |
      ∃ (T : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
        (headShift : SATDeciderGaugeSpace M n hn2 htb hns),
        T.length = headKappa ∧
        headShift.totalDegree <= headEll ∧
        headShift.vars <= T.toFinset ∧
        SPDP.isBlockAdmissible
          (cook_levin_compilation M n hn2 htb hns).partition T ∧
        q =
          mlProj
            (headShift *
              SPDP.iterDerivList T
                (compiledPoly (cook_levin_compilation M n hn2 htb hns))) }) =>
      routeBSPDPGeneratorRow M n hn2 htb hns q S shift ∈ U)
    ?gen ?zero ?add ?smul hpHead
  · rintro q ⟨T, headShift, hTlen, hheadShiftDegree, hheadShiftVars,
      hTadm, rfl⟩
    exact
      hgen headKappa headEll spdpKappa ell T headShift S shift
        hTlen hheadShiftDegree hheadShiftVars hTadm hheadKappaLog
        hheadEllLog hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
  · change routeBSPDPGeneratorRow M n hn2 htb hns 0 S shift ∈ U
    rw [routeBSPDPGeneratorRow_zero]
    exact Submodule.zero_mem U
  · intro q r _hq _hr hq hr
    change
      routeBSPDPGeneratorRow M n hn2 htb hns (q + r) S shift ∈ U
    rw [routeBSPDPGeneratorRow_add]
    exact Submodule.add_mem U hq hr
  · intro c q _hq hq
    change routeBSPDPGeneratorRow M n hn2 htb hns (c • q) S shift ∈ U
    rw [routeBSPDPGeneratorRow_smul]
    exact Submodule.smul_mem U c hq

/-- Constituent second-pass closure proves the requested stable-generator-map
predicate for the whole canonical log-window head span. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_constituentSecondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hconst :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanConstituentSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
      M n hn2 htb hns := by
  intro spdpKappa ell S shift hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm q hq
  let U := routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns
  rcases hq with ⟨p, hpHead, rfl⟩
  change routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈ U
  let headSubspace :
      Fin (Nat.log 2 n + 1) ->
        Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
    fun headKappa =>
      ⨆ headEll : Fin (Nat.log 2 n + 1),
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          headKappa.1 headEll.1
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))
  have hpHead' : p ∈ ⨆ headKappa, headSubspace headKappa := by
    simpa [U, headSubspace, routeBRicherSPDPStableCandidateLogWindowHeadSpan]
      using hpHead
  refine Submodule.iSup_induction (p := headSubspace) (x := p)
    (motive := fun p =>
      routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈ U)
    hpHead' ?_ ?_ ?_
  · intro headKappa p hpKappa
    let ellSubspace :
        Fin (Nat.log 2 n + 1) ->
          Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns) :=
      fun headEll =>
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition
          headKappa.1 headEll.1
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))
    have hpKappa' : p ∈ ⨆ headEll, ellSubspace headEll := by
      simpa [headSubspace, ellSubspace] using hpKappa
    refine Submodule.iSup_induction (p := ellSubspace) (x := p)
      (motive := fun p =>
        routeBSPDPGeneratorRow M n hn2 htb hns p S shift ∈ U)
      hpKappa' ?_ ?_ ?_
    · intro headEll p hpSummand
      exact
        hconst headKappa.1 headEll.1 spdpKappa ell p S shift hpSummand
          (Nat.le_of_lt_succ headKappa.2)
          (Nat.le_of_lt_succ headEll.2)
          hSlen hshiftDegree hSlog hshiftLog hshiftVars hadm
    · change routeBSPDPGeneratorRow M n hn2 htb hns 0 S shift ∈ U
      rw [routeBSPDPGeneratorRow_zero]
      exact Submodule.zero_mem U
    · intro p r hp hr
      change
        routeBSPDPGeneratorRow M n hn2 htb hns (p + r) S shift ∈ U
      rw [routeBSPDPGeneratorRow_add]
      exact Submodule.add_mem U hp hr
  · change routeBSPDPGeneratorRow M n hn2 htb hns 0 S shift ∈ U
    rw [routeBSPDPGeneratorRow_zero]
    exact Submodule.zero_mem U
  · intro p r hp hr
    change routeBSPDPGeneratorRow M n hn2 htb hns (p + r) S shift ∈ U
    rw [routeBSPDPGeneratorRow_add]
    exact Submodule.add_mem U hp hr

/-- Generator-level second-pass closure is sufficient for the positive
stable-generator-map target. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hgen :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
      M n hn2 htb hns :=
  routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_constituentSecondPassClosure
    M n hn2 htb hns
    (routeBRicherSPDPStableCandidate_headSpanConstituentSecondPassClosure_of_generatorSecondPassClosure
      M n hn2 htb hns hgen)

/-- Stable generator maps rule out a concrete head-span generator-map escape.
-/
theorem routeBRicherSPDPStableCandidate_no_headSpanGeneratorMapEscape_of_stableGeneratorMaps
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hstable :
      RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns) :
    ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns := by
  rintro ⟨spdpKappa, ell, p, S, shift, hpHead, hSlen, hshiftDegree,
    hSlog, hshiftLog, hshiftVars, hadm, hnotHead⟩
  let U := routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns
  let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
  have hmap : L p ∈ Submodule.map L U := ⟨p, hpHead, rfl⟩
  exact hnotHead
    (by
      simpa [L, U, routeBSPDPGeneratorRowLinearMap_apply] using
        hstable spdpKappa ell S shift hSlen hshiftDegree hSlog
          hshiftLog hshiftVars hadm hmap)

/-- If no concrete head-span generator-map escape exists, then the canonical
head span is stable under all log-window generator maps. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_no_headSpanGeneratorMapEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hno :
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
      M n hn2 htb hns := by
  intro spdpKappa ell S shift hSlen hshiftDegree hSlog hshiftLog
    hshiftVars hadm q hq
  let U := routeBRicherSPDPStableCandidateLogWindowHeadSpan M n hn2 htb hns
  let L := routeBSPDPGeneratorRowLinearMap M n hn2 htb hns S shift
  rcases hq with ⟨p, hpHead, rfl⟩
  by_contra hnotHead
  exact hno
    ⟨spdpKappa, ell, p, S, shift, hpHead, hSlen, hshiftDegree,
      hSlog, hshiftLog, hshiftVars, hadm,
      by
        simpa [L, U, routeBSPDPGeneratorRowLinearMap_apply] using hnotHead⟩

/-- The positive stable-generator-map target is exactly absence of the
head-span generator-map escape witness. -/
theorem routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_iff_no_headSpanGeneratorMapEscape
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherSPDPStableCandidateLogWindowHeadSpanStableGeneratorMaps
        M n hn2 htb hns ↔
      ¬ RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
        M n hn2 htb hns := by
  constructor
  · exact
      routeBRicherSPDPStableCandidate_no_headSpanGeneratorMapEscape_of_stableGeneratorMaps
        M n hn2 htb hns
  · exact
      routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_no_headSpanGeneratorMapEscape
        M n hn2 htb hns

/-! ## Axiom audit anchors -/

#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorSecondPassClosure
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadSpanConstituentSecondPassClosure
#print axioms RouteBRicherSPDPStableCandidateLogWindowHeadSpanGeneratorMapEscapeWitness
#print axioms routeBRicherSPDPStableCandidate_headSpanConstituentSecondPassClosure_of_generatorSecondPassClosure
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_constituentSecondPassClosure
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_generatorSecondPassClosure
#print axioms routeBRicherSPDPStableCandidate_no_headSpanGeneratorMapEscape_of_stableGeneratorMaps
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_of_no_headSpanGeneratorMapEscape
#print axioms routeBRicherSPDPStableCandidate_logWindowHeadSpanStableGeneratorMaps_iff_no_headSpanGeneratorMapEscape

end PallLean.Paper93.Paper283
