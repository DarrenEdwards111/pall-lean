import PallLean.Paper93.Paper283.RouteBProjectedPWindowAssembly

/-!
# Route B projected P-window control proof

This file sharpens the remaining projected P-window control obligation for
the PiPhi/head-span gauge.  The broad containment reduces to a pointwise row
identity: every generator row of the selected projected P-window must be the
chosen quotient projection of the corresponding zero-profile shifted
base-product row.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MvPolynomial
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- Minimal remaining row identity for the PiPhi/head-span projected P-window.

For each generator row queried by `mlBlockedSpdpSubspace` at the P-window
parameters, the selected PiPhi/head-span projected row must agree with the
quotient projection of the matching zero-profile shifted base-product row.

This is intentionally pointwise and specific to the PiPhi/head-span gauge; it
does not introduce a broad policy interface for arbitrary gauges. -/
def RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
  (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) =
      project
        (mlProj
          (shift *
            Finset.univ.prod
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)))

/-- Exact generator-membership reduction for the PiPhi/head-span projected
P-window containment. -/
def RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileGeneratorReduction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) : Prop :=
  ∀ (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat),
    S.length = Nat.log 2 n →
    shift.totalDegree ≤ Nat.log 2 n →
    shift.vars ⊆ S.toFinset →
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S →
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project

/-- The pointwise row identity gives membership of every projected P-window
generator in the projected zero-profile shifted span. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowGenerator_mem_zeroProfileProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project)
    (S : List (Fin n)) (shift : MvPolynomial (Fin n) Rat)
    (hSlen : S.length = Nat.log 2 n)
    (hshiftDegree : shift.totalDegree ≤ Nat.log 2 n)
    (hshiftVars : shift.vars ⊆ S.toFinset)
    (hadm :
      SPDP.isBlockAdmissible
        (cook_levin_compilation M n hn2 htb hns).partition S) :
    mlProj
        (shift * SPDP.iterDerivList S
          ((routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
            (compiledPoly (cook_levin_compilation M n hn2 htb hns)))) ∈
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project := by
  classical
  have hzero :
      mlProj
          (shift *
            Finset.univ.prod
              (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ∈
        zeroProfileShiftImageSet (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) := by
    simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
      Set.mem_singleton_iff]
    exact ⟨S, le_of_eq hSlen, shift, hshiftVars, rfl⟩
  have hproject :
      project
          (mlProj
            (shift *
              Finset.univ.prod
                (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) ∈
        zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project := by
    exact Submodule.mem_map_of_mem (Submodule.subset_span hzero)
  rw [hrow S shift hSlen hshiftDegree hshiftVars hadm]
  exact hproject

/-- The original broad containment is exactly the generator-by-generator
zero-profile membership check. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project ↔
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileGeneratorReduction
        M n hn2 htb hns project := by
  classical
  constructor
  · intro hcontrol S shift hSlen hshiftDegree hshiftVars hadm
    have hle :
        routeBRicherGaugeProjectedPWindowSubspace M n hn2 htb hns
            (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) ≤
          zeroProfileProjectedShiftSpan (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            project := by
      simpa [RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection,
        RouteBProjectedPWindowControlledByZeroProfileProjection] using
        hcontrol
    apply hle
    unfold routeBRicherGaugeProjectedPWindowSubspace
    unfold mlBlockedSpdpSubspace
    exact Submodule.subset_span
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
  · intro hgen
    rw [RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection,
      RouteBProjectedPWindowControlledByZeroProfileProjection]
    unfold routeBRicherGaugeProjectedPWindowSubspace
    unfold mlBlockedSpdpSubspace
    refine Submodule.span_le.mpr ?_
    intro q hq
    rcases hq with
      ⟨S, shift, hSlen, hshiftDegree, hshiftVars, hadm, rfl⟩
    exact hgen S shift hSlen hshiftDegree hshiftVars hadm

/-- The pointwise row identity proves the full projected P-window containment
needed by the projected zero-profile assembly. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
      M n hn2 htb hns project := by
  exact
    (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
      M n hn2 htb hns project).mpr
    (fun S shift hSlen hshiftDegree hshiftVars hadm =>
    routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowGenerator_mem_zeroProfileProjection
      M n hn2 htb hns project hrow S shift
      hSlen hshiftDegree hshiftVars hadm)

/-! ## Axiom audit anchors -/

#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileGeneratorReduction
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowGenerator_mem_zeroProfileProjection
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_iff_generatorReduction
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity

end PallLean.Paper93.Paper283
