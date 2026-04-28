import PallLean.Paper93.DeepMath.PathB.ZeroProfileQuotientTypeCompression
import PallLean.Paper93.DeepMath.PathB.ZeroProfileConcreteNormalFormProgress
import PallLean.Paper93.Paper283.RouteBProjectedPWindowAssembly

/-!
# Route B zero-profile quotiented compression proof

This file instantiates the projected/quotiented zero-profile target from the
existing normal-form and quotient-type certificate machinery.  The concrete
singleton quotient is reduced to the exact remaining arithmetic condition:
the projected quotient finrank must fit inside `withinProfileBound`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- A Cook-Levin projected normal-form obligation gives an actual
quotiented zero-profile common-span target as soon as its type budget fits the
within-profile budget. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_exists_of_projectedNormalFormObligation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {typeBudget : Nat}
    (hnf :
      CookLevinZeroProfileProjectedNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n)) :
    Exists fun project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat =>
        CookLevinZeroProfileQuotientedShiftCommonSpan
          M n hn2 htb hns project := by
  rcases hnf with ⟨cert⟩
  exact
    ⟨cert.project,
      cookLevinZeroProfileQuotientedShiftCommonSpan_of_projectedNormalFormCertificate
        M n hn2 htb hns cert hbudget⟩

/-- A quotient type-space certificate also directly supplies the quotiented
zero-profile target; no residual span is paid here. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_of_quotientTypeSpaceCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {typeBudget : Nat}
    (cert :
      ZeroProfileQuotientTypeSpaceCertificate (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        typeBudget)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns cert.project := by
  refine ⟨cert.project_idempotent, cert.killsSingleton, ?_⟩
  exact
    zeroProfileProjectedCommonSpanWithBudget_mono
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      cert.project
      (zeroProfileProjectedCommonSpanWithBudget_of_quotientTypeSpaceCertificate
        (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        cert)
      hbudget

/-- Existential quotient/type normal-form obligations close the quotiented
zero-profile target under the same projected type-budget bound. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_exists_of_quotientTypeNormalFormObligation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {typeBudget : Nat}
    (hquot :
      CookLevinZeroProfileQuotientTypeNormalFormObligation
        M n hn2 htb hns typeBudget)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n)) :
    Exists fun project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat =>
        CookLevinZeroProfileQuotientedShiftCommonSpan
          M n hn2 htb hns project := by
  rcases hquot with ⟨cert⟩
  exact
    ⟨cert.project,
      cookLevinZeroProfileQuotientedShiftCommonSpan_of_quotientTypeSpaceCertificate
        M n hn2 htb hns cert hbudget⟩

/-- Exact selected-projection constructor: idempotence, singleton-kernel
containment, and the projected shifted-span finrank bound are precisely enough
to close the quotiented zero-profile target. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_of_projectedShiftSpan_finrank
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hproject : project.comp project = project)
    (hkills :
      ZeroProfileProjectionKillsSingletonShifts
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project)
    (hbudget :
      Module.finrank Rat
          ↥(zeroProfileProjectedShiftSpan (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            project) <=
        withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns project := by
  refine ⟨hproject, hkills, ?_⟩
  exact
    zeroProfileProjectedCommonSpanWithBudget_of_projectedShiftSpan_finrank
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project hbudget

/-- For any selected projection already known to be an idempotent quotient
killing singleton-shift rows, the quotiented zero-profile target is equivalent
to the exact projected shifted-span finrank bound. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_iff_projectedShiftSpan_finrank
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hproject : project.comp project = project)
    (hkills :
      ZeroProfileProjectionKillsSingletonShifts
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project ↔
      Module.finrank Rat
          ↥(zeroProfileProjectedShiftSpan (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
            project) <=
        withinProfileBound (Nat.log 2 n) := by
  constructor
  · exact
      cookLevinZeroProfileQuotientedShiftCommonSpan_projectedShiftSpan_finrank_le
        M n hn2 htb hns project
  · exact
      cookLevinZeroProfileQuotientedShiftCommonSpan_of_projectedShiftSpan_finrank
        M n hn2 htb hns project hproject hkills

/-- A projected common-span certificate for any selected projection reduces the
exact shifted-span finrank budget to the certificate budget. -/
theorem cookLevinZeroProfileProjectedShiftSpan_finrank_le_withinProfileBound_of_projectedCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    {budget : Nat}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project budget)
    (hbudget : budget <= withinProfileBound (Nat.log 2 n)) :
    Module.finrank Rat
        ↥(zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project) <=
      withinProfileBound (Nat.log 2 n) := by
  classical
  rcases hspan with ⟨G, hG_card, hG_span⟩
  have hle :
      zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project ≤
        Submodule.span Rat
          (↑G : Set (MvPolynomial (Fin n) Rat)) := by
    rw [zeroProfileProjectedShiftSpan_eq_span_projectedShiftImageSet]
    exact Submodule.span_le.mpr hG_span
  haveI hprojFinite :
      Module.Finite Rat
        ↥(zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
          project) :=
    zeroProfileProjectedShiftSpan_finite (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
      project
  haveI hspanFinite :
      Module.Finite Rat
        ↥(Submodule.span Rat
          (↑G : Set (MvPolynomial (Fin n) Rat))) :=
    Module.Finite.span_of_finite Rat (Finset.finite_toSet G)
  exact
    (Submodule.finrank_mono hle).trans
      ((finrank_span_finset_le_card G).trans (hG_card.trans hbudget))

/-- A projected common-span certificate for the concrete singleton quotient
directly proves the exact singleton projected type-budget inequality. -/
theorem cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_projectedCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {budget : Nat}
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        budget)
    (hbudget : budget <= withinProfileBound (Nat.log 2 n)) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
      withinProfileBound (Nat.log 2 n) := by
  simpa [zeroProfileSingletonQuotientProjectedTypeBudget] using
    cookLevinZeroProfileProjectedShiftSpan_finrank_le_withinProfileBound_of_projectedCommonSpan
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      hspan hbudget

/-- A quotient type map for the concrete singleton quotient reduces the exact
projected type-budget gate to its local type budget. -/
theorem cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_projectedTypeMap
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {typeBudget : Nat}
    (A : ZeroProfileQuotientTypeAlphabet n typeBudget)
    (hmap :
      ZeroProfileProjectedGeneratorTypeMap (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) A
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)))
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n)) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
      withinProfileBound (Nat.log 2 n) := by
  exact
    cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_projectedCommonSpan
      M n hn2 htb hns
      (zeroProfileProjectedCommonSpanWithBudget_of_projectedTypeMap
        (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        A
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        hmap)
      hbudget

/-- A projected normal-form row map for the concrete singleton quotient
reduces the exact projected type-budget gate to the profile-compression
normal-form budget. -/
theorem cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_normalFormRowMap
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {typeBudget : Nat}
    (F : ZeroProfileProjectedNormalFormFamily n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileProjectedNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        F)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n)) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
      withinProfileBound (Nat.log 2 n) := by
  exact
    cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_projectedCommonSpan
      M n hn2 htb hns
      (zeroProfileProjectedCommonSpanWithBudget_of_normalFormRowMap
        (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        F hmap)
      hbudget

/-- A finite normal-form classifier for the concrete singleton quotient
instantiates the exact projected type-budget gate.  This is the
finite-normal-form version of the reducer above, keeping the local normal-form
source data visible. -/
theorem cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_finiteClassifier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {typeBudget : Nat}
    {A : ZeroProfileFiniteNormalFormAlphabet (Nat.log 2 n)}
    (D : ZeroProfileFiniteNormalFormFamilyData A n typeBudget)
    (C :
      ZeroProfileFiniteNormalFormRowClassifier
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n)) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
      withinProfileBound (Nat.log 2 n) :=
  PallLean.Paper93.DeepMath.PathB.zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_finiteNormalFormClassifier
    M n hn2 htb hns D C hbudget

/-- A concrete normal-form row classifier for the concrete singleton quotient
instantiates the exact projected type-budget gate via the finite-normal-form
classifier bridge.  No shifted-support enumeration is used. -/
theorem cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteClassifier
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {typeBudget : Nat}
    (D : ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n)) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
      withinProfileBound (Nat.log 2 n) :=
  zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteRowMap
    M n hn2 htb hns D hmap hbudget

/-- Concrete singleton-quotient constructor: the existing exact projected
quotient type-space certificate proves the quotiented target once the exact
projected quotient finrank fits inside `withinProfileBound`. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_of_singletonQuotient_projectedTypeBudget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) := by
  simpa [zeroProfileSingletonQuotientTypeSpaceCertificate_projectedFinrank] using
    cookLevinZeroProfileQuotientedShiftCommonSpan_of_quotientTypeSpaceCertificate
      M n hn2 htb hns
      (zeroProfileSingletonQuotientTypeSpaceCertificate_projectedFinrank
        (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      hbudget

/-- Necessity of the remaining singleton-quotient arithmetic: any proof of
the quotiented target for the concrete singleton quotient forces the exact
projected quotient finrank to fit inside `withinProfileBound`. -/
theorem zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_quotientedShiftCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
      withinProfileBound (Nat.log 2 n) := by
  simpa [zeroProfileSingletonQuotientProjectedTypeBudget] using
    cookLevinZeroProfileQuotientedShiftCommonSpan_projectedShiftSpan_finrank_le
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      hquot

/-- For the concrete singleton quotient, the quotiented zero-profile target is
equivalent to the exact projected quotient finrank bound.  This isolates the
remaining hard hypothesis as a pure projected compression bound. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_singletonQuotient_iff_projectedTypeBudget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i)) ↔
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n) := by
  constructor
  · exact
      zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_quotientedShiftCommonSpan
        M n hn2 htb hns
  · exact
      cookLevinZeroProfileQuotientedShiftCommonSpan_of_singletonQuotient_projectedTypeBudget
        M n hn2 htb hns

/-- P-window assembly specialization using the concrete singleton quotient.
The only zero-profile hard hypothesis is the projected quotient finrank bound;
the separate Route B hypothesis remains the projected P-window containment. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPSideBound_of_singletonQuotient_projectedTypeBudget
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hcontrol :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) :=
  routeBPaperFaithfulPiPhiHeadSpan_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
    M n hn2 htb hns
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
    (cookLevinZeroProfileQuotientedShiftCommonSpan_of_singletonQuotient_projectedTypeBudget
      M n hn2 htb hns hbudget)
    hcontrol

/-! ## Axiom audit anchors -/

#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_exists_of_projectedNormalFormObligation
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_of_quotientTypeSpaceCertificate
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_exists_of_quotientTypeNormalFormObligation
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_of_projectedShiftSpan_finrank
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_iff_projectedShiftSpan_finrank
#print axioms cookLevinZeroProfileProjectedShiftSpan_finrank_le_withinProfileBound_of_projectedCommonSpan
#print axioms cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_projectedCommonSpan
#print axioms cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_projectedTypeMap
#print axioms cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_normalFormRowMap
#print axioms cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_finiteClassifier
#print axioms cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteClassifier
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_of_singletonQuotient_projectedTypeBudget
#print axioms zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_quotientedShiftCommonSpan
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_singletonQuotient_iff_projectedTypeBudget
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPSideBound_of_singletonQuotient_projectedTypeBudget

end PallLean.Paper93.Paper283
