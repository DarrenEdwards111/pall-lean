import PallLean.Paper93.Paper283.RouteBRicherGaugeReducedCertificate
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNPBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeKeepFirstMoves

/-!
# Concrete Route B finite-row NP witness

This file instantiates the NP-side row data for the finite-span Route B
candidate with the smallest concrete row family: the flat embedded Cook-Levin
identity-minor witness itself.

The construction is intentionally only NP-facing.  It does not assert the
separate Route B SPDP-containment or P-window cover obligations.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The concrete flat coupled-sheet witness for Route B: the Cook-Levin
compiled polynomial, viewed as a coupled-sheet polynomial for the flat
zero-tableau split. -/
noncomputable def routeBRicherConcreteNPWitnessQ
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns) :=
  compiledPoly (cook_levin_compilation M n hn2 htb hns)

/-- The one concrete finite witness row: the flat embedding of the concrete
Cook-Levin coupled-sheet witness. -/
noncomputable def routeBRicherConcreteNPWitnessRows
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Fin 1 -> SATDeciderGaugeSpace M n hn2 htb hns :=
  fun _ =>
    CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
      (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)

/-- The concrete finite witness row is exactly the embedded source row. -/
theorem routeBRicherConcreteNPWitnessRows_eq_embed
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (i : Fin 1) :
    routeBRicherConcreteNPWitnessRows M n hn2 htb hns i =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns) := by
  rfl

/-- Pulling the Cook-Levin partition back along the flat split's `inlU`
returns the same partition. -/
theorem flatCookLevinUVSplit_pullbackPartition_eq
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    pullbackPartition
        (cook_levin_compilation M n hn2 htb hns).partition
        (flatCookLevinUVSplit M n hn2 htb hns).inlU =
      (cook_levin_compilation M n hn2 htb hns).partition := by
  unfold pullbackPartition
  congr 1

/-- In the flat zero-tableau split, embedding the concrete coupled-sheet
witness gives back the Cook-Levin compiled polynomial. -/
theorem routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns) =
      compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  unfold CoupledSheetPoly.embed routeBRicherConcreteNPWitnessQ
  have hidx :
      (flatCookLevinUVSplit M n hn2 htb hns).inlU =
        (id : Fin (flatCookLevinUVSplit M n hn2 htb hns).numU ->
          Fin (flatCookLevinUVSplit M n hn2 htb hns).total) := by
    funext i
    exact Fin.ext rfl
  rw [hidx]
  exact MvPolynomial.rename_id_apply
    (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- The concrete source witness exposes the same linear coefficient as the
Cook-Levin compiled polynomial: at the second flat Cook-Levin variable the
coefficient is `-1`. -/
theorem routeBRicherConcreteNPWitnessQ_coeff_secondVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns) = (-1 : Rat) := by
  unfold routeBRicherConcreteNPWitnessQ
  exact compiledPoly_coeff_secondVar M n hn2 htb hns

/-- Explicit nonzero monomial coefficient for the concrete source witness. -/
theorem routeBRicherConcreteNPWitnessQ_coeff_secondVar_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns) ≠ 0 := by
  rw [routeBRicherConcreteNPWitnessQ_coeff_secondVar]
  norm_num

/-- The concrete head row has the exposed coefficient `-1` at the second flat
Cook-Levin variable. -/
theorem routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) = (-1 : Rat) := by
  rw [routeBRicherConcreteNPWitnessRows_eq_embed,
    routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly]
  exact compiledPoly_coeff_secondVar M n hn2 htb hns

/-- Explicit nonzero monomial coefficient for the concrete head row. -/
theorem routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_ne_zero
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns 0) ≠ 0 := by
  rw [routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar]
  norm_num

/-- Concrete source identity-minor lower bound for the Route B flat
coupled-sheet witness, obtained from the existing Lemma 124 Cook-Levin lower
bound. -/
theorem routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (routeBRicherConcreteNPWitnessQ M n hn2 htb hns) := by
  unfold SourceIdentityMinorLowerBound routeBRicherConcreteNPWitnessQ
  rw [flatCookLevinUVSplit_pullbackPartition_eq M n hn2 htb hns]
  exact lemma124_compiledPoly_identity_minor_lower_bound M n hn hn2 htb hns

/-- The concrete one-row finite-span candidate sends `compiledPoly` to the
same image as the embedded source witness. -/
theorem routeBRicherConcreteNPWitnessRows_extracts_compiled
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns))
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns))
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns)
          (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) := by
  rw [routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly]

/-- Concrete finite-row-span certificate for the Route B NP fixed-row
transport surface.  The only numeric assumption is the existing Lemma 124
large-`n` threshold. -/
noncomputable def routeBRicherConcreteNPFixedFiniteRowSpanCertificate
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBRicherGaugeNPFixedFiniteRowSpanCertificate M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) where
  Q := routeBRicherConcreteNPWitnessQ M n hn2 htb hns
  rowCount := 1
  row := routeBRicherConcreteNPWitnessRows M n hn2 htb hns
  fixes_row := by
    intro i
    exact routeBRicherFiniteRowsCandidateGauge_fixes_row
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns) i
  embedded_mem_rowSpan := by
    exact Submodule.subset_span ⟨0, rfl⟩
  extracts_compiled_to_embed := by
    rw [← routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly M n hn2 htb hns]
    exact routeBRicherFiniteRowsCandidateGauge_fixes_row
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns) 0
  source_lower_bound :=
    routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
      M n hn hn2 htb hns

/-- Concrete NP component for the one-row finite-span candidate. -/
theorem routeBSATProjectedNPIdentityMinorLowerBound_of_concreteNPWitnessRows
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns))) :=
  routeBSATProjectedNPIdentityMinorLowerBound_of_richerGaugeNPFixedFiniteRowSpanCertificate
    M n hn2 htb hns
    (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns))
    (routeBRicherConcreteNPFixedFiniteRowSpanCertificate
      M n hn hn2 htb hns)

/-- Route B transport certificate using the concrete one-row NP witness, once
the non-NP Route B containment and P-window cover inputs are supplied. -/
theorem routeBRicherConcreteNP_transportCertificate
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
        (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)) := by
  exact
    routeBRicherFiniteRowsCandidateGauge_transportCertificate
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)
      hcontain cover
      (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)
      0
      (by rfl)
      (routeBRicherConcreteNPWitnessRows_extracts_compiled M n hn2 htb hns)
      (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
        M n hn hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms flatCookLevinUVSplit_pullbackPartition_eq
#print axioms routeBRicherConcreteNPWitnessQ_embed_eq_compiledPoly
#print axioms routeBRicherConcreteNPWitnessQ_coeff_secondVar
#print axioms routeBRicherConcreteNPWitnessQ_coeff_secondVar_ne_zero
#print axioms routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar
#print axioms routeBRicherConcreteNPWitnessRows_zero_coeff_secondVar_ne_zero
#print axioms routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
#print axioms routeBRicherConcreteNPWitnessRows_extracts_compiled
#print axioms routeBRicherConcreteNPFixedFiniteRowSpanCertificate
#print axioms routeBSATProjectedNPIdentityMinorLowerBound_of_concreteNPWitnessRows
#print axioms routeBRicherConcreteNP_transportCertificate

end PallLean.Paper93.Paper283
