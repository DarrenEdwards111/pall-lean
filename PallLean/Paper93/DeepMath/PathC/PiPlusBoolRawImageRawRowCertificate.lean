import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageRawRowGeneratorCriterion

/-!
# Row-certificate criterion for raw-row Pi+ generator transport

The generator criterion asks each transformed raw SPDP generator to belong to the
opposite raw row span.  This file lowers that membership obligation to the most
concrete row-certificate form: exhibit an actual source generator whose row is
definitionally equal to the target row.

This is the next algebraic surface for the concrete Cook--Levin `Pi+` action:
prove exact raw derivative-row identities, and the span membership follows.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- Row-certificate version of raw-row generator preservation.  For every raw
SPDP generator of `gauge q`, exhibit a raw SPDP generator of `q` equal to it. -/
def PiPlusRawRowGeneratorPreservationCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
    ∃ (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m' : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S'.length = κ ∧
        m'.totalDegree ≤ ℓ ∧
          m'.vars ⊆ S'.toFinset ∧
            isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S' ∧
              m * iterDerivList S (piP.gauge q) = m' * iterDerivList S' q

/-- Row-certificate version of raw-row generator reflection.  For every raw SPDP
generator of `q`, exhibit a raw SPDP generator of `gauge q` equal to it. -/
def PiPlusRawRowGeneratorReflectionCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
    ∃ (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m' : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S'.length = κ ∧
        m'.totalDegree ≤ ℓ ∧
          m'.vars ⊆ S'.toFinset ∧
            isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S' ∧
              m * iterDerivList S q = m' * iterDerivList S' (piP.gauge q)

/-- Row certificates imply generator-level preservation by inserting the
exhibited row into the raw span. -/
theorem piPlusRawRowGeneratorPreservation_of_certificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hcert : PiPlusRawRowGeneratorPreservationCertificate piP κ ℓ q) :
    PiPlusRawRowGeneratorPreservation piP κ ℓ q := by
  intro S m hlen hdeg hvars hadm
  rcases hcert S m hlen hdeg hvars hadm with
    ⟨S', m', hlen', hdeg', hvars', hadm', hrow⟩
  rw [hrow]
  exact Submodule.subset_span ⟨S', m', hlen', hdeg', hvars', hadm', rfl⟩

/-- Row certificates imply generator-level reflection by inserting the exhibited
row into the raw span. -/
theorem piPlusRawRowGeneratorReflection_of_certificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hcert : PiPlusRawRowGeneratorReflectionCertificate piP κ ℓ q) :
    PiPlusRawRowGeneratorReflection piP κ ℓ q := by
  intro S m hlen hdeg hvars hadm
  rcases hcert S m hlen hdeg hvars hadm with
    ⟨S', m', hlen', hdeg', hvars', hadm', hrow⟩
  rw [hrow]
  exact Submodule.subset_span ⟨S', m', hlen', hdeg', hvars', hadm', rfl⟩

/-- Two-sided raw row certificates imply corrected raw-image rank invariance. -/
theorem piPlusBoolRawImageRankInvariant_of_rawRowCertificates
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (κ ℓ : ℕ)
    (q : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hpres : PiPlusRawRowGeneratorPreservationCertificate piP κ ℓ q)
    (hreflect : PiPlusRawRowGeneratorReflectionCertificate piP κ ℓ q) :
    boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge q) =
      boolRawImageBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ q :=
  piPlusBoolRawImageRankInvariant_of_rawRowGeneratorEquivalence piP κ ℓ q
    (piPlusRawRowGeneratorPreservation_of_certificate piP κ ℓ q hpres)
    (piPlusRawRowGeneratorReflection_of_certificate piP κ ℓ q hreflect)

/-- Paper-scale row-certificate preservation at the NP window. -/
def PaperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowGeneratorPreservationCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale row-certificate reflection at the NP window. -/
def PaperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRowGeneratorReflectionCertificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Paper-scale row certificates imply generator preservation. -/
theorem paperScaleCookLevinPiPlusRawRowGeneratorPreservation_of_certificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcert : PaperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGeneratorPreservation M htb hns := by
  unfold PaperScaleCookLevinPiPlusRawRowGeneratorPreservation
  exact piPlusRawRowGeneratorPreservation_of_certificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hcert

/-- Paper-scale row certificates imply generator reflection. -/
theorem paperScaleCookLevinPiPlusRawRowGeneratorReflection_of_certificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcert : PaperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate M htb hns) :
    PaperScaleCookLevinPiPlusRawRowGeneratorReflection M htb hns := by
  unfold PaperScaleCookLevinPiPlusRawRowGeneratorReflection
  exact piPlusRawRowGeneratorReflection_of_certificate
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hcert

/-- Paper-scale row certificates give the corrected raw-image rank-invariance
payload. -/
theorem paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowCertificates
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpres : PaperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate M htb hns)
    (hreflect : PaperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolRawImageRankInvariant M htb hns :=
  paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowGeneratorEquivalence
    M htb hns
    (paperScaleCookLevinPiPlusRawRowGeneratorPreservation_of_certificate
      M htb hns hpres)
    (paperScaleCookLevinPiPlusRawRowGeneratorReflection_of_certificate
      M htb hns hreflect)

/-- No-decider surface where raw-image rank invariance is reduced to exact raw
row certificates. -/
theorem no_decidesSAT_at_paperScale_of_rawRowCertificatesAndLegacyPostGaugePBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HPlegacy : DecidesSAT M → blockedSpdpRankInc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804) + 1) (Nat.log 2 (2 ^ 804) + 0)
      ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
        (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))
      Finset.univ ≤ (2 ^ 804) ^ 200)
    (Hpres : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowGeneratorPreservationCertificate M htb hns)
    (Hreflect : DecidesSAT M →
      PaperScaleCookLevinPiPlusRawRowGeneratorReflectionCertificate M htb hns)
    (HrawNP : DecidesSAT M → PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinBoolRawImageSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  exact no_decidesSAT_at_paperScale_of_rawRowGeneratorsAndLegacyPostGaugePBound
    M htb hns HPlegacy
    (fun hdec => paperScaleCookLevinPiPlusRawRowGeneratorPreservation_of_certificate
      M htb hns (Hpres hdec))
    (fun hdec => paperScaleCookLevinPiPlusRawRowGeneratorReflection_of_certificate
      M htb hns (Hreflect hdec))
    HrawNP Hker

/-! ## Axiom audit anchors -/

#print axioms piPlusRawRowGeneratorPreservation_of_certificate
#print axioms piPlusRawRowGeneratorReflection_of_certificate
#print axioms piPlusBoolRawImageRankInvariant_of_rawRowCertificates
#print axioms paperScaleCookLevinPiPlusBoolRawImageRankInvariant_of_rawRowCertificates
#print axioms no_decidesSAT_at_paperScale_of_rawRowCertificatesAndLegacyPostGaugePBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
