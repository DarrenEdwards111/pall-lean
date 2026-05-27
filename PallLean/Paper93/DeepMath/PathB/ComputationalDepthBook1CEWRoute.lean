import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStrictPortStandardBridge

/-!
# Book 1 CEW/SPDP epistemic-boundary route

Book 1 suggests that the active obstruction should be phrased as an
epistemic-boundary/CEW route, not as containment of the same-sheet God-Move rank
inside a low-action live-boundary rank.

This file records that route as an explicit, audit-friendly port:

* P observers/deciders have bounded contextual-entanglement width (CEW).
* Bounded CEW gives polynomial SPDP rank.
* The hard NP family has the calibrated Ramanujan/Tseitin super-polynomial
  SPDP rank `n^(log₂ n / 4)`.
* Any SAT decider would transport the hard-family rank into its P-side rank.
* The super-polynomial lower bound eventually beats every polynomial upper
  bound; this last growth fact is proved below, not assumed.

No old Step4 wrapper is imported here, and no CEW axiom is hidden as a theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Hard-sheet extraction model for Book 1.

This isolates the non-P-vs-NP-hard part of `hardRank_le_extracted`: if the
extracted God-Move sheet is chosen to carry the same hard-family SPDP surface,
then the hard-family rank is visible on the extracted sheet by a direct
rank-surface comparison.

The remaining mathematical content is therefore not the inequality below, but
instantiating `extractedRank` with the actual Ramanujan/Tseitin/identity-minor
sheet and proving the sheet comparison field. -/
structure Book1HardSheetExtractionModel
    (enc : ThreeCNFEncoding)
    (hardRank : Nat -> Nat) where
  extractedRank : TuringMachine.DTM -> Nat -> Nat
  hardSheet_le_extracted :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat, hardRank n <= extractedRank M n

/-- The calibrated Ramanujan/Tseitin hard-rank scale currently proved by the
sound PD/identity-minor side of the development.  The `/4` is intentional: it
matches the concrete binomial lower bound already available in `GodMoveCore`,
and still beats every fixed polynomial. -/
def book1CalibratedRamanujanTseitinHardRank (n : Nat) : Nat :=
  n ^ (Nat.log 2 n / 4)

/-- The calibrated hard-rank scale has the Book-1 NP lower bound by definition. -/
theorem book1CalibratedRamanujanTseitinHardNPLowerBound :
    forall n : Nat,
      n ^ (Nat.log 2 n / 4) <= book1CalibratedRamanujanTseitinHardRank n := by
  intro n
  rfl

/-- A concrete same-target Ramanujan/Tseitin certificate for one extracted
rank value.

This is the Book-1 hard-sheet object tied to the actual `GodMoveCore` seam:
the extracted rank is definitionally the blocked-SPDP rank of a selected
`GodMoveExtractionTarget`, and the NP lower bound comes from same-target
PD-matrix/Ramanujan-Tseitin data.  The `timeBound ≤ 4` and `numStates ≤ n`
side conditions are intentionally explicit; they are part of the existing
God-Move target interface and should not be silently fabricated. -/
structure Book1SameTargetRamanujanTseitinRankCertificate
    (M : TuringMachine.DTM) (n r : Nat) where
  hn2 : n >= 2
  htb : M.timeBound <= 4
  hns : M.numStates <= n
  target : GodMoveExtractionTarget M n hn2 htb hns
  sameTargetPD : RouteBNPFromPdMatrixSameTarget target
  rank_eq :
    r = MultilinearSPDP.mlBlockedSpdpRank target.coupledPartition
      (Nat.log 2 n) (Nat.log 2 n) target.coupledPoly

/-- Same-target Ramanujan/Tseitin data proves the calibrated hard lower bound
for the extracted rank value. -/
theorem book1CalibratedHardRank_le_of_sameTargetRamanujanTseitinCertificate
    {M : TuringMachine.DTM} {n r : Nat}
    (C : Book1SameTargetRamanujanTseitinRankCertificate M n r) :
    book1CalibratedRamanujanTseitinHardRank n <= r := by
  have htarget : n ^ (Nat.log 2 n / 4) <=
      MultilinearSPDP.mlBlockedSpdpRank C.target.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) C.target.coupledPoly :=
    routeB_weakened_np_from_same_target_pdMatrix C.sameTargetPD
  calc
    book1CalibratedRamanujanTseitinHardRank n = n ^ (Nat.log 2 n / 4) := rfl
    _ <= MultilinearSPDP.mlBlockedSpdpRank C.target.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) C.target.coupledPoly := htarget
    _ = r := C.rank_eq.symm

/-- A global same-target Ramanujan/Tseitin hard-sheet model.

For paper-scale sizes it requires the real same-target PD/SPDP certificate from
`GodMoveCore`; below the paper threshold it asks for a finite endpoint lower
bound separately.  This avoids pretending that the asymptotic target interface
already covers `n = 0,1,...,2^804-1`. -/
structure Book1SameTargetRamanujanTseitinHardSheetModel
    (enc : ThreeCNFEncoding) where
  extractedRank : TuringMachine.DTM -> Nat -> Nat
  large_sameTarget :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          2 ^ 804 <= n ->
            Book1SameTargetRamanujanTseitinRankCertificate M n (extractedRank M n)
  preThreshold_lower :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            book1CalibratedRamanujanTseitinHardRank n <= extractedRank M n

/-- The real same-target Ramanujan/Tseitin model instantiates the Book-1
hard-sheet extraction bridge. -/
def book1HardSheetExtractionModel_of_sameTargetRamanujanTseitinModel
    {enc : ThreeCNFEncoding}
    (R : Book1SameTargetRamanujanTseitinHardSheetModel enc) :
    Book1HardSheetExtractionModel enc book1CalibratedRamanujanTseitinHardRank where
  extractedRank := R.extractedRank
  hardSheet_le_extracted := by
    intro M hM n
    by_cases hn : 2 ^ 804 <= n
    · exact book1CalibratedHardRank_le_of_sameTargetRamanujanTseitinCertificate
        (R.large_sameTarget M hM n hn)
    · exact R.preThreshold_lower M hM n (Nat.lt_of_not_ge hn)

/-- If the extracted sheet is exactly the calibrated Ramanujan/Tseitin hard
rank function, the hard-sheet extraction model is immediate.  This remains a
sanity-check/modeling baseline; the real same-target bridge above is the
paper-facing route. -/
def book1CalibratedHardSheetExtractionModel (enc : ThreeCNFEncoding) :
    Book1HardSheetExtractionModel enc book1CalibratedRamanujanTseitinHardRank where
  extractedRank := fun _ n => book1CalibratedRamanujanTseitinHardRank n
  hardSheet_le_extracted := by
    intro M hM n
    rfl

/-- The hard-sheet extraction model proves the first half of the split transport
certificate: the hard-family rank appears on the extracted God-Move sheet. -/
theorem hardRank_le_extracted_of_hardSheetExtractionModel
    {enc : ThreeCNFEncoding}
    {hardRank : Nat -> Nat}
    (H : Book1HardSheetExtractionModel enc hardRank) :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat, hardRank n <= H.extractedRank M n := by
  intro M hM n
  exact H.hardSheet_le_extracted M hM n

/-- Explicit bridge between the encoded SAT semantics used by the Book-1 route
and the core `GodMoveCore.DecidesSAT` semantics used by extraction transfer.

This keeps the semantics conversion honest: downstream ambient constructors may
use this field, but we do not silently coerce between the two definitions. -/
structure Book1SATSemanticsBridge (enc : ThreeCNFEncoding) where
  toCoreDecidesSAT :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M -> DecidesSAT M

/-- In the current core `ThreeCNF` model clauses contain only positive
variables, so every formula is satisfiable by the all-true assignment.

This is a local fact about the existing toy SAT syntax.  It is useful for the
semantic bridge below, and it also marks a modeling limitation: once signed
literals are added, this lemma should disappear and the bridge must be proved
from the real parser/encoding semantics. -/
theorem threeCNF_positive_isSatisfiable (φ : ThreeCNF) : φ.IsSatisfiable := by
  refine ⟨fun _ => true, ?_⟩
  intro c hc
  left
  rfl

/-- The current positive-clause encoding semantics imply the core
`DecidesSAT` semantics.

For satisfiable formulas, encoding completeness supplies an input and encoded
SAT correctness supplies acceptance.  For unsatisfiable formulas, the current
positive-only `ThreeCNF` syntax makes the premise contradictory.  This is safe
because it is explicitly tied to the present syntax; it is not a silent coercion
between future richer SAT definitions. -/
def book1SATSemanticsBridge_of_positiveThreeCNFEncoding
    (enc : ThreeCNFEncoding) : Book1SATSemanticsBridge enc where
  toCoreDecidesSAT := by
    intro M hM
    refine ⟨?accepts_sat, ?rejects_unsat⟩
    · intro φ n hn hsize hsat
      rcases enc.complete φ n hsize with ⟨input, henc⟩
      exact ⟨input, (hM hn input φ henc).mpr hsat⟩
    · intro φ n hn hsize hunsat input
      exact False.elim (hunsat (threeCNF_positive_isSatisfiable φ))

/-- One-size ambient no-loss certificate for the same-target Book-1 sheet.

It states that the extracted rank is the blocked-SPDP rank of the selected
same-target sheet, and that the same sheet satisfies the `GodMoveCore`
extraction-transfer inequality into the full Cook--Levin compiled rank.  The
ambient rank is identified with that full compiled rank; no low-action or CEW
collapse is used here. -/
structure Book1SameTargetAmbientRankCertificate
    (M : TuringMachine.DTM) (n extracted ambient : Nat) where
  hardCert : Book1SameTargetRamanujanTseitinRankCertificate M n extracted
  hdecCore : DecidesSAT M
  extractionTransfer :
    GodMoveRouteB_ExtractionTransfer M n hardCert.hn2 hardCert.htb hardCert.hns
      hdecCore hardCert.target
  ambient_eq :
    ambient = MultilinearSPDP.mlBlockedSpdpRank
      (cook_levin_compilation M n hardCert.hn2 hardCert.htb hardCert.hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hardCert.hn2 hardCert.htb hardCert.hns))

/-- Build an ambient rank certificate from an explicit encoded-to-core SAT
semantics bridge.  This is the preferred constructor when the source hypothesis
is `DTMDecidesSATWithEncoding enc M`: the bridge supplies the exact
`DecidesSAT M` witness consumed by `GodMoveRouteB_ExtractionTransfer`. -/
def book1SameTargetAmbientRankCertificate_of_encodedSATBridge
    {enc : ThreeCNFEncoding}
    (S : Book1SATSemanticsBridge enc)
    {M : TuringMachine.DTM} {n extracted ambient : Nat}
    (hM : DTMDecidesSATWithEncoding enc M)
    (hardCert : Book1SameTargetRamanujanTseitinRankCertificate M n extracted)
    (extractionTransfer :
      GodMoveRouteB_ExtractionTransfer M n hardCert.hn2 hardCert.htb hardCert.hns
        (S.toCoreDecidesSAT M hM) hardCert.target)
    (ambient_eq :
      ambient = MultilinearSPDP.mlBlockedSpdpRank
        (cook_levin_compilation M n hardCert.hn2 hardCert.htb hardCert.hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hardCert.hn2 hardCert.htb hardCert.hns))) :
    Book1SameTargetAmbientRankCertificate M n extracted ambient where
  hardCert := hardCert
  hdecCore := S.toCoreDecidesSAT M hM
  extractionTransfer := extractionTransfer
  ambient_eq := ambient_eq

/-- The same-target ambient certificate proves extracted-rank containment in the
full compiled/PAC ambient rank. -/
theorem extracted_le_ambient_of_sameTargetAmbientRankCertificate
    {M : TuringMachine.DTM} {n extracted ambient : Nat}
    (C : Book1SameTargetAmbientRankCertificate M n extracted ambient) :
    extracted <= ambient := by
  calc
    extracted = MultilinearSPDP.mlBlockedSpdpRank C.hardCert.target.coupledPartition
        (Nat.log 2 n) (Nat.log 2 n) C.hardCert.target.coupledPoly := C.hardCert.rank_eq
    _ <= MultilinearSPDP.mlBlockedSpdpRank
        (cook_levin_compilation M n C.hardCert.hn2 C.hardCert.htb C.hardCert.hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n C.hardCert.hn2 C.hardCert.htb C.hardCert.hns)) :=
      C.extractionTransfer
    _ = ambient := C.ambient_eq.symm

/-- Bridge-aware paper-scale ambient payload.

This is the shape downstream code should prove from the actual extraction map:
for each encoded SAT-decider and large `n`, provide the same-target hard
certificate, the extraction transfer using the explicit semantic bridge, and the
ambient-rank definitional equality. -/
structure Book1SameTargetAmbientLargePayload
    {enc : ThreeCNFEncoding}
    (S : Book1SATSemanticsBridge enc)
    (M : TuringMachine.DTM) (hM : DTMDecidesSATWithEncoding enc M)
    (n extracted ambient : Nat) where
  hardCert : Book1SameTargetRamanujanTseitinRankCertificate M n extracted
  extractionTransfer :
    GodMoveRouteB_ExtractionTransfer M n hardCert.hn2 hardCert.htb hardCert.hns
      (S.toCoreDecidesSAT M hM) hardCert.target
  ambient_eq :
    ambient = MultilinearSPDP.mlBlockedSpdpRank
      (cook_levin_compilation M n hardCert.hn2 hardCert.htb hardCert.hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hardCert.hn2 hardCert.htb hardCert.hns))

/-- A bridge-aware large ambient payload produces the older ambient certificate
shape. -/
def Book1SameTargetAmbientLargePayload.toCertificate
    {enc : ThreeCNFEncoding}
    {S : Book1SATSemanticsBridge enc}
    {M : TuringMachine.DTM} {hM : DTMDecidesSATWithEncoding enc M}
    {n extracted ambient : Nat}
    (P : Book1SameTargetAmbientLargePayload S M hM n extracted ambient) :
    Book1SameTargetAmbientRankCertificate M n extracted ambient :=
  book1SameTargetAmbientRankCertificate_of_encodedSATBridge S hM
    P.hardCert P.extractionTransfer P.ambient_eq

/-- Global same-target ambient-rank model.

For paper-scale sizes, the real content is a same-target ambient certificate
built from God-Move extraction transfer.  Below the paper threshold, the model
keeps the finite endpoint comparison explicit. -/
structure Book1SameTargetAmbientCompiledRankModel
    (enc : ThreeCNFEncoding) where
  hardModel : Book1SameTargetRamanujanTseitinHardSheetModel enc
  ambientRank : TuringMachine.DTM -> Nat -> Nat
  large_ambient :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          2 ^ 804 <= n ->
            Book1SameTargetAmbientRankCertificate M n
              (hardModel.extractedRank M n) (ambientRank M n)
  preThreshold_ambient :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            hardModel.extractedRank M n <= ambientRank M n

/-- Bridge-aware global ambient-rank model.

This refines `Book1SameTargetAmbientCompiledRankModel` by requiring the large
ambient data to pass through an explicit encoded-to-core SAT semantics bridge.
It is safer for final instantiation, because it makes the `DecidesSAT M` witness
used by `GodMoveRouteB_ExtractionTransfer` visible. -/
structure Book1SameTargetAmbientCompiledRankModelWithBridge
    (enc : ThreeCNFEncoding) where
  hardModel : Book1SameTargetRamanujanTseitinHardSheetModel enc
  semanticBridge : Book1SATSemanticsBridge enc
  ambientRank : TuringMachine.DTM -> Nat -> Nat
  large_ambient_payload :
    forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        forall n : Nat,
          2 ^ 804 <= n ->
            Book1SameTargetAmbientLargePayload semanticBridge M hM n
              (hardModel.extractedRank M n) (ambientRank M n)
  preThreshold_ambient :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            hardModel.extractedRank M n <= ambientRank M n

/-- Forget the explicit bridge-aware ambient model into the older ambient model
by packaging each large payload as a certificate. -/
def book1SameTargetAmbientCompiledRankModel_of_withBridge
    {enc : ThreeCNFEncoding}
    (A : Book1SameTargetAmbientCompiledRankModelWithBridge enc) :
    Book1SameTargetAmbientCompiledRankModel enc where
  hardModel := A.hardModel
  ambientRank := A.ambientRank
  large_ambient := by
    intro M hM n hn
    exact (A.large_ambient_payload M hM n hn).toCertificate
  preThreshold_ambient := A.preThreshold_ambient

/-- Ambient compiled/PAC rank choice for Book 1.

This is the safe target for the no-loss theorem.  `ambientRank M n` is meant to
be the full compiled/PAC P-side rank before any low-action or CEW collapse is
applied.  `extractedRank M n` is the God-Move extracted sheet rank.

The point of this structure is to prove the transport into the **ambient** rank
only.  It deliberately does not claim transport into a collapsed live-boundary
rank; that stronger target is exactly where the earlier contradiction/no-go
appears. -/
structure Book1AmbientCompiledRankModel
    (enc : ThreeCNFEncoding)
    (hardRank : Nat -> Nat) where
  ambientRank : TuringMachine.DTM -> Nat -> Nat
  hardSheet : Book1HardSheetExtractionModel enc hardRank
  /-- No-loss extraction/PAC monotonicity into the full ambient compiled rank. -/
  extracted_le_ambient :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat, hardSheet.extractedRank M n <= ambientRank M n

/-- The same-target ambient-rank model instantiates the generic Book-1 ambient
compiled-rank model. -/
def book1AmbientCompiledRankModel_of_sameTargetAmbientModel
    {enc : ThreeCNFEncoding}
    (A : Book1SameTargetAmbientCompiledRankModel enc) :
    Book1AmbientCompiledRankModel enc book1CalibratedRamanujanTseitinHardRank where
  ambientRank := A.ambientRank
  hardSheet := book1HardSheetExtractionModel_of_sameTargetRamanujanTseitinModel A.hardModel
  extracted_le_ambient := by
    intro M hM n
    by_cases hn : 2 ^ 804 <= n
    · exact extracted_le_ambient_of_sameTargetAmbientRankCertificate
        (A.large_ambient M hM n hn)
    · exact A.preThreshold_ambient M hM n (Nat.lt_of_not_ge hn)

/-- The ambient compiled/PAC rank model proves the load-bearing no-loss half
`extracted <= pRank` when `pRank` is chosen to be the ambient compiled rank. -/
theorem extracted_le_pRank_of_ambientCompiledRankModel
    {enc : ThreeCNFEncoding}
    {hardRank : Nat -> Nat}
    (A : Book1AmbientCompiledRankModel enc hardRank) :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat, A.hardSheet.extractedRank M n <= A.ambientRank M n := by
  intro M hM n
  exact A.extracted_le_ambient M hM n

/-- Decider transport/no-loss certificate for Book 1.

This is the sharpened form of the monster bridge.  Instead of assuming the final
inequality `hardRank n <= pRank M n` as a black box, the certificate splits it
into the two mathematical movements described by the paper:

1. the hard NP-family rank is realized on an extracted God-Move sheet; and
2. the extracted sheet transports without rank loss into the P-side observer
   rank.

The first field is the hard-family/extraction lower surface; the second is the
PAC/God-Move no-loss transport into the observer's P-side rank. -/
structure Book1DeciderTransportCertificate
    (enc : ThreeCNFEncoding)
    (pRank : TuringMachine.DTM -> Nat -> Nat)
    (hardRank : Nat -> Nat) where
  extractedRank : TuringMachine.DTM -> Nat -> Nat
  hardRank_le_extracted :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat, hardRank n <= extractedRank M n
  extracted_le_pRank :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat, extractedRank M n <= pRank M n

/-- The ambient compiled/PAC rank model also gives the whole split transport
certificate for the ambient rank choice. -/
def book1TransportCertificate_of_ambientCompiledRankModel
    {enc : ThreeCNFEncoding}
    {hardRank : Nat -> Nat}
    (A : Book1AmbientCompiledRankModel enc hardRank) :
    Book1DeciderTransportCertificate enc A.ambientRank hardRank where
  extractedRank := A.hardSheet.extractedRank
  hardRank_le_extracted := hardRank_le_extracted_of_hardSheetExtractionModel A.hardSheet
  extracted_le_pRank := extracted_le_pRank_of_ambientCompiledRankModel A

/-- The split Book-1 transport certificate proves the original no-loss bridge:
any encoded SAT decider transports the hard-family rank into its P-side rank. -/
theorem deciderTransportHardToP_of_book1TransportCertificate
    {enc : ThreeCNFEncoding}
    {pRank : TuringMachine.DTM -> Nat -> Nat}
    {hardRank : Nat -> Nat}
    (T : Book1DeciderTransportCertificate enc pRank hardRank) :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat, hardRank n <= pRank M n := by
  intro M hM n
  exact Nat.le_trans (T.hardRank_le_extracted M hM n) (T.extracted_le_pRank M hM n)

/-- A tiny arithmetic helper used by the CEW counting route: for `n ≥ 2`,
every constant `c` is bounded by `n^c`. -/
theorem book1_constant_le_pow_of_two_le {n c : Nat} (hn : 2 <= n) :
    c <= n ^ c := by
  have h2n : 2 ^ c <= n ^ c := Nat.pow_le_pow_left hn c
  exact Nat.le_trans c.lt_two_pow_self.le h2n

/-- Local counting certificate for the Book-1 CEW→SPDP upper bound.

The intended mathematical content is: once a computation has contextual window
width `CEW`, the number/rank of projected SPDP directions is bounded by a fixed
monomial in `CEW` and the input size.  Small-size fields handle the awkward
`n = 0,1` endpoints caused by the strict `n^d` polynomial predicate used in the
existing port. -/
structure Book1CEWToSPDPCountingCertificate
    (pCEW : TuringMachine.DTM -> Nat -> Nat)
    (pRank : TuringMachine.DTM -> Nat -> Nat) where
  cewExponent : Nat
  sizeExponent : Nat
  rank_le_count :
    forall M : TuringMachine.DTM,
      forall n : Nat,
        pRank M n <= (pCEW M n) ^ cewExponent * n ^ sizeExponent
  rank_zero : forall M : TuringMachine.DTM, pRank M 0 <= 0
  rank_one : forall M : TuringMachine.DTM, pRank M 1 <= 1

/-- Concrete local profile-counting model for the Book-1 CEW upper bound.

`profileCount M n` is the finite number of local CEW/window profiles available
at size `n`.  The two load-bearing local facts are separated:

* the SPDP rank is bounded by the number of profiles; and
* the number of profiles is bounded by a fixed monomial in CEW and input size.

This is the intended local combinatorics theorem: it does not quantify over all
P deciders having small CEW; it only says that once a concrete observer has a
CEW/window profile universe of this size, its rank is counted by that universe. -/
structure Book1CEWProfileCountingModel
    (pCEW : TuringMachine.DTM -> Nat -> Nat)
    (pRank : TuringMachine.DTM -> Nat -> Nat) where
  profileCount : TuringMachine.DTM -> Nat -> Nat
  cewExponent : Nat
  sizeExponent : Nat
  rank_le_profile :
    forall M : TuringMachine.DTM,
      forall n : Nat, pRank M n <= profileCount M n
  profile_le_cew_monomial :
    forall M : TuringMachine.DTM,
      forall n : Nat,
        profileCount M n <= (pCEW M n) ^ cewExponent * n ^ sizeExponent
  rank_zero : forall M : TuringMachine.DTM, pRank M 0 <= 0
  rank_one : forall M : TuringMachine.DTM, pRank M 1 <= 1

/-- A concrete CEW profile-counting model supplies the simpler monomial counting
certificate used by the Book-1 route. -/
def book1CEWToSPDPCountingCertificate_of_profileCountingModel
    {pCEW : TuringMachine.DTM -> Nat -> Nat}
    {pRank : TuringMachine.DTM -> Nat -> Nat}
    (P : Book1CEWProfileCountingModel pCEW pRank) :
    Book1CEWToSPDPCountingCertificate pCEW pRank where
  cewExponent := P.cewExponent
  sizeExponent := P.sizeExponent
  rank_le_count := by
    intro M n
    exact Nat.le_trans (P.rank_le_profile M n) (P.profile_le_cew_monomial M n)
  rank_zero := P.rank_zero
  rank_one := P.rank_one

/-- A local CEW counting certificate proves the Book-1 `CEW ⇒ polynomial SPDP`
upper-bound field.  This is structural: polylog CEW plus a monomial counting
bound gives polynomial ambient rank. -/
theorem cewToPolynomialSPDP_of_countingCertificate
    {pCEW : TuringMachine.DTM -> Nat -> Nat}
    {pRank : TuringMachine.DTM -> Nat -> Nat}
    (C : Book1CEWToSPDPCountingCertificate pCEW pRank) :
    forall M : TuringMachine.DTM,
      (exists c k : Nat,
        forall n : Nat, pCEW M n <= c * (Nat.log 2 n) ^ k) ->
        exists d : Nat, forall n : Nat, pRank M n <= n ^ d := by
  intro M hpolylog
  rcases hpolylog with ⟨c, k, hcew_polylog⟩
  refine ⟨(c + k) * C.cewExponent + C.sizeExponent, ?_⟩
  intro n
  by_cases hn2 : 2 <= n
  · have hlog_le_n : Nat.log 2 n <= n := Nat.log_le_self 2 n
    have hlogpow_le : (Nat.log 2 n) ^ k <= n ^ k :=
      Nat.pow_le_pow_left hlog_le_n k
    have hc_le : c <= n ^ c := book1_constant_le_pow_of_two_le hn2
    have hcew_le_n : pCEW M n <= n ^ (c + k) := by
      calc
        pCEW M n <= c * (Nat.log 2 n) ^ k := hcew_polylog n
        _ <= n ^ c * n ^ k := Nat.mul_le_mul hc_le hlogpow_le
        _ = n ^ (c + k) := by rw [Nat.pow_add]
    have hcew_pow_le : (pCEW M n) ^ C.cewExponent <= n ^ ((c + k) * C.cewExponent) := by
      calc
        (pCEW M n) ^ C.cewExponent <= (n ^ (c + k)) ^ C.cewExponent :=
          Nat.pow_le_pow_left hcew_le_n C.cewExponent
        _ = n ^ ((c + k) * C.cewExponent) := by rw [Nat.pow_mul]
    calc
      pRank M n <= (pCEW M n) ^ C.cewExponent * n ^ C.sizeExponent :=
        C.rank_le_count M n
      _ <= n ^ ((c + k) * C.cewExponent) * n ^ C.sizeExponent :=
        Nat.mul_le_mul_right (n ^ C.sizeExponent) hcew_pow_le
      _ = n ^ ((c + k) * C.cewExponent + C.sizeExponent) := by rw [Nat.pow_add]
  · have hn_small : n = 0 ∨ n = 1 := by omega
    rcases hn_small with rfl | rfl
    · exact Nat.le_trans (C.rank_zero M) (Nat.zero_le _)
    · simpa using C.rank_one M

/-- A syntactic CEW-budget model for the P-side observer/window choice.

This is the safe form of `boundedCEWForP`: the bound is attached to the chosen
local-window accounting function itself, uniformly in `M`, and does **not** say
that arbitrary semantic SAT deciders must have low global complexity.  The SAT
correctness hypothesis is only consumed later by transport/extraction, not by
this syntactic budget theorem. -/
structure Book1SyntacticBoundedCEWModel
    (pCEW : TuringMachine.DTM -> Nat -> Nat) where
  cewConstant : Nat
  cewExponent : Nat
  syntactic_bound :
    forall M : TuringMachine.DTM,
      forall n : Nat,
        pCEW M n <= cewConstant * (Nat.log 2 n) ^ cewExponent

/-- A syntactic CEW-budget model supplies the Book-1 `boundedCEWForP` field.
The decider hypothesis is intentionally unused: the result is about the chosen
observer/window accounting, not about SAT semantics. -/
theorem boundedCEWForP_of_syntacticBoundedCEWModel
    {enc : ThreeCNFEncoding}
    {pCEW : TuringMachine.DTM -> Nat -> Nat}
    (S : Book1SyntacticBoundedCEWModel pCEW) :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        exists c k : Nat,
          forall n : Nat, pCEW M n <= c * (Nat.log 2 n) ^ k := by
  intro M _hM
  exact ⟨S.cewConstant, S.cewExponent, S.syntactic_bound M⟩

/-- Canonical syntactic log-window CEW budget.

This is deliberately only a window budget, not a claim that an arbitrary SAT
decider has low semantic complexity: `pCEW` is chosen to count the logarithmic
Book-1 local observer window. -/
def book1LogSyntacticPCEW (_M : TuringMachine.DTM) (n : Nat) : Nat :=
  Nat.log 2 n

/-- The canonical log-window CEW budget is polylogarithmically bounded. -/
def book1LogSyntacticBoundedCEWModel :
    Book1SyntacticBoundedCEWModel book1LogSyntacticPCEW where
  cewConstant := 1
  cewExponent := 1
  syntactic_bound := by
    intro M n
    simp [book1LogSyntacticPCEW]

/-- The canonical log-window model supplies the Book-1 `boundedCEWForP` field. -/
theorem boundedCEWForP_of_logSyntacticPCEW
    {enc : ThreeCNFEncoding} :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        exists c k : Nat,
          forall n : Nat, book1LogSyntacticPCEW M n <= c * (Nat.log 2 n) ^ k :=
  boundedCEWForP_of_syntacticBoundedCEWModel book1LogSyntacticBoundedCEWModel

/-- Book-1 CEW/SPDP data for a fixed encoding.

`pCEW M n` is the contextual entanglement width of the observer/compiled
P-family induced by a machine `M` at size `n`.  `pRank M n` is the corresponding
SPDP rank after the Book-1 projection.  `hardRank n` is the SPDP rank of the
hard NP-complete family at size `n`.

The fields are deliberately stated as obligations, because this is the honest
Book-1 seam: these are the mathematical claims that must be proved to turn the
conceptual CEW route into an unconditional Lean proof. -/
structure Book1CEWSPDPEpistemicBoundaryPort (enc : ThreeCNFEncoding) where
  /-- Contextual-entanglement width of the P-side observer family. -/
  pCEW : TuringMachine.DTM -> Nat -> Nat
  /-- SPDP rank of the P-side observer family after contextual projection. -/
  pRank : TuringMachine.DTM -> Nat -> Nat
  /-- SPDP rank of the hard NP family after the same Book-1 projection. -/
  hardRank : Nat -> Nat
  /-- (A1) Every SAT-deciding P observer has polylogarithmic CEW. -/
  boundedCEWForP :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        exists c k : Nat,
          forall n : Nat, pCEW M n <= c * (Nat.log 2 n) ^ k
  /-- (A2) Polylogarithmic CEW implies polynomial SPDP rank. -/
  cewToPolynomialSPDP :
    forall M : TuringMachine.DTM,
      (exists c k : Nat,
        forall n : Nat, pCEW M n <= c * (Nat.log 2 n) ^ k) ->
        exists d : Nat, forall n : Nat, pRank M n <= n ^ d
  /-- (A3) The hard NP family has the calibrated Book-1 super-polynomial SPDP
  lower bound.  The `/4` matches the sound Ramanujan/Tseitin binomial lower
  bound already present in the development and is still super-polynomial. -/
  hardNPLowerBound :
    forall n : Nat, n ^ (Nat.log 2 n / 4) <= hardRank n
  /-- Transport/no-loss certificate: a SAT decider first exposes the hard-family
  rank as an extracted God-Move rank, then the extracted rank embeds into the
  P-side observer rank.  The combined `hardRank <= pRank` theorem is proved
  below from these two genuinely load-bearing movements. -/
  transportCertificate :
    Book1DeciderTransportCertificate enc pRank hardRank

/-- Concrete assembly certificate for the Book-1 port.

This is only wiring: it combines four explicit local/certificate layers already
introduced above.

* `ambientModel`: same-target Ramanujan/Tseitin hard sheet plus extraction
  containment in the full compiled ambient rank;
* `cewBudget`: syntactic/log-window CEW budget;
* `profileCounting`: local finite-profile counting bound for the ambient rank;
* calibrated hard rank: `book1CalibratedRamanujanTseitinHardRank`.

No new semantic claim that “all P deciders have low CEW” is introduced here;
that comes only from the chosen syntactic CEW budget field. -/
structure Book1ConcreteAssemblyCertificate (enc : ThreeCNFEncoding) where
  pCEW : TuringMachine.DTM -> Nat -> Nat
  ambientModel : Book1SameTargetAmbientCompiledRankModel enc
  cewBudget : Book1SyntacticBoundedCEWModel pCEW
  profileCounting : Book1CEWProfileCountingModel pCEW ambientModel.ambientRank

/-- Bridge-aware concrete assembly certificate for the Book-1 port.  This is
the preferred final certificate shape: the ambient model carries an explicit
encoded-to-core SAT semantic bridge. -/
structure Book1ConcreteAssemblyCertificateWithBridge (enc : ThreeCNFEncoding) where
  pCEW : TuringMachine.DTM -> Nat -> Nat
  ambientModel : Book1SameTargetAmbientCompiledRankModelWithBridge enc
  cewBudget : Book1SyntacticBoundedCEWModel pCEW
  profileCounting : Book1CEWProfileCountingModel pCEW ambientModel.ambientRank

/-- Fully explicit safe local payload bundle.

This is the least magical final-input shape.  It stores only named local data:
CEW budget, same-target RT hard payloads, explicit encoded/core SAT semantics
bridge, extraction-transfer ambient payloads, finite endpoint comparisons, and
profile-counting inequalities.  It does **not** derive any of those payloads
from the bare existence of a SAT decider. -/
structure Book1SafeLocalPayloadBundle (enc : ThreeCNFEncoding) where
  pCEW : TuringMachine.DTM -> Nat -> Nat
  extractedRank : TuringMachine.DTM -> Nat -> Nat
  ambientRank : TuringMachine.DTM -> Nat -> Nat
  semanticBridge : Book1SATSemanticsBridge enc
  cewBudget : Book1SyntacticBoundedCEWModel pCEW
  large_sameTarget :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          2 ^ 804 <= n ->
            Book1SameTargetRamanujanTseitinRankCertificate M n (extractedRank M n)
  preThreshold_lower :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            book1CalibratedRamanujanTseitinHardRank n <= extractedRank M n
  large_ambient_payload :
    forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        forall n : Nat,
          2 ^ 804 <= n ->
            Book1SameTargetAmbientLargePayload semanticBridge M hM n
              (extractedRank M n) (ambientRank M n)
  preThreshold_ambient :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            extractedRank M n <= ambientRank M n
  profileCount : TuringMachine.DTM -> Nat -> Nat
  cewExponent : Nat
  sizeExponent : Nat
  rank_le_profile :
    forall M : TuringMachine.DTM,
      forall n : Nat, ambientRank M n <= profileCount M n
  profile_le_cew_monomial :
    forall M : TuringMachine.DTM,
      forall n : Nat,
        profileCount M n <= (pCEW M n) ^ cewExponent * n ^ sizeExponent
  rank_zero : forall M : TuringMachine.DTM, ambientRank M 0 <= 0
  rank_one : forall M : TuringMachine.DTM, ambientRank M 1 <= 1

/-- What kind of normalization/padding evidence is being supplied.

This tag is deliberately explicit so the Book-1 payload cannot silently treat a
raw SAT decider as if it already satisfied the same-target God-Move machine
bounds. -/
inductive Book1NormalizationMode where
  /-- A genuine machine transform with length-preserving acceptance equivalence. -/
  | realMachineTransform
  /-- A padded simulator/normal form whose SAT language correctness is certified. -/
  | paddedSimulation
  /-- A certificate-only normal form, used only when the normal machine is
  supplied directly as local data. -/
  | certificateOnlyNormalForm

/-- Mode-specific evidence attached to a normalization certificate. -/
def Book1NormalizationModePayload
    (enc : ThreeCNFEncoding)
    (M : TuringMachine.DTM)
    (_hM : DTMDecidesSATWithEncoding enc M)
    (N : TuringMachine.DTM) : Book1NormalizationMode -> Prop
  | Book1NormalizationMode.realMachineTransform =>
      forall {n : Nat} (hn : n >= 1) (input : Fin n -> Bool),
        TuringMachine.accepts N n hn input <-> TuringMachine.accepts M n hn input
  | Book1NormalizationMode.paddedSimulation =>
      DTMDecidesSATWithEncoding enc N
  | Book1NormalizationMode.certificateOnlyNormalForm =>
      DTMDecidesSATWithEncoding enc N

/-- A length-preserving acceptance-equivalent machine preserves encoded SAT
semantics. -/
theorem DTMDecidesSATWithEncoding_of_acceptance_equiv
    {enc : ThreeCNFEncoding}
    {M N : TuringMachine.DTM}
    (hM : DTMDecidesSATWithEncoding enc M)
    (heq : forall {n : Nat} (hn : n >= 1) (input : Fin n -> Bool),
      TuringMachine.accepts N n hn input <-> TuringMachine.accepts M n hn input) :
    DTMDecidesSATWithEncoding enc N := by
  intro n hn input φ henc
  exact Iff.trans (heq hn input) (hM hn input φ henc)

/-- Explicit normalization/padding data for a raw SAT decider.

The same-target God-Move interface asks for machine-side bounds such as
`timeBound ≤ 4` and `numStates ≤ n`.  Those are not properties of an arbitrary
raw SAT decider.  This certificate makes the missing move explicit: from a raw
encoded SAT decider `M`, provide a normalized/padded decider `normalized`, say
which mode of normalization is being used, and certify both semantic
preservation/correctness and the side bounds. -/
structure Book1NormalizationPaddingCertificate
    (enc : ThreeCNFEncoding)
    (M : TuringMachine.DTM)
    (hM : DTMDecidesSATWithEncoding enc M) where
  mode : Book1NormalizationMode
  normalized : TuringMachine.DTM
  modePayload : Book1NormalizationModePayload enc M hM normalized mode
  normalized_decides : DTMDecidesSATWithEncoding enc normalized
  normalized_timeBound_le_four : normalized.timeBound <= 4
  normalized_numStates_le_large :
    forall n : Nat, 2 ^ 804 <= n -> normalized.numStates <= n

namespace Book1NormalizationPaddingCertificate

/-- Constructor for a genuine length-preserving machine transform. -/
def ofRealMachineTransform
    {enc : ThreeCNFEncoding}
    {M N : TuringMachine.DTM}
    {hM : DTMDecidesSATWithEncoding enc M}
    (heq : forall {n : Nat} (hn : n >= 1) (input : Fin n -> Bool),
      TuringMachine.accepts N n hn input <-> TuringMachine.accepts M n hn input)
    (htime : N.timeBound <= 4)
    (hstates : forall n : Nat, 2 ^ 804 <= n -> N.numStates <= n) :
    Book1NormalizationPaddingCertificate enc M hM where
  mode := Book1NormalizationMode.realMachineTransform
  normalized := N
  modePayload := heq
  normalized_decides := DTMDecidesSATWithEncoding_of_acceptance_equiv hM heq
  normalized_timeBound_le_four := htime
  normalized_numStates_le_large := hstates

/-- Constructor for a padded simulation with certified encoded SAT semantics. -/
def ofPaddedSimulation
    {enc : ThreeCNFEncoding}
    {M N : TuringMachine.DTM}
    {hM : DTMDecidesSATWithEncoding enc M}
    (hN : DTMDecidesSATWithEncoding enc N)
    (htime : N.timeBound <= 4)
    (hstates : forall n : Nat, 2 ^ 804 <= n -> N.numStates <= n) :
    Book1NormalizationPaddingCertificate enc M hM where
  mode := Book1NormalizationMode.paddedSimulation
  normalized := N
  modePayload := hN
  normalized_decides := hN
  normalized_timeBound_le_four := htime
  normalized_numStates_le_large := hstates

/-- Constructor for a certificate-only normal form supplied directly as local
data.  This is intentionally marked so auditors can distinguish it from an
actual machine transform. -/
def ofCertificateOnlyNormalForm
    {enc : ThreeCNFEncoding}
    {M N : TuringMachine.DTM}
    {hM : DTMDecidesSATWithEncoding enc M}
    (hN : DTMDecidesSATWithEncoding enc N)
    (htime : N.timeBound <= 4)
    (hstates : forall n : Nat, 2 ^ 804 <= n -> N.numStates <= n) :
    Book1NormalizationPaddingCertificate enc M hM where
  mode := Book1NormalizationMode.certificateOnlyNormalForm
  normalized := N
  modePayload := hN
  normalized_decides := hN
  normalized_timeBound_le_four := htime
  normalized_numStates_le_large := hstates

end Book1NormalizationPaddingCertificate

/-- Explicit family of normalized/padded machines for raw encoded SAT deciders.
This is local certificate data: the route never proves that such a family exists
from SAT semantics alone. -/
structure Book1ExplicitNormalizationFamily (enc : ThreeCNFEncoding) where
  normalize :
    forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        Book1NormalizationPaddingCertificate enc M hM

/-- Local normalization boundary: a raw encoded SAT decider is converted to an
explicitly certified normal form.  This is a certificate boundary, not a global
theorem that every raw machine already satisfies God-Move side conditions. -/
structure Book1LocalNormalizationBoundary (enc : ThreeCNFEncoding) where
  normalForms : Book1ExplicitNormalizationFamily enc

/-- Explicit same-target Ramanujan/Tseitin family for the chosen extracted-rank
model.  It is local data: for each raw decider and large size, the caller
supplies the target certificate on the normalized machine. -/
structure Book1ExplicitSameTargetRTFamily
    (enc : ThreeCNFEncoding)
    (extractedRank : TuringMachine.DTM -> Nat -> Nat)
    (normalize : forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        Book1NormalizationPaddingCertificate enc M hM) where
  large_sameTarget_normalized :
    forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        forall n : Nat,
          forall _hn : 2 ^ 804 <= n,
            Book1SameTargetRamanujanTseitinRankCertificate
              ((normalize M hM).normalized) n (extractedRank M n)
  preThreshold_lower :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            book1CalibratedRamanujanTseitinHardRank n <= extractedRank M n

/-- Local same-target Ramanujan/Tseitin certificate boundary.  It asks only for
an explicit RT family plus finite pre-threshold lower bounds. -/
structure Book1LocalSameTargetRTBoundary
    (enc : ThreeCNFEncoding)
    (extractedRank : TuringMachine.DTM -> Nat -> Nat)
    (normalize : forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        Book1NormalizationPaddingCertificate enc M hM) where
  rtFamily : Book1ExplicitSameTargetRTFamily enc extractedRank normalize

/-- Explicit ambient-transfer family for the chosen normalized machine family.
It packages Cook--Levin/God-Move transfer payloads as supplied local data. -/
structure Book1ExplicitAmbientTransferFamily
    (enc : ThreeCNFEncoding)
    (semanticBridge : Book1SATSemanticsBridge enc)
    (extractedRank ambientRank : TuringMachine.DTM -> Nat -> Nat)
    (normalize : forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        Book1NormalizationPaddingCertificate enc M hM) where
  large_ambient_payload_normalized :
    forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        forall n : Nat,
          forall _hn : 2 ^ 804 <= n,
            Book1SameTargetAmbientLargePayload semanticBridge
              ((normalize M hM).normalized)
              ((normalize M hM).normalized_decides) n
              (extractedRank M n) (ambientRank M n)
  preThreshold_ambient :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            extractedRank M n <= ambientRank M n

/-- Local ambient-transfer certificate boundary.  It packages an explicit
God-Move/Cook--Levin ambient-transfer family, not a global theorem. -/
structure Book1LocalAmbientTransferBoundary
    (enc : ThreeCNFEncoding)
    (semanticBridge : Book1SATSemanticsBridge enc)
    (extractedRank ambientRank : TuringMachine.DTM -> Nat -> Nat)
    (normalize : forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        Book1NormalizationPaddingCertificate enc M hM) where
  transferFamily :
    Book1ExplicitAmbientTransferFamily enc semanticBridge extractedRank ambientRank normalize

/-- Explicit local CEW/profile universe.

This is deliberately **not** a theorem that every SAT decider has low CEW.
It is a supplied finite profile accounting object for the chosen observer/rank
model: `profileCount M n` is the size of this chosen local profile universe,
`rank_le_profile` says the ambient rank is accounted for by that universe, and
`profile_le_cew_monomial` is the local counting inequality for this universe. -/
structure Book1ExplicitCEWProfileUniverse
    (pCEW : TuringMachine.DTM -> Nat -> Nat)
    (ambientRank : TuringMachine.DTM -> Nat -> Nat) where
  profileCount : TuringMachine.DTM -> Nat -> Nat
  cewExponent : Nat
  sizeExponent : Nat
  rank_le_profile :
    forall M : TuringMachine.DTM,
      forall n : Nat, ambientRank M n <= profileCount M n
  profile_le_cew_monomial :
    forall M : TuringMachine.DTM,
      forall n : Nat,
        profileCount M n <= (pCEW M n) ^ cewExponent * n ^ sizeExponent
  rank_zero : forall M : TuringMachine.DTM, ambientRank M 0 <= 0
  rank_one : forall M : TuringMachine.DTM, ambientRank M 1 <= 1

/-- Local CEW/profile counting certificate boundary.  This is the intended
assumption frontier for the P-side upper bound: a concrete profile universe and
its counting inequalities are supplied explicitly, as local data. -/
structure Book1LocalCEWProfileBoundary
    (pCEW : TuringMachine.DTM -> Nat -> Nat)
    (ambientRank : TuringMachine.DTM -> Nat -> Nat) where
  profileUniverse : Book1ExplicitCEWProfileUniverse pCEW ambientRank

/-- Fully named certificate-boundary input for the normalized Book-1 route.
The route file proves only that these local certificates assemble; it does not
claim that SAT deciders globally generate them. -/
structure Book1NamedCertificateBoundaryBundle (enc : ThreeCNFEncoding) where
  pCEW : TuringMachine.DTM -> Nat -> Nat
  extractedRank : TuringMachine.DTM -> Nat -> Nat
  ambientRank : TuringMachine.DTM -> Nat -> Nat
  semanticBridge : Book1SATSemanticsBridge enc
  cewBudget : Book1SyntacticBoundedCEWModel pCEW
  normalization : Book1LocalNormalizationBoundary enc
  sameTargetRT :
    Book1LocalSameTargetRTBoundary enc extractedRank normalization.normalForms.normalize
  ambientTransfer :
    Book1LocalAmbientTransferBoundary enc semanticBridge extractedRank ambientRank
      normalization.normalForms.normalize
  profileCounting : Book1LocalCEWProfileBoundary pCEW ambientRank

namespace Book1LocalNormalizationBoundary

/-- Package a supplied normalization family as the local normalization boundary. -/
def ofFamily {enc : ThreeCNFEncoding}
    (F : Book1ExplicitNormalizationFamily enc) :
    Book1LocalNormalizationBoundary enc where
  normalForms := F

end Book1LocalNormalizationBoundary

namespace Book1LocalSameTargetRTBoundary

/-- Package a supplied same-target RT family as the local RT boundary. -/
def ofFamily
    {enc : ThreeCNFEncoding}
    {extractedRank : TuringMachine.DTM -> Nat -> Nat}
    {normalize : forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        Book1NormalizationPaddingCertificate enc M hM}
    (F : Book1ExplicitSameTargetRTFamily enc extractedRank normalize) :
    Book1LocalSameTargetRTBoundary enc extractedRank normalize where
  rtFamily := F

end Book1LocalSameTargetRTBoundary

namespace Book1LocalAmbientTransferBoundary

/-- Package a supplied ambient-transfer family as the local ambient boundary. -/
def ofFamily
    {enc : ThreeCNFEncoding}
    {semanticBridge : Book1SATSemanticsBridge enc}
    {extractedRank ambientRank : TuringMachine.DTM -> Nat -> Nat}
    {normalize : forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        Book1NormalizationPaddingCertificate enc M hM}
    (F : Book1ExplicitAmbientTransferFamily enc semanticBridge extractedRank ambientRank normalize) :
    Book1LocalAmbientTransferBoundary enc semanticBridge extractedRank ambientRank normalize where
  transferFamily := F

end Book1LocalAmbientTransferBoundary

namespace Book1ExplicitCEWProfileUniverse

/-- Build an explicit profile universe from a chosen profile-count function and
its local counting inequalities. -/
def ofProfileCount
    {pCEW ambientRank : TuringMachine.DTM -> Nat -> Nat}
    (profileCount : TuringMachine.DTM -> Nat -> Nat)
    (cewExponent sizeExponent : Nat)
    (rank_le_profile :
      forall M : TuringMachine.DTM,
        forall n : Nat, ambientRank M n <= profileCount M n)
    (profile_le_cew_monomial :
      forall M : TuringMachine.DTM,
        forall n : Nat,
          profileCount M n <= (pCEW M n) ^ cewExponent * n ^ sizeExponent)
    (rank_zero : forall M : TuringMachine.DTM, ambientRank M 0 <= 0)
    (rank_one : forall M : TuringMachine.DTM, ambientRank M 1 <= 1) :
    Book1ExplicitCEWProfileUniverse pCEW ambientRank where
  profileCount := profileCount
  cewExponent := cewExponent
  sizeExponent := sizeExponent
  rank_le_profile := rank_le_profile
  profile_le_cew_monomial := profile_le_cew_monomial
  rank_zero := rank_zero
  rank_one := rank_one

/-- Special local constructor when the chosen profile universe is exactly the
ambient-rank index set.  The only remaining obligation is the local monomial
bound on that chosen rank function. -/
def ofAmbientRankMonomialBound
    {pCEW ambientRank : TuringMachine.DTM -> Nat -> Nat}
    (cewExponent sizeExponent : Nat)
    (rank_le_monomial :
      forall M : TuringMachine.DTM,
        forall n : Nat,
          ambientRank M n <= (pCEW M n) ^ cewExponent * n ^ sizeExponent)
    (rank_zero : forall M : TuringMachine.DTM, ambientRank M 0 <= 0)
    (rank_one : forall M : TuringMachine.DTM, ambientRank M 1 <= 1) :
    Book1ExplicitCEWProfileUniverse pCEW ambientRank :=
  ofProfileCount ambientRank cewExponent sizeExponent
    (by intro M n; rfl) rank_le_monomial rank_zero rank_one

end Book1ExplicitCEWProfileUniverse

namespace Book1LocalCEWProfileBoundary

/-- Package a supplied explicit profile universe as the local CEW/profile
boundary. -/
def ofUniverse
    {pCEW ambientRank : TuringMachine.DTM -> Nat -> Nat}
    (U : Book1ExplicitCEWProfileUniverse pCEW ambientRank) :
    Book1LocalCEWProfileBoundary pCEW ambientRank where
  profileUniverse := U

end Book1LocalCEWProfileBoundary

namespace Book1NamedCertificateBoundaryBundle

/-- Assemble the named boundary bundle from the four explicit local families.
This is the final “certificates in” constructor: it performs no global
certificate generation. -/
def ofExplicitFamilies
    {enc : ThreeCNFEncoding}
    (pCEW extractedRank ambientRank : TuringMachine.DTM -> Nat -> Nat)
    (semanticBridge : Book1SATSemanticsBridge enc)
    (cewBudget : Book1SyntacticBoundedCEWModel pCEW)
    (normalization : Book1ExplicitNormalizationFamily enc)
    (sameTargetRT :
      Book1ExplicitSameTargetRTFamily enc extractedRank normalization.normalize)
    (ambientTransfer :
      Book1ExplicitAmbientTransferFamily enc semanticBridge extractedRank ambientRank
        normalization.normalize)
    (profileUniverse : Book1ExplicitCEWProfileUniverse pCEW ambientRank) :
    Book1NamedCertificateBoundaryBundle enc where
  pCEW := pCEW
  extractedRank := extractedRank
  ambientRank := ambientRank
  semanticBridge := semanticBridge
  cewBudget := cewBudget
  normalization := Book1LocalNormalizationBoundary.ofFamily normalization
  sameTargetRT := Book1LocalSameTargetRTBoundary.ofFamily sameTargetRT
  ambientTransfer := Book1LocalAmbientTransferBoundary.ofFamily ambientTransfer
  profileCounting := Book1LocalCEWProfileBoundary.ofUniverse profileUniverse

end Book1NamedCertificateBoundaryBundle

/-- Normalized safe local payload bundle.

This is the safer successor to `Book1SafeLocalPayloadBundle`: large-size RT and
ambient payloads are requested for the explicitly normalized/padded machine,
not for the arbitrary raw decider.  The raw machine only indexes the final
observer rank and profile count. -/
structure Book1NormalizedSafeLocalPayloadBundle (enc : ThreeCNFEncoding) where
  pCEW : TuringMachine.DTM -> Nat -> Nat
  extractedRank : TuringMachine.DTM -> Nat -> Nat
  ambientRank : TuringMachine.DTM -> Nat -> Nat
  semanticBridge : Book1SATSemanticsBridge enc
  cewBudget : Book1SyntacticBoundedCEWModel pCEW
  normalize :
    forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        Book1NormalizationPaddingCertificate enc M hM
  large_sameTarget_normalized :
    forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        forall n : Nat,
          forall _hn : 2 ^ 804 <= n,
            Book1SameTargetRamanujanTseitinRankCertificate
              ((normalize M hM).normalized) n (extractedRank M n)
  preThreshold_lower :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            book1CalibratedRamanujanTseitinHardRank n <= extractedRank M n
  large_ambient_payload_normalized :
    forall M : TuringMachine.DTM,
      forall hM : DTMDecidesSATWithEncoding enc M,
        forall n : Nat,
          forall _hn : 2 ^ 804 <= n,
            Book1SameTargetAmbientLargePayload semanticBridge
              ((normalize M hM).normalized)
              ((normalize M hM).normalized_decides) n
              (extractedRank M n) (ambientRank M n)
  preThreshold_ambient :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat,
          n < 2 ^ 804 ->
            extractedRank M n <= ambientRank M n
  profileCount : TuringMachine.DTM -> Nat -> Nat
  cewExponent : Nat
  sizeExponent : Nat
  rank_le_profile :
    forall M : TuringMachine.DTM,
      forall n : Nat, ambientRank M n <= profileCount M n
  profile_le_cew_monomial :
    forall M : TuringMachine.DTM,
      forall n : Nat,
        profileCount M n <= (pCEW M n) ^ cewExponent * n ^ sizeExponent
  rank_zero : forall M : TuringMachine.DTM, ambientRank M 0 <= 0
  rank_one : forall M : TuringMachine.DTM, ambientRank M 1 <= 1

/-- Flatten the named certificate-boundary bundle into the lower-level
normalized payload shape. -/
def book1NormalizedSafeLocalPayloadBundle_of_namedCertificateBoundary
    {enc : ThreeCNFEncoding}
    (B : Book1NamedCertificateBoundaryBundle enc) :
    Book1NormalizedSafeLocalPayloadBundle enc where
  pCEW := B.pCEW
  extractedRank := B.extractedRank
  ambientRank := B.ambientRank
  semanticBridge := B.semanticBridge
  cewBudget := B.cewBudget
  normalize := B.normalization.normalForms.normalize
  large_sameTarget_normalized :=
    B.sameTargetRT.rtFamily.large_sameTarget_normalized
  preThreshold_lower := B.sameTargetRT.rtFamily.preThreshold_lower
  large_ambient_payload_normalized :=
    B.ambientTransfer.transferFamily.large_ambient_payload_normalized
  preThreshold_ambient := B.ambientTransfer.transferFamily.preThreshold_ambient
  profileCount := B.profileCounting.profileUniverse.profileCount
  cewExponent := B.profileCounting.profileUniverse.cewExponent
  sizeExponent := B.profileCounting.profileUniverse.sizeExponent
  rank_le_profile := B.profileCounting.profileUniverse.rank_le_profile
  profile_le_cew_monomial := B.profileCounting.profileUniverse.profile_le_cew_monomial
  rank_zero := B.profileCounting.profileUniverse.rank_zero
  rank_one := B.profileCounting.profileUniverse.rank_one

/-- Convert the explicit local payload bundle into the bridge-aware assembly
certificate.  This is pure packaging. -/
def book1ConcreteAssemblyCertificateWithBridge_of_safeLocalPayloadBundle
    {enc : ThreeCNFEncoding}
    (P : Book1SafeLocalPayloadBundle enc) :
    Book1ConcreteAssemblyCertificateWithBridge enc where
  pCEW := P.pCEW
  ambientModel :=
    { hardModel :=
        { extractedRank := P.extractedRank
          large_sameTarget := P.large_sameTarget
          preThreshold_lower := P.preThreshold_lower }
      semanticBridge := P.semanticBridge
      ambientRank := P.ambientRank
      large_ambient_payload := P.large_ambient_payload
      preThreshold_ambient := P.preThreshold_ambient }
  cewBudget := P.cewBudget
  profileCounting :=
    { profileCount := P.profileCount
      cewExponent := P.cewExponent
      sizeExponent := P.sizeExponent
      rank_le_profile := P.rank_le_profile
      profile_le_cew_monomial := P.profile_le_cew_monomial
      rank_zero := P.rank_zero
      rank_one := P.rank_one }

/-- Forget the bridge-aware assembly certificate into the older assembly shape. -/
def book1ConcreteAssemblyCertificate_of_withBridge
    {enc : ThreeCNFEncoding}
    (A : Book1ConcreteAssemblyCertificateWithBridge enc) :
    Book1ConcreteAssemblyCertificate enc where
  pCEW := A.pCEW
  ambientModel := book1SameTargetAmbientCompiledRankModel_of_withBridge A.ambientModel
  cewBudget := A.cewBudget
  profileCounting := A.profileCounting

/-- Assemble the concrete Book-1 CEW/SPDP port from explicit local certificates.
This is the final non-magical wiring theorem for the Book-1 route. -/
def book1CEWSPDPEpistemicBoundaryPort_of_concreteAssembly
    {enc : ThreeCNFEncoding}
    (A : Book1ConcreteAssemblyCertificate enc) :
    Book1CEWSPDPEpistemicBoundaryPort enc where
  pCEW := A.pCEW
  pRank := A.ambientModel.ambientRank
  hardRank := book1CalibratedRamanujanTseitinHardRank
  boundedCEWForP := boundedCEWForP_of_syntacticBoundedCEWModel A.cewBudget
  cewToPolynomialSPDP :=
    cewToPolynomialSPDP_of_countingCertificate
      (book1CEWToSPDPCountingCertificate_of_profileCountingModel A.profileCounting)
  hardNPLowerBound := book1CalibratedRamanujanTseitinHardNPLowerBound
  transportCertificate :=
    book1TransportCertificate_of_ambientCompiledRankModel
      (book1AmbientCompiledRankModel_of_sameTargetAmbientModel A.ambientModel)

/-- Assemble the concrete Book-1 CEW/SPDP port from the preferred bridge-aware
certificate shape. -/
def book1CEWSPDPEpistemicBoundaryPort_of_concreteAssemblyWithBridge
    {enc : ThreeCNFEncoding}
    (A : Book1ConcreteAssemblyCertificateWithBridge enc) :
    Book1CEWSPDPEpistemicBoundaryPort enc :=
  book1CEWSPDPEpistemicBoundaryPort_of_concreteAssembly
    (book1ConcreteAssemblyCertificate_of_withBridge A)

/-- The explicit safe local payload bundle assembles the full Book-1 port. -/
def book1CEWSPDPEpistemicBoundaryPort_of_safeLocalPayloadBundle
    {enc : ThreeCNFEncoding}
    (P : Book1SafeLocalPayloadBundle enc) :
    Book1CEWSPDPEpistemicBoundaryPort enc :=
  book1CEWSPDPEpistemicBoundaryPort_of_concreteAssemblyWithBridge
    (book1ConcreteAssemblyCertificateWithBridge_of_safeLocalPayloadBundle P)

/-- A normalized safe payload bundle gives the split transport certificate
without pretending the raw decider itself satisfies the God-Move machine-size
side conditions.  Large-size same-target and ambient certificates are taken on
`(P.normalize M hM).normalized`; only the resulting rank inequalities are
transported back to the raw observer rank indexed by `M`. -/
def book1TransportCertificate_of_normalizedSafeLocalPayloadBundle
    {enc : ThreeCNFEncoding}
    (P : Book1NormalizedSafeLocalPayloadBundle enc) :
    Book1DeciderTransportCertificate enc P.ambientRank
      book1CalibratedRamanujanTseitinHardRank where
  extractedRank := P.extractedRank
  hardRank_le_extracted := by
    intro M hM n
    by_cases hn : 2 ^ 804 <= n
    · exact book1CalibratedHardRank_le_of_sameTargetRamanujanTseitinCertificate
        (P.large_sameTarget_normalized M hM n hn)
    · exact P.preThreshold_lower M hM n (Nat.lt_of_not_ge hn)
  extracted_le_pRank := by
    intro M hM n
    by_cases hn : 2 ^ 804 <= n
    · exact extracted_le_ambient_of_sameTargetAmbientRankCertificate
        ((P.large_ambient_payload_normalized M hM n hn).toCertificate)
    · exact P.preThreshold_ambient M hM n (Nat.lt_of_not_ge hn)

/-- Assemble the full Book-1 port from the normalized safe local payload bundle.
This is the preferred safe route when raw deciders require a padding/
normalization step before the same-target RT/God-Move certificates apply. -/
def book1CEWSPDPEpistemicBoundaryPort_of_normalizedSafeLocalPayloadBundle
    {enc : ThreeCNFEncoding}
    (P : Book1NormalizedSafeLocalPayloadBundle enc) :
    Book1CEWSPDPEpistemicBoundaryPort enc where
  pCEW := P.pCEW
  pRank := P.ambientRank
  hardRank := book1CalibratedRamanujanTseitinHardRank
  boundedCEWForP := boundedCEWForP_of_syntacticBoundedCEWModel P.cewBudget
  cewToPolynomialSPDP :=
    cewToPolynomialSPDP_of_countingCertificate
      (book1CEWToSPDPCountingCertificate_of_profileCountingModel
        { profileCount := P.profileCount
          cewExponent := P.cewExponent
          sizeExponent := P.sizeExponent
          rank_le_profile := P.rank_le_profile
          profile_le_cew_monomial := P.profile_le_cew_monomial
          rank_zero := P.rank_zero
          rank_one := P.rank_one })
  hardNPLowerBound := book1CalibratedRamanujanTseitinHardNPLowerBound
  transportCertificate :=
    book1TransportCertificate_of_normalizedSafeLocalPayloadBundle P

/-- Assemble the full Book-1 port from named local certificate boundaries.  This
is the most audit-friendly entry point: each remaining mathematical assumption
is carried by an explicitly named local certificate structure. -/
def book1CEWSPDPEpistemicBoundaryPort_of_namedCertificateBoundary
    {enc : ThreeCNFEncoding}
    (B : Book1NamedCertificateBoundaryBundle enc) :
    Book1CEWSPDPEpistemicBoundaryPort enc :=
  book1CEWSPDPEpistemicBoundaryPort_of_normalizedSafeLocalPayloadBundle
    (book1NormalizedSafeLocalPayloadBundle_of_namedCertificateBoundary B)

/-- Growth separation: the calibrated Ramanujan/Tseitin scale
`n^(log₂ n / 4)` eventually beats every fixed polynomial.

This is the one purely arithmetic Book-1 obligation; it is discharged by taking
`n = 2^(4(d+1))`, so `log₂ n / 4 = d+1`. -/
theorem book1_superPolynomialGap :
    forall d : Nat, exists n : Nat, n ^ d < n ^ (Nat.log 2 n / 4) := by
  intro d
  refine ⟨2 ^ (4 * (d + 1)), ?_⟩
  rw [Nat.log_pow (by decide : 1 < 2)]
  have hbase : 1 < 2 ^ (4 * (d + 1)) :=
    Nat.one_lt_pow (by omega : 4 * (d + 1) ≠ 0) (by decide : 1 < 2)
  have hexp : d < 4 * (d + 1) / 4 := by omega
  exact Nat.pow_lt_pow_right hbase hexp

/-- From Book-1 axioms (A1) and (A2), every SAT-deciding P observer has a
polynomial SPDP-rank bound. -/
theorem book1_pSidePolynomialSPDP_of_decider
    {enc : ThreeCNFEncoding}
    (B : Book1CEWSPDPEpistemicBoundaryPort enc)
    {M : TuringMachine.DTM}
    (hM : DTMDecidesSATWithEncoding enc M) :
    exists d : Nat, forall n : Nat, B.pRank M n <= n ^ d := by
  exact B.cewToPolynomialSPDP M (B.boundedCEWForP M hM)

/-- The Book-1 CEW/SPDP epistemic-boundary port rules out encoded SAT deciders.

This is the clean replacement for trying to force same-sheet rank into
`liveBoundaryRank`: the contradiction is between a polynomial P-side SPDP upper
bound and the transported super-polynomial hard-family SPDP lower bound. -/
theorem no_DTMDecidesSATWithEncoding_of_book1CEWSPDP
    (enc : ThreeCNFEncoding)
    (B : Book1CEWSPDPEpistemicBoundaryPort enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  intro hdec
  rcases hdec with ⟨M, hM⟩
  rcases book1_pSidePolynomialSPDP_of_decider B hM with ⟨d, hpUpper⟩
  rcases book1_superPolynomialGap d with ⟨n, hgap⟩
  have htransport : forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M -> forall n : Nat, B.hardRank n <= B.pRank M n :=
    deciderTransportHardToP_of_book1TransportCertificate B.transportCertificate
  have hlower_to_p : n ^ (Nat.log 2 n / 4) <= B.pRank M n :=
    Nat.le_trans (B.hardNPLowerBound n) (htransport M hM n)
  have hp_to_poly : B.pRank M n <= n ^ d := hpUpper n
  have hle : n ^ (Nat.log 2 n / 4) <= n ^ d := Nat.le_trans hlower_to_p hp_to_poly
  exact (Nat.not_le_of_lt hgap) hle

/-- With a standard bridge supplied, the Book-1 CEW/SPDP port yields the chosen
standard `P ≠ NP` statement. -/
theorem standardPvsNP_of_book1CEWSPDP
    {enc : ThreeCNFEncoding}
    (S : StandardPvsNPBridge enc)
    (B : Book1CEWSPDPEpistemicBoundaryPort enc) :
    S.standardPvsNP :=
  S.standardPvsNP_iff_no_encodedSATDecider.mpr
    (no_DTMDecidesSATWithEncoding_of_book1CEWSPDP enc B)

#print axioms threeCNF_positive_isSatisfiable
#print axioms book1SATSemanticsBridge_of_positiveThreeCNFEncoding
#print axioms book1CalibratedRamanujanTseitinHardNPLowerBound
#print axioms book1CalibratedHardRank_le_of_sameTargetRamanujanTseitinCertificate
#print axioms book1HardSheetExtractionModel_of_sameTargetRamanujanTseitinModel
#print axioms book1SameTargetAmbientRankCertificate_of_encodedSATBridge
#print axioms Book1SameTargetAmbientLargePayload.toCertificate
#print axioms book1SameTargetAmbientCompiledRankModel_of_withBridge
#print axioms extracted_le_ambient_of_sameTargetAmbientRankCertificate
#print axioms book1AmbientCompiledRankModel_of_sameTargetAmbientModel
#print axioms book1CalibratedHardSheetExtractionModel
#print axioms book1_superPolynomialGap
#print axioms hardRank_le_extracted_of_hardSheetExtractionModel
#print axioms extracted_le_pRank_of_ambientCompiledRankModel
#print axioms book1CEWToSPDPCountingCertificate_of_profileCountingModel
#print axioms boundedCEWForP_of_syntacticBoundedCEWModel
#print axioms boundedCEWForP_of_logSyntacticPCEW
#print axioms cewToPolynomialSPDP_of_countingCertificate
#print axioms DTMDecidesSATWithEncoding_of_acceptance_equiv
#print axioms Book1NormalizationPaddingCertificate.ofRealMachineTransform
#print axioms Book1NormalizationPaddingCertificate.ofPaddedSimulation
#print axioms Book1NormalizationPaddingCertificate.ofCertificateOnlyNormalForm
#print axioms Book1LocalNormalizationBoundary.ofFamily
#print axioms Book1LocalSameTargetRTBoundary.ofFamily
#print axioms Book1LocalAmbientTransferBoundary.ofFamily
#print axioms Book1ExplicitCEWProfileUniverse.ofProfileCount
#print axioms Book1ExplicitCEWProfileUniverse.ofAmbientRankMonomialBound
#print axioms Book1LocalCEWProfileBoundary.ofUniverse
#print axioms Book1NamedCertificateBoundaryBundle.ofExplicitFamilies
#print axioms book1ConcreteAssemblyCertificateWithBridge_of_safeLocalPayloadBundle
#print axioms book1CEWSPDPEpistemicBoundaryPort_of_safeLocalPayloadBundle
#print axioms book1NormalizedSafeLocalPayloadBundle_of_namedCertificateBoundary
#print axioms book1TransportCertificate_of_normalizedSafeLocalPayloadBundle
#print axioms book1CEWSPDPEpistemicBoundaryPort_of_normalizedSafeLocalPayloadBundle
#print axioms book1CEWSPDPEpistemicBoundaryPort_of_namedCertificateBoundary
#print axioms book1CEWSPDPEpistemicBoundaryPort_of_concreteAssembly
#print axioms book1CEWSPDPEpistemicBoundaryPort_of_concreteAssemblyWithBridge
#print axioms book1TransportCertificate_of_ambientCompiledRankModel
#print axioms deciderTransportHardToP_of_book1TransportCertificate
#print axioms book1_pSidePolynomialSPDP_of_decider
#print axioms no_DTMDecidesSATWithEncoding_of_book1CEWSPDP
#print axioms standardPvsNP_of_book1CEWSPDP

end PallLean.Paper93.DeepMath.PathB
