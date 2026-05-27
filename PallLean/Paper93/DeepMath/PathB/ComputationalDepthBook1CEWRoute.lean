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

/-- If the extracted sheet is exactly the calibrated Ramanujan/Tseitin hard
sheet, the hard-sheet extraction model is immediate.  This is the honest
concrete instantiation target for the remaining ambient/CEW route: downstream
code can replace `extractedRank` with the actual same-target PD/SPDP rank once
that object is wired in. -/
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

#print axioms book1CalibratedRamanujanTseitinHardNPLowerBound
#print axioms book1CalibratedHardSheetExtractionModel
#print axioms book1_superPolynomialGap
#print axioms hardRank_le_extracted_of_hardSheetExtractionModel
#print axioms extracted_le_pRank_of_ambientCompiledRankModel
#print axioms cewToPolynomialSPDP_of_countingCertificate
#print axioms book1TransportCertificate_of_ambientCompiledRankModel
#print axioms deciderTransportHardToP_of_book1TransportCertificate
#print axioms book1_pSidePolynomialSPDP_of_decider
#print axioms no_DTMDecidesSATWithEncoding_of_book1CEWSPDP
#print axioms standardPvsNP_of_book1CEWSPDP

end PallLean.Paper93.DeepMath.PathB
