import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStrictPortStandardBridge

/-!
# Book 1 CEW/SPDP epistemic-boundary route

Book 1 suggests that the active obstruction should be phrased as an
epistemic-boundary/CEW route, not as containment of the same-sheet God-Move rank
inside a low-action live-boundary rank.

This file records that route as an explicit, audit-friendly port:

* P observers/deciders have bounded contextual-entanglement width (CEW).
* Bounded CEW gives polynomial SPDP rank.
* The hard NP family has super-polynomial SPDP rank.
* Any SAT decider would transport the hard-family rank into its P-side rank.
* The super-polynomial lower bound eventually beats every polynomial upper
  bound.

No old Step4 wrapper is imported here, and no CEW axiom is hidden as a theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

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
  /-- (A3) The hard NP family has the Book-1 super-polynomial SPDP lower bound. -/
  hardNPLowerBound :
    forall n : Nat, n ^ (Nat.log 2 n) <= hardRank n
  /-- Transport/no-loss: a SAT decider would realize the hard family inside its
  P-side observer rank.  This is the CEW-route analogue of the God-Move
  transport seam. -/
  deciderTransportHardToP :
    forall M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M ->
        forall n : Nat, hardRank n <= pRank M n
  /-- Growth separation: `n^log n` eventually beats every fixed polynomial. -/
  superPolynomialGap :
    forall d : Nat, exists n : Nat, n ^ d < n ^ (Nat.log 2 n)

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
  rcases B.superPolynomialGap d with ⟨n, hgap⟩
  have hlower_to_p : n ^ (Nat.log 2 n) <= B.pRank M n :=
    Nat.le_trans (B.hardNPLowerBound n) (B.deciderTransportHardToP M hM n)
  have hp_to_poly : B.pRank M n <= n ^ d := hpUpper n
  have hle : n ^ (Nat.log 2 n) <= n ^ d := Nat.le_trans hlower_to_p hp_to_poly
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

#print axioms book1_pSidePolynomialSPDP_of_decider
#print axioms no_DTMDecidesSATWithEncoding_of_book1CEWSPDP
#print axioms standardPvsNP_of_book1CEWSPDP

end PallLean.Paper93.DeepMath.PathB
