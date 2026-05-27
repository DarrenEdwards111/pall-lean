import PallLean.GodMoveCore

/-!
# Faithful decoder layer for Route B / Global God-Move

This file isolates the part of the Global God-Move that is already a clean
linear-rank theorem:

*if a faithful staged decoder/extraction witness exists, then the SPDP rank of
the extracted coupled hard sheet is bounded by the SPDP rank of the compiled
Cook-Levin polynomial.*

It deliberately does **not** prove the harder semantic theorem

`DecidesSAT M -> FaithfulDecoder M n ...`,

which remains the real paper-facing God-Move frontier. Instead, it gives that
frontier a precise target object.
-/

namespace PaperFaithfulSeparation

open SPDP MultilinearSPDP MvPolynomial TuringMachine

/--
A faithful decoder is the exact staged semantic witness needed for the
paper-faithful Route B extraction, together with the rank wrapper for that same
witness.

Conceptually this is the typed Lean version of:

`Fin bulk.rank -> Fin (liftCost boundary.rank)`

or, more precisely, of the assertion that the hard coupled boundary/SPDP object
is obtained from the compiled bulk object by a witness-free, instance-uniform,
block-local restriction/projection/relabeling map whose induced SPDP-rank
transport is monotone.

The important point is that this structure is **not** automatically obtained
from `DecidesSAT M`. The later God-Move theorem should prove that connection.
-/
structure FaithfulDecoder
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) where
  /-- The staged semantic extraction witness: restriction, projection, and
  output identification against the chosen coupled hard target. -/
  semantics : ExtractionMapSemantics M n hn2 htb hns hdec target
  /-- The rank-monotonicity wrapper for exactly that staged semantic witness. -/
  rankBridge : ExtractionMapRankBridge semantics

namespace FaithfulDecoder

/-- Forget a faithful decoder to the older Route-B extraction obligation. -/
theorem to_extraction_obligation
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (D : FaithfulDecoder M n hn2 htb hns hdec target) :
    GodMoveRouteB_ExtractionObligation M n hn2 htb hns hdec target := by
  exact extraction_from_semantics D.semantics D.rankBridge

/--
Rank transfer from a faithful decoder.

This is the formally proved part of the Global God-Move: once the faithful
semantic decoder exists, the coupled hard target cannot have larger SPDP rank
than the compiled Cook-Levin polynomial at the same `(κ, ℓ) = (log₂ n, log₂ n)`
parameters.
-/
theorem rank_transfer
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (D : FaithfulDecoder M n hn2 htb hns hdec target) :
    mlBlockedSpdpRank target.coupledPartition (Nat.log 2 n) (Nat.log 2 n)
        target.coupledPoly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  exact D.to_extraction_obligation

/-- A staged semantic witness already contains the same rank wrappers, so it can
be repackaged as a faithful decoder. -/
def ofSemantics
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (sem : ExtractionMapSemantics M n hn2 htb hns hdec target) :
    FaithfulDecoder M n hn2 htb hns hdec target where
  semantics := sem
  rankBridge := ExtractionMapRankBridge.ofSemantics sem

/-- Convenience version of rank transfer directly from staged semantics. -/
theorem rank_transfer_of_semantics
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (sem : ExtractionMapSemantics M n hn2 htb hns hdec target) :
    mlBlockedSpdpRank target.coupledPartition (Nat.log 2 n) (Nat.log 2 n)
        target.coupledPoly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  exact (ofSemantics sem).rank_transfer

end FaithfulDecoder

/--
The remaining Global God-Move frontier, now stated as a precise theorem target.

This is intentionally a `def`, not an axiom: it names the exact proposition that
must be proved to turn SAT-decider semantics into a faithful decoder. Proving
this is the hard semantic step. Once it is available, `FaithfulDecoder.rank_transfer`
gives the SPDP-rank inequality immediately.
-/
def FaithfulDecoderFromSATSemantics
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hdec : DecidesSAT M)
    (target : GodMoveExtractionTarget M n hn2 htb hns) : Prop :=
  Nonempty (FaithfulDecoder M n hn2 htb hns hdec target)

/-- If the remaining semantic theorem supplies a faithful decoder, rank transfer follows. -/
theorem rank_transfer_of_faithfulDecoderFromSATSemantics
    {M : DTM} {n : ℕ} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {hdec : DecidesSAT M}
    {target : GodMoveExtractionTarget M n hn2 htb hns}
    (hfaithful : FaithfulDecoderFromSATSemantics M n hn2 htb hns hdec target) :
    mlBlockedSpdpRank target.coupledPartition (Nat.log 2 n) (Nat.log 2 n)
        target.coupledPoly ≤
      mlBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  rcases hfaithful with ⟨D⟩
  exact D.rank_transfer

end PaperFaithfulSeparation
