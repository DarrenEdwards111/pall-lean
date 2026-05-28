import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinProtocolLowerBound

/-!
# Tseitin protocol magnification target

The restricted Tseitin protocol lower bound is real leverage, but only inside
its protocol model.  To reach unrestricted P-vs-NP one would need a
normal-form/magnification theorem:

* every P-time signed SAT decider can be converted into a local Tseitin
  protocol whose transcript fits inside the P-observer lightcone.

This file does **not** prove that theorem.  It makes it exact and proves the
downstream consequence: at a scale where the independent Tseitin direction
count exceeds the observer lightcone, such a normal form rules out P-time
signed SAT deciders.

So the "magic" is no longer vague.  It is the explicit
`PTimeTseitinProtocolMagnificationAt` input below.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## P-time signed SAT decider surface -/

/-- Placeholder for the concrete polynomial-time predicate on signed SAT
deciders.  It is deliberately kept separate from the restricted protocol model:
the magnification theorem below is exactly the missing claim that this ordinary
P-time surface normalizes into the protocol surface. -/
def PTimeSATPolynomialTime (_enc : SignedFormulaEncoding) (_M : DTM) : Prop :=
  True

/-- A signed SAT decider in the intended P-time observer class.

The polynomial-time predicate is kept explicit, as
`PTimeSATPolynomialTime`, rather than identified with the N-frame protocol
model.  A concrete machine model can later replace that predicate by an exact
time-bound definition. -/
structure PTimeSignedSATDecider
    (enc : SignedFormulaEncoding)
    (M : DTM) : Prop where
  decides : SignedDTMDecidesSAT enc M
  polynomial_time_cert : PTimeSATPolynomialTime enc M

/-! ## Normal-form / magnification target -/

/-- A P-time SAT decider has been normalized at one Tseitin scale into a local
protocol whose transcript fits inside the P-observer lightcone.

This is the restricted-protocol representation whose existence is the hard
magnification/normal-form claim. -/
structure PTimeTseitinProtocolNormalFormAt
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (M : DTM)
    (hM : SignedDTMDecidesSAT enc M)
    (n : Nat)
    (hn : n >= 1) : Type where
  protocol :
    LocalTseitinProtocolRealization (F.boundaryAt M hM n hn)
  fits_lightcone :
    protocol.transcript.bandwidth <= ObserverLightconeBandwidthLimit Pobs

/-- The exact "magic" theorem at one scale: every P-time signed SAT decider
normalizes into the restricted local Tseitin protocol model at that scale. -/
structure PTimeTseitinProtocolMagnificationAt
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (n : Nat)
    (hn : n >= 1) : Type where
  normalize :
    forall (M : DTM) (H : PTimeSignedSATDecider enc M),
      PTimeTseitinProtocolNormalFormAt F Pobs M H.decides n hn

/-- A selected scale where the independent direction count exceeds the
P-observer lightcone capacity. -/
structure IndependentTseitinLightconeGap
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver) : Type where
  n : Nat
  hn : n >= 1
  gap :
    ObserverLightconeBandwidthLimit Pobs < F.directionCountAt n hn

/-! ## Consequences of the magic theorem -/

/-- At a lightcone-gap scale, a protocol normal form for one P-time decider is
impossible. -/
theorem not_normalFormAt_of_lightconeGap
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (M : DTM)
    (H : PTimeSignedSATDecider enc M)
    (n : Nat)
    (hn : n >= 1)
    (hgap :
      ObserverLightconeBandwidthLimit Pobs < F.directionCountAt n hn) :
    Not (Nonempty
      (PTimeTseitinProtocolNormalFormAt F Pobs M H.decides n hn)) := by
  rintro ⟨NF⟩
  exact
    no_lightconeBoundedProtocol_of_independentAsymptoticGap
      F Pobs M H.decides n hn hgap
      ⟨NF.protocol, NF.fits_lightcone⟩

/-- If the one-scale magnification theorem holds at a lightcone-gap scale,
then there is no P-time signed SAT decider for the encoding. -/
theorem no_pTimeSignedSATDecider_of_magnificationAt
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (n : Nat)
    (hn : n >= 1)
    (hgap :
      ObserverLightconeBandwidthLimit Pobs < F.directionCountAt n hn)
    (Mag : PTimeTseitinProtocolMagnificationAt F Pobs n hn) :
    Not (exists M : DTM, PTimeSignedSATDecider enc M) := by
  rintro ⟨M, H⟩
  exact not_normalFormAt_of_lightconeGap
    F Pobs M H n hn hgap ⟨Mag.normalize M H⟩

/-- Gap-packaged version of the previous theorem. -/
theorem no_pTimeSignedSATDecider_of_magnificationAt_gap
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (G : IndependentTseitinLightconeGap F Pobs)
    (Mag : PTimeTseitinProtocolMagnificationAt F Pobs G.n G.hn) :
    Not (exists M : DTM, PTimeSignedSATDecider enc M) :=
  no_pTimeSignedSATDecider_of_magnificationAt
    F Pobs G.n G.hn G.gap Mag

/-- A family-level magnification theorem supplies the one-scale theorem at
every scale.  This is stronger than needed for the contradiction, but it is
the natural statement of a global normal-form result. -/
structure PTimeTseitinProtocolMagnification
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver) : Type where
  atScale :
    forall n : Nat, forall hn : n >= 1,
      PTimeTseitinProtocolMagnificationAt F Pobs n hn

/-- A global magnification theorem plus any lightcone-gap scale rules out
P-time signed SAT deciders. -/
theorem no_pTimeSignedSATDecider_of_magnification
    {enc : SignedFormulaEncoding}
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (G : IndependentTseitinLightconeGap F Pobs)
    (Mag : PTimeTseitinProtocolMagnification F Pobs) :
    Not (exists M : DTM, PTimeSignedSATDecider enc M) :=
  no_pTimeSignedSATDecider_of_magnificationAt_gap
    F Pobs G (Mag.atScale G.n G.hn)

/-! ## Kernel-only axiom trace -/

#print axioms not_normalFormAt_of_lightconeGap
#print axioms no_pTimeSignedSATDecider_of_magnificationAt
#print axioms no_pTimeSignedSATDecider_of_magnificationAt_gap
#print axioms no_pTimeSignedSATDecider_of_magnification

end PallLean.Paper93.DeepMath.PathB
