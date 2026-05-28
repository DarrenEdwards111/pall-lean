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

/-- A supplied polynomial-time surface for signed SAT deciders.

The file does not define polynomial time as `True`: the caller must provide the
machine-class predicate.  This keeps the endpoint as "no decider in this P-time
class", rather than the false statement that no DTM decides SAT at all. -/
structure PTimeSATPolynomialTime (_enc : SignedFormulaEncoding) : Type where
  isPTime : DTM -> Prop

/-- A signed SAT decider in the intended P-time observer class.

The polynomial-time predicate is supplied by `PT`, rather than identified with
the N-frame protocol model.  A concrete machine model can instantiate `PT` with
an exact time-bound definition. -/
structure PTimeSignedSATDecider
    (enc : SignedFormulaEncoding)
    (PT : PTimeSATPolynomialTime enc)
    (M : DTM) : Prop where
  decides : SignedDTMDecidesSAT enc M
  polynomial_time_cert : PT.isPTime M

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
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (n : Nat)
    (hn : n >= 1) : Type where
  normalize :
    forall (M : DTM) (H : PTimeSignedSATDecider enc PT M),
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
    {PT : PTimeSATPolynomialTime enc}
    (H : PTimeSignedSATDecider enc PT M)
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
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (n : Nat)
    (hn : n >= 1)
    (hgap :
      ObserverLightconeBandwidthLimit Pobs < F.directionCountAt n hn)
    (Mag : PTimeTseitinProtocolMagnificationAt PT F Pobs n hn) :
    Not (exists M : DTM, PTimeSignedSATDecider enc PT M) := by
  rintro ⟨M, H⟩
  exact not_normalFormAt_of_lightconeGap
    F Pobs M H n hn hgap ⟨Mag.normalize M H⟩

/-- The one-scale magnification theorem is always constructible from the
no-decider endpoint, but only vacuously: there is no P-time signed SAT decider
to normalize.

This is the precise conservation-of-difficulty direction.  It does not supply a
normal-form construction for deciders; it shows that such a construction follows
once the endpoint has already been proved. -/
def magnificationAt_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (n : Nat)
    (hn : n >= 1)
    (hno : Not (exists M : DTM, PTimeSignedSATDecider enc PT M)) :
    PTimeTseitinProtocolMagnificationAt PT F Pobs n hn where
  normalize M H := False.elim (hno ⟨M, H⟩)

/-- Propositional version of the vacuous construction above. -/
theorem nonempty_magnificationAt_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (n : Nat)
    (hn : n >= 1)
    (hno : Not (exists M : DTM, PTimeSignedSATDecider enc PT M)) :
    Nonempty (PTimeTseitinProtocolMagnificationAt PT F Pobs n hn) :=
  ⟨magnificationAt_of_no_pTimeSignedSATDecider PT F Pobs n hn hno⟩

/-- At a lightcone-gap scale, the one-scale magnification theorem is equivalent
to the no-P-time-signed-SAT-decider endpoint.

So this theorem cannot be an independent bridge inside the present framework:
proving the left side unconditionally would already prove the endpoint on the
right. -/
theorem magnificationAt_iff_no_pTimeSignedSATDecider_of_gap
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (n : Nat)
    (hn : n >= 1)
    (hgap :
      ObserverLightconeBandwidthLimit Pobs < F.directionCountAt n hn) :
    Nonempty (PTimeTseitinProtocolMagnificationAt PT F Pobs n hn) <->
      Not (exists M : DTM, PTimeSignedSATDecider enc PT M) := by
  constructor
  · rintro ⟨Mag⟩
    exact no_pTimeSignedSATDecider_of_magnificationAt
      PT F Pobs n hn hgap Mag
  · intro hno
    exact nonempty_magnificationAt_of_no_pTimeSignedSATDecider
      PT F Pobs n hn hno

/-- Gap-packaged version of the previous theorem. -/
theorem no_pTimeSignedSATDecider_of_magnificationAt_gap
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (G : IndependentTseitinLightconeGap F Pobs)
    (Mag : PTimeTseitinProtocolMagnificationAt PT F Pobs G.n G.hn) :
    Not (exists M : DTM, PTimeSignedSATDecider enc PT M) :=
  no_pTimeSignedSATDecider_of_magnificationAt
    PT F Pobs G.n G.hn G.gap Mag

/-- A family-level magnification theorem supplies the one-scale theorem at
every scale.  This is stronger than needed for the contradiction, but it is
the natural statement of a global normal-form result. -/
structure PTimeTseitinProtocolMagnification
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver) : Type where
  atScale :
    forall n : Nat, forall hn : n >= 1,
      PTimeTseitinProtocolMagnificationAt PT F Pobs n hn

/-- A global magnification theorem plus any lightcone-gap scale rules out
P-time signed SAT deciders. -/
theorem no_pTimeSignedSATDecider_of_magnification
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (G : IndependentTseitinLightconeGap F Pobs)
    (Mag : PTimeTseitinProtocolMagnification PT F Pobs) :
    Not (exists M : DTM, PTimeSignedSATDecider enc PT M) :=
  no_pTimeSignedSATDecider_of_magnificationAt_gap
    PT F Pobs G (Mag.atScale G.n G.hn)

/-- A global magnification theorem is constructible from the no-decider
endpoint, but only vacuously at every scale. -/
def magnification_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (hno : Not (exists M : DTM, PTimeSignedSATDecider enc PT M)) :
    PTimeTseitinProtocolMagnification PT F Pobs where
  atScale n hn :=
    magnificationAt_of_no_pTimeSignedSATDecider
      PT F Pobs n hn hno

/-- Propositional form of the vacuous global construction. -/
theorem nonempty_magnification_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (hno : Not (exists M : DTM, PTimeSignedSATDecider enc PT M)) :
    Nonempty (PTimeTseitinProtocolMagnification PT F Pobs) :=
  ⟨magnification_of_no_pTimeSignedSATDecider PT F Pobs hno⟩

/-- Once any lightcone-gap scale exists, global magnification is equivalent to
the no-P-time-signed-SAT-decider endpoint.

This is the formal guardrail for the "magic" theorem: an unconditional proof of
global magnification at a gap would already be an unconditional proof of the
endpoint. -/
theorem magnification_iff_no_pTimeSignedSATDecider_of_gap
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (F : IndependentAsymptoticSignedTseitinExpanderFamily enc)
    (Pobs : PClassLocalPhysicalObserver)
    (G : IndependentTseitinLightconeGap F Pobs) :
    Nonempty (PTimeTseitinProtocolMagnification PT F Pobs) <->
      Not (exists M : DTM, PTimeSignedSATDecider enc PT M) := by
  constructor
  · rintro ⟨Mag⟩
    exact no_pTimeSignedSATDecider_of_magnification
      PT F Pobs G Mag
  · intro hno
    exact nonempty_magnification_of_no_pTimeSignedSATDecider
      PT F Pobs hno

/-! ## Kernel-only axiom trace -/

#print axioms not_normalFormAt_of_lightconeGap
#print axioms no_pTimeSignedSATDecider_of_magnificationAt
#print axioms nonempty_magnificationAt_of_no_pTimeSignedSATDecider
#print axioms magnificationAt_iff_no_pTimeSignedSATDecider_of_gap
#print axioms no_pTimeSignedSATDecider_of_magnificationAt_gap
#print axioms no_pTimeSignedSATDecider_of_magnification
#print axioms nonempty_magnification_of_no_pTimeSignedSATDecider
#print axioms magnification_iff_no_pTimeSignedSATDecider_of_gap

end PallLean.Paper93.DeepMath.PathB
