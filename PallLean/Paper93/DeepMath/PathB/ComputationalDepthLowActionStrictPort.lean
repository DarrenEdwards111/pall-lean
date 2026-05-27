import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207StrictPort
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStrictPortStandardBridge

/-!
# Low-action / polynomial-capacity strict port

This module implements the narrowed observer route.

The previous global coverage target tried to show that every arbitrary strict
observer has polynomial live-boundary capacity.  That is false for the current
`StrictDynamicNFrameLagrangianObserver`, because its `configActionRank : Nat ->
Nat` is unconstrained.

The corrected move is to make the observer class itself polynomial-capacity:
`LowActionStrictDynamicNFrameLagrangianObserver`.  This file defines the strict
port directly over that narrowed class and proves the Book-1 contradiction
there.

The remaining hard theorem is now explicit and appropriately narrowed:

```lean
Theorem207LowActionStrictLiveBoundaryPort enc
```

It says the God-Move lower-bound minor exists for every polynomial-capacity
strict observer at its own exponent.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Theorem 207 port restricted to polynomial-capacity / low-action strict
observers.

For every low-action observer, at a scale calibrated to its own exponent `k`,
there is a strict live minor for its underlying strict observer. -/
def Theorem207LowActionStrictLiveBoundaryPort
    (enc : ThreeCNFEncoding) : Prop :=
  forall L : LowActionStrictDynamicNFrameLagrangianObserver enc,
    exists n : Nat,
      n >= 2 ^ 20 /\
      4 * (L.k + 1) <= Nat.log 2 n /\
      Nonempty (StrictDynamicNFrameLagrangianLiveMinor enc L.base n)

/-- A full strict port implies the narrowed low-action port by querying the
full port at the low-action observer's own exponent. -/
theorem theorem207LowActionStrictPort_of_theorem207StrictPort
    {enc : ThreeCNFEncoding}
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    Theorem207LowActionStrictLiveBoundaryPort enc := by
  intro L
  rcases Hport L.k with ⟨n, hn20, hlog, HextractAt⟩
  exact ⟨n, hn20, hlog, HextractAt L.base⟩

/-- Low-action port plus the already-proved low-action Book-1 obstruction gives
no encoded SAT-deciding DTM.

This is the narrowed-class contradiction: a hypothetical SAT decider has the
canonical zero-rank low-action presentation; the low-action port supplies a
minor; the polynomial-capacity Book-1 theorem bounds it below the required
binomial floor, contradicting the minor's lower bound. -/
theorem no_DTMDecidesSATWithEncoding_of_theorem207LowActionStrictPort
    (enc : ThreeCNFEncoding)
    (Hport : Theorem207LowActionStrictLiveBoundaryPort enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  intro hdec
  rcases hdec with ⟨M, hM⟩
  let L : LowActionStrictDynamicNFrameLagrangianObserver enc :=
    lowActionStrictObserver_of_DTMDecidesSATWithEncoding hM
  rcases Hport L with ⟨n, hn20, hlog, hminor⟩
  rcases hminor with ⟨minor⟩
  have hbudget :
      L.base.toTrajectory.liveBoundaryRank n minor.input minor.time <
        Nat.choose (n / 3) (Nat.log 2 n) :=
    universalBook1BoundaryBudgetObstructionLowAction_theorem enc
      L.k n hn20 hlog L (Nat.le_refl L.k) minor.input minor.time
  have hlower :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.base.toTrajectory.liveBoundaryRank n minor.input minor.time := by
    rw [← minor.liveActionRank_eq_boundary]
    exact minor.rank_lower
  exact (Nat.not_le_of_lt hbudget) hlower

/-- The narrowed low-action port is enough for the bridged standard statement. -/
theorem standardPvsNP_of_theorem207LowActionStrictPort
    {enc : ThreeCNFEncoding}
    (B : StandardPvsNPBridge enc)
    (Hport : Theorem207LowActionStrictLiveBoundaryPort enc) :
    B.standardPvsNP :=
  B.standardPvsNP_iff_no_encodedSATDecider.mpr
    (no_DTMDecidesSATWithEncoding_of_theorem207LowActionStrictPort enc Hport)

/-- Exact package form for the narrowed route. -/
structure Theorem207LowActionStrictPortPackage
    (enc : ThreeCNFEncoding) : Type where
  hport : Theorem207LowActionStrictLiveBoundaryPort enc

/-- Package-level no-decider endpoint for the narrowed route. -/
theorem no_DTMDecidesSATWithEncoding_of_lowActionStrictPortPackage
    (enc : ThreeCNFEncoding)
    (pkg : Theorem207LowActionStrictPortPackage enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_theorem207LowActionStrictPort enc pkg.hport

/-- Package-level standard readout for the narrowed route. -/
theorem standardPvsNP_of_lowActionStrictPortPackage
    {enc : ThreeCNFEncoding}
    (B : StandardPvsNPBridge enc)
    (pkg : Theorem207LowActionStrictPortPackage enc) :
    B.standardPvsNP :=
  standardPvsNP_of_theorem207LowActionStrictPort B pkg.hport

/-- The old strict port still yields the narrowed package.  This theorem is
mostly migration glue for existing route files. -/
def lowActionStrictPortPackage_of_strictPortPackage
    {enc : ThreeCNFEncoding}
    (pkg : Theorem207StrictPortSeparationPackage enc) :
    Theorem207LowActionStrictPortPackage enc where
  hport := theorem207LowActionStrictPort_of_theorem207StrictPort pkg.hport

#print axioms theorem207LowActionStrictPort_of_theorem207StrictPort
#print axioms no_DTMDecidesSATWithEncoding_of_theorem207LowActionStrictPort
#print axioms standardPvsNP_of_theorem207LowActionStrictPort
#print axioms no_DTMDecidesSATWithEncoding_of_lowActionStrictPortPackage
#print axioms standardPvsNP_of_lowActionStrictPortPackage
#print axioms lowActionStrictPortPackage_of_strictPortPackage

end PallLean.Paper93.DeepMath.PathB
