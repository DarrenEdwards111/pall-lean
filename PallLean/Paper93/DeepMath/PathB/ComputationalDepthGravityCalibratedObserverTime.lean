import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKtRouteTheorem

/-
# Gravity-calibrated observer time

This file formalizes the useful part of the N-Frame gravity/conscious-time
idea without turning it into a false proof.

The book's gravitational clock is an entropy/area clock: boundary area gives an
information-capacity scale.  That is not itself a P-vs-NP separator, because
capacity is a space/information axis.  The separator must live on the time
axis.

So we split observer time into two profiles:

* `tauArea`: gravitational / entropy / boundary-area capacity clock;
* `tauCompute`: actual computational update budget, the K^t time axis.

The physical calibration is the domination relation

  tauCompute n <= tauArea n.

This lets gravity calibrate how much computation an observer can physically
afford, while the lower-bound target remains a K^t / computational-depth
statement.  The final theorem proves that the gravity-calibrated lower bound is
exactly `DeepSATSearch`, i.e. the canonical P-vs-NP search target in this
formal surface.
-/

namespace SATDepthMachine

/-! ## Gravity-calibrated clocks -/

/-- A split observer-time clock.

`tauArea` is the gravitational entropy/area capacity clock.
`tauCompute` is the actual computational-time budget used in K^t style witness
search.  The calibration field says computational updates must fit inside the
available boundary capacity. -/
structure GravityCalibratedObserverTime where
  tauArea : Nat -> Nat
  tauCompute : Nat -> Nat
  compute_le_area : ∀ n : Nat, tauCompute n <= tauArea n

/-- The K^t-relevant polynomial-time condition: the compute clock is
polynomially bounded. -/
def PolynomialObserverComputeTime
    (T : GravityCalibratedObserverTime) : Prop :=
  IsPolynomialLengthBound T.tauCompute

/-- The gravity-side polynomial condition: the boundary area/entropy clock is
polynomially bounded. -/
def PolynomialObserverAreaTime
    (T : GravityCalibratedObserverTime) : Prop :=
  IsPolynomialLengthBound T.tauArea

/-- A polynomial area/entropy clock induces a polynomial compute clock when
compute time is calibrated below area. -/
theorem polynomialComputeTime_of_polynomialAreaTime
    (T : GravityCalibratedObserverTime)
    (harea : PolynomialObserverAreaTime T) :
    PolynomialObserverComputeTime T := by
  rcases harea with ⟨k, c, harea_poly⟩
  exact ⟨k, c, fun n => Nat.le_trans (T.compute_le_area n) (harea_poly n)⟩

/-! ## K^tau witness cost -/

/-- K^tau cost is just the existing K^t cost with `tauCompute` as the time
budget.  The area clock is calibration metadata, not the load-bearing lower
bound. -/
def ObserverKtCostAtMost
    (D : DescribedCanonicalSurface)
    (T : GravityCalibratedObserverTime)
    (code : Nat) (φ : CNF) : Prop :=
  KtCostAtMost D.toDescriptionMachineModel T.tauCompute code φ

/-- A local witness description under the observer's compute clock. -/
def ObserverKtWitnessDescription
    (D : DescribedCanonicalSurface)
    (T : GravityCalibratedObserverTime)
    (φ : CNF) : Prop :=
  KtCostWitnessDescription D.toDescriptionMachineModel T.tauCompute φ

/-! ## Uniform observer search under a calibrated clock -/

/-- A searcher is within observer time `T` if its certified polynomial runtime
budget is pointwise below the observer's computational time budget. -/
def SearchMachineWithinObserverTime
    {C : CanonicalMachineSurface}
    (T : GravityCalibratedObserverTime)
    (M : SearchMachine C.toMachineModel) : Prop :=
  ∀ n : Nat, M.budget n <= T.tauCompute n

/-- A gravity-calibrated shallow SAT observer: one correct search machine runs
within the observer's compute-time clock. -/
def GravityCalibratedShallowSATSearch
    (C : CanonicalMachineSurface)
    (T : GravityCalibratedObserverTime) : Prop :=
  ∃ M : SearchMachine C.toMachineModel,
    SearchCorrect C.toMachineModel M ∧
      SearchMachineWithinObserverTime T M

/-- Any gravity-calibrated shallow observer is an ordinary shallow SAT searcher.
-/
theorem shallowSATSearch_of_gravityCalibratedShallow
    (C : CanonicalMachineSurface)
    (T : GravityCalibratedObserverTime)
    (h : GravityCalibratedShallowSATSearch C T) :
    ShallowSATSearch C.toMachineModel := by
  rcases h with ⟨M, hcorrect, _hwithin⟩
  exact ⟨M, hcorrect⟩

/-- The clock induced by one search machine's own runtime budget.  This is the
minimal calibration needed for the converse: if a correct polynomial searcher
exists, it supplies its own polynomial compute clock. -/
def observerTimeClockOfSearchMachine
    {C : CanonicalMachineSurface}
    (M : SearchMachine C.toMachineModel) :
    GravityCalibratedObserverTime where
  tauArea := M.budget
  tauCompute := M.budget
  compute_le_area := fun n => Nat.le_refl (M.budget n)

/-- A search machine's induced clock has polynomial compute time. -/
theorem polynomialComputeTime_of_searchMachineClock
    {C : CanonicalMachineSurface}
    (M : SearchMachine C.toMachineModel) :
    PolynomialObserverComputeTime (observerTimeClockOfSearchMachine M) := by
  rcases M.polyBudget with ⟨k, c, hpoly⟩
  exact ⟨k, c, hpoly⟩

/-- A search machine's induced clock has polynomial area time as well. -/
theorem polynomialAreaTime_of_searchMachineClock
    {C : CanonicalMachineSurface}
    (M : SearchMachine C.toMachineModel) :
    PolynomialObserverAreaTime (observerTimeClockOfSearchMachine M) := by
  rcases M.polyBudget with ⟨k, c, hpoly⟩
  exact ⟨k, c, hpoly⟩

/-- A correct search machine is gravity-calibrated shallow for its own induced
clock. -/
theorem gravityCalibratedShallow_of_searchCorrect
    {C : CanonicalMachineSurface}
    (M : SearchMachine C.toMachineModel)
    (hM : SearchCorrect C.toMachineModel M) :
    GravityCalibratedShallowSATSearch
      C (observerTimeClockOfSearchMachine M) := by
  exact ⟨M, hM, fun n => Nat.le_refl (M.budget n)⟩

/-! ## Lower-bound sockets and equivalences -/

/-- No polynomial compute-time observer can uniformly produce SAT witnesses.
This is the K^t/conscious-compute-time lower-bound socket. -/
def ComputeTimeSATLowerBound
    (C : CanonicalMachineSurface) : Prop :=
  ∀ T : GravityCalibratedObserverTime,
    PolynomialObserverComputeTime T ->
      ¬ GravityCalibratedShallowSATSearch C T

/-- No polynomial area-calibrated observer can uniformly produce SAT witnesses.
This is the gravity-calibrated version. -/
def GravityAreaCalibratedSATLowerBound
    (C : CanonicalMachineSurface) : Prop :=
  ∀ T : GravityCalibratedObserverTime,
    PolynomialObserverAreaTime T ->
      ¬ GravityCalibratedShallowSATSearch C T

/-- Deep SAT search implies the compute-time lower bound. -/
theorem computeTimeSATLowerBound_of_deepSATSearch
    (C : CanonicalMachineSurface)
    (hdeep : DeepSATSearch C.toMachineModel) :
    ComputeTimeSATLowerBound C := by
  intro T _hpoly hshallow
  exact hdeep (shallowSATSearch_of_gravityCalibratedShallow C T hshallow)

/-- The compute-time lower bound implies deep SAT search. -/
theorem deepSATSearch_of_computeTimeSATLowerBound
    (C : CanonicalMachineSurface)
    (hlower : ComputeTimeSATLowerBound C) :
    DeepSATSearch C.toMachineModel := by
  intro hshallow
  rcases hshallow with ⟨M, hM⟩
  exact hlower (observerTimeClockOfSearchMachine M)
    (polynomialComputeTime_of_searchMachineClock M)
    (gravityCalibratedShallow_of_searchCorrect M hM)

/-- The compute-time lower-bound socket is exactly deep SAT search. -/
theorem computeTimeSATLowerBound_iff_deepSATSearch
    (C : CanonicalMachineSurface) :
    ComputeTimeSATLowerBound C ↔ DeepSATSearch C.toMachineModel :=
  ⟨deepSATSearch_of_computeTimeSATLowerBound C,
    computeTimeSATLowerBound_of_deepSATSearch C⟩

/-- Deep SAT search also implies the gravity-area calibrated lower bound. -/
theorem gravityAreaCalibratedSATLowerBound_of_deepSATSearch
    (C : CanonicalMachineSurface)
    (hdeep : DeepSATSearch C.toMachineModel) :
    GravityAreaCalibratedSATLowerBound C := by
  intro T _harea hshallow
  exact hdeep (shallowSATSearch_of_gravityCalibratedShallow C T hshallow)

/-- The gravity-area calibrated lower bound implies deep SAT search. -/
theorem deepSATSearch_of_gravityAreaCalibratedSATLowerBound
    (C : CanonicalMachineSurface)
    (hlower : GravityAreaCalibratedSATLowerBound C) :
    DeepSATSearch C.toMachineModel := by
  intro hshallow
  rcases hshallow with ⟨M, hM⟩
  exact hlower (observerTimeClockOfSearchMachine M)
    (polynomialAreaTime_of_searchMachineClock M)
    (gravityCalibratedShallow_of_searchCorrect M hM)

/-- Gravity can calibrate observer time, but the resulting lower-bound socket is
still exactly deep SAT search. -/
theorem gravityAreaCalibratedSATLowerBound_iff_deepSATSearch
    (C : CanonicalMachineSurface) :
    GravityAreaCalibratedSATLowerBound C ↔
      DeepSATSearch C.toMachineModel :=
  ⟨deepSATSearch_of_gravityAreaCalibratedSATLowerBound C,
    gravityAreaCalibratedSATLowerBound_of_deepSATSearch C⟩

/-- Closure from the gravity-calibrated observer-time lower bound. -/
theorem noCanonicalSATDecisionInP_of_gravityAreaCalibratedSATLowerBound
    (C : CanonicalMachineSurface)
    (hlower : GravityAreaCalibratedSATLowerBound C) :
    ¬ CanonicalSATDecisionInP C :=
  canonicalNoDecider_of_deepSATSearch C
    (deepSATSearch_of_gravityAreaCalibratedSATLowerBound C hlower)

/-! ## Axiom trace -/

#print axioms polynomialComputeTime_of_polynomialAreaTime
#print axioms shallowSATSearch_of_gravityCalibratedShallow
#print axioms gravityCalibratedShallow_of_searchCorrect
#print axioms computeTimeSATLowerBound_iff_deepSATSearch
#print axioms gravityAreaCalibratedSATLowerBound_iff_deepSATSearch
#print axioms noCanonicalSATDecisionInP_of_gravityAreaCalibratedSATLowerBound

end SATDepthMachine
