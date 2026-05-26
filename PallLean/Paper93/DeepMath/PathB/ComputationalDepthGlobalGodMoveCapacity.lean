import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207StrictPort

/-!
# Global God-Move finite-capacity boundary theorem surface

This file encodes the Book-1 missing move in one place:

1. a single global capacity functional over strict observers,
2. a uniform live-boundary upper bound from that capacity,
3. a non-vacuous NP-vs-capacity obstruction,
4. direct no-decider consequence once strict port is present.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- A global God-Move capacity witness for the strict observer class.

`cap n` is a single boundary-capacity budget for length `n` that bounds every
strict observer's live boundary rank at every state/time, and is itself
polynomially bounded. -/
structure GlobalGodMoveCapacityWitness
    (enc : ThreeCNFEncoding) : Type 1 where
  cap : Nat -> Nat
  cap_bounds_liveBoundary :
    forall (L : StrictDynamicNFrameLagrangianObserver enc)
      (n : Nat) (input : Fin n -> Bool) (time : Nat),
      L.toTrajectory.liveBoundaryRank n input time <= cap n
  poly_exponent : Nat
  cap_le_poly : forall n : Nat, cap n <= n ^ poly_exponent

/-- Book-1-style uniform upper bound immediately read off from the global
capacity witness. -/
theorem uniform_liveBoundary_upperBound_of_globalGodMoveCapacity
    {enc : ThreeCNFEncoding}
    (C : GlobalGodMoveCapacityWitness enc) :
    forall (L : StrictDynamicNFrameLagrangianObserver enc)
      (n : Nat) (input : Fin n -> Bool) (time : Nat),
      L.toTrajectory.liveBoundaryRank n input time <= n ^ C.poly_exponent := by
  intro L n input time
  exact le_trans (C.cap_bounds_liveBoundary L n input time) (C.cap_le_poly n)

/-- Calibrated non-vacuous Book-1 obstruction from a single global capacity
functional: at scales calibrated to `poly_exponent`, every strict observer
boundary is below the NP binomial floor. -/
theorem book1_obstruction_at_globalGodMoveCapacityExponent
    {enc : ThreeCNFEncoding}
    (C : GlobalGodMoveCapacityWitness enc)
    {n : Nat}
    (hn20 : n >= 2 ^ 20)
    (hlog : 4 * (C.poly_exponent + 1) <= Nat.log 2 n) :
    forall (L : StrictDynamicNFrameLagrangianObserver enc)
      (input : Fin n -> Bool) (time : Nat),
      L.toTrajectory.liveBoundaryRank n input time <
        Nat.choose (n / 3) (Nat.log 2 n) := by
  intro L input time
  have hgap : n ^ C.poly_exponent < Nat.choose (n / 3) (Nat.log 2 n) :=
    arithmetic_gap_for_exponent C.poly_exponent n hn20 hlog
  exact lt_of_le_of_lt
    (uniform_liveBoundary_upperBound_of_globalGodMoveCapacity C L n input time)
    hgap

/-- Global God-Move closure theorem in calibrated-capacity form.

If a single polynomial global capacity functional exists for strict observers,
then strict port at exponent `poly_exponent` yields the no-decider endpoint. -/
theorem no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_globalGodMoveCapacity
    (enc : ThreeCNFEncoding)
    (Hport : Theorem207StrictLiveBoundaryPort enc)
    (C : GlobalGodMoveCapacityWitness enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  intro hdec
  have hL : Nonempty (StrictDynamicNFrameLagrangianObserver enc) :=
    strictObserver_nonempty_of_DTMDecidesSATWithEncoding hdec
  rcases hL with ⟨L⟩
  rcases Hport C.poly_exponent with ⟨n, hn20, hlog, Hn⟩
  rcases Hn L with ⟨minor⟩
  have hlower :
      Nat.choose (n / 3) (Nat.log 2 n) <=
        L.toTrajectory.liveBoundaryRank n minor.input minor.time := by
    simpa [minor.liveActionRank_eq_boundary] using minor.rank_lower
  have hupper :
      L.toTrajectory.liveBoundaryRank n minor.input minor.time <
        Nat.choose (n / 3) (Nat.log 2 n) :=
    book1_obstruction_at_globalGodMoveCapacityExponent C hn20 hlog
      L minor.input minor.time
  exact (Nat.not_le_of_lt hupper) hlower

#print axioms uniform_liveBoundary_upperBound_of_globalGodMoveCapacity
#print axioms book1_obstruction_at_globalGodMoveCapacityExponent
#print axioms no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_globalGodMoveCapacity

end PallLean.Paper93.DeepMath.PathB
