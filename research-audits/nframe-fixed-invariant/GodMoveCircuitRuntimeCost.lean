import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposablePpolyDischarge

/-!
# A direct clock-to-circuit gate bound

For the repository's faithful machine simulator, expand the actual step-layer
gate accounting into a bound in the encoded input length `L` and run clock `t`:

`(circuitFor M L t).length ≤ circuitConstant M * (L+t+1)^4`.

The constant depends only on the fixed finite machine, through its number of
states. This is an unconditional bound on the constructed circuit's gate
count; it neither assumes polynomial runtime nor assumes any rank bound.
The simulator's correctness already accounts for its actual transitions,
head movement, tape snapshots, wire reuse, and repeated tape reads. This file
does not claim a running-time bound for an implementation of the compiler,
or a numerical bit-cost bound for evaluation of an arithmetic representation.
-/

namespace GodMoveCircuitRuntimeCost

open PallLean.Paper93.DeepMath.PathB
open ComposableMachine ComposableStepCircuit ComposablePpolyDischarge
open NFrameBoundaryTransducer SATCircuitSeparationBridge

/-- A fixed-machine constant for a quartic gate-count bound. -/
def circuitConstant (M : Machine) : ℕ :=
  (QM M + 2) * (61 * QM M + 10) + 5 * QM M + 3

theorem stepV_eq_polynomial (M : Machine) (S : ℕ) :
    stepV M S = 8 * QM M * S ^ 2 + 27 * QM M * S + 26 * QM M + 10 := by
  unfold stepV
  ring

theorem stepV_le_quadratic (M : Machine) (S : ℕ) (hS : 1 ≤ S) :
    stepV M S ≤ (61 * QM M + 10) * S ^ 2 := by
  have hSsq : S ≤ S ^ 2 := by nlinarith
  have h1sq : 1 ≤ S ^ 2 := hS.trans hSsq
  have hlin := Nat.mul_le_mul_left (27 * QM M) hSsq
  have hc := Nat.mul_le_mul_left (26 * QM M + 10) h1sq
  rw [stepV_eq_polynomial]
  nlinarith

theorem ports_le_linear (M : Machine) (S : ℕ) (hS : 1 ≤ S) :
    S + S + QM M ≤ (QM M + 2) * S := by
  have hq := Nat.mul_le_mul_left (QM M) hS
  nlinarith

/-- The concrete simulator's gate count is polynomial in input length and the
actual clock, with an explicit constant depending only on the machine. -/
theorem circuitFor_length_le_quartic (M : Machine) (L t : ℕ) :
    (circuitFor M L t).length ≤ circuitConstant M * (L + t + 1) ^ 4 := by
  let S := L + t + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have ht : t ≤ S := by dsimp [S]; omega
  have hS4 : S ≤ S ^ 4 := by
    calc
      S = S ^ 1 := by rw [pow_one]
      _ ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have h14 : 1 ≤ S ^ 4 := hS.trans hS4
  have hp := ports_le_linear M S hS
  have hs := stepV_le_quadratic M S hS
  have hsteps : t * ((S + S + QM M) * stepV M S) ≤
      ((QM M + 2) * (61 * QM M + 10)) * S ^ 4 := by
    calc
      _ ≤ S * (((QM M + 2) * S) * ((61 * QM M + 10) * S ^ 2)) := by
        exact Nat.mul_le_mul ht (Nat.mul_le_mul hp hs)
      _ = ((QM M + 2) * (61 * QM M + 10)) * S ^ 4 := by ring
  have hinit : S + S + QM M ≤ (QM M + 2) * S ^ 4 :=
    hp.trans (Nat.mul_le_mul_left _ hS4)
  have hfinal : QM M * 3 + QM M + 1 ≤ (4 * QM M + 1) * S ^ 4 := by
    have h := Nat.mul_le_mul_left (4 * QM M + 1) h14
    nlinarith
  rw [circuitFor_length, wvol_acceptT]
  change S + S + QM M +
    (t * ((S + S + QM M) * stepV M S) + (QM M * 3 + QM M + 1)) ≤
      circuitConstant M * S ^ 4
  calc
    _ ≤ (QM M + 2) * S ^ 4 +
        (((QM M + 2) * (61 * QM M + 10)) * S ^ 4 +
          (4 * QM M + 1) * S ^ 4) := Nat.add_le_add hinit (Nat.add_le_add hsteps hfinal)
    _ = circuitConstant M * S ^ 4 := by unfold circuitConstant; ring

/-- For a correct decider, the same explicit bound controls the existing
N-Frame circuit budget of each length slice. -/
theorem cbudget_lengthSlice_le_quartic (M : Machine) (f : List Bool → Bool)
    (T : ℕ → ℕ) (hDec : Decides M f T) (L : ℕ) :
    cbudget (lengthSlice f L) ≤ circuitConstant M * (L + T L + 1) ^ 4 :=
  (cbudget_lengthSlice_le M f T hDec L).trans (circuitFor_length_le_quartic M L (T L))

end GodMoveCircuitRuntimeCost

#print axioms GodMoveCircuitRuntimeCost.stepV_eq_polynomial
#print axioms GodMoveCircuitRuntimeCost.stepV_le_quadratic
#print axioms GodMoveCircuitRuntimeCost.ports_le_linear
#print axioms GodMoveCircuitRuntimeCost.circuitFor_length_le_quartic
#print axioms GodMoveCircuitRuntimeCost.cbudget_lengthSlice_le_quartic
