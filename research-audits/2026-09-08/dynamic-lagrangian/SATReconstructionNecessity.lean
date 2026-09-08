import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSATBoundaryFoolingWidthLB
import Mathlib.Data.Fintype.Pi

/-!
SAT-specific necessity for the actual equality-CNF family. Correctness forces
injectivity at a one-way boundary. It yields n bits, not 2^n operations.
No claim is made that arbitrary SAT machines obey this one-way factorization.
-/
namespace SATReconstructionNecessity
open PallLean.Paper93.DeepMath.PathB
open SATDepthMachine PvsNPSATBoundaryFoolingWidthLB

theorem equalityCNF_boundary_injective {n : ℕ} {Boundary : Type*}
    (encode : (Fin n → Bool) → Boundary)
    (resume : Boundary → (Fin n → Bool) → Bool)
    (correct : ∀ a b, resume (encode a) b = true ↔ Satisfiable (equalityCNF a b)) :
    Function.Injective encode := by
  intro a b same
  have haa : resume (encode a) a = true :=
    (correct a a).mpr ((equalityCNF_satisfiable_iff a a).mpr rfl)
  rw [same] at haa
  exact ((equalityCNF_satisfiable_iff b a).mp ((correct b a).mp haa)).symm

theorem equalityCNF_boundary_bits {n bits : ℕ}
    (encode : (Fin n → Bool) → (Fin bits → Bool))
    (resume : (Fin bits → Bool) → (Fin n → Bool) → Bool)
    (correct : ∀ a b, resume (encode a) b = true ↔ Satisfiable (equalityCNF a b)) :
    n ≤ bits := by
  have hc := Fintype.card_le_of_injective encode
    (equalityCNF_boundary_injective encode resume correct)
  have hp : 2 ^ n ≤ 2 ^ bits := by simpa using hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp

/-- The lower bound is attained: retain the first block and compare to the
second. This is a semantic construction, not a formal TM runtime analysis. -/
theorem equalityCNF_boundary_bits_attained (n : ℕ) :
    ∃ (encode : (Fin n → Bool) → (Fin n → Bool))
      (resume : (Fin n → Bool) → (Fin n → Bool) → Bool),
      ∀ a b, resume (encode a) b = true ↔ Satisfiable (equalityCNF a b) := by
  classical
  refine ⟨id, fun a b => decide (a = b), ?_⟩
  intro a b
  simp [equalityCNF_satisfiable_iff]

/-- Only after a machine-specific space/time bound is established can this
one-way-boundary result constrain time. That premise is not hidden. -/
theorem equalityCNF_runtime_capacity {n bits initial rate time : ℕ}
    (encode : (Fin n → Bool) → (Fin bits → Bool))
    (resume : (Fin bits → Bool) → (Fin n → Bool) → Bool)
    (correct : ∀ a b, resume (encode a) b = true ↔ Satisfiable (equalityCNF a b))
    (space_time : bits ≤ initial + rate * time) :
    n ≤ initial + rate * time :=
  (equalityCNF_boundary_bits encode resume correct).trans space_time

end SATReconstructionNecessity

#print axioms SATReconstructionNecessity.equalityCNF_boundary_injective
#print axioms SATReconstructionNecessity.equalityCNF_boundary_bits
#print axioms SATReconstructionNecessity.equalityCNF_boundary_bits_attained
#print axioms SATReconstructionNecessity.equalityCNF_runtime_capacity
