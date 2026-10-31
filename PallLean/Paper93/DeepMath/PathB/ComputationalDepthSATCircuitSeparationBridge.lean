import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparationTarget
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConditionalPvsNP

/-!
# The faithful SAT-to-circuit separation bridge

This file removes the abstract machine predicates from the N-Frame/circuit capstone and
connects it directly to the repository's actual separation target:

* `SeparationTarget.SAT_not_in_P`, defined using the faithful, uniform
  `ComposableMachine` model; and
* `NFrameCircuitLowerBoundTarget`, the super-polynomial `cbudget` lower bound for a
  length-indexed Boolean family.

The only remaining semantic seam is stated exactly as `ComposablePSubsetPpoly`: every
language decided by a faithful polynomial-time `ComposableMachine` has polynomially
bounded circuit budget on its fixed-length slices.  This is the standard uniform
TM-to-circuit simulation (`P ⊆ P/poly`).  The repository already proves the circuit
tableau for local machines and a concrete bounded-tape TM; what is not yet proved is the
translation from `ComposableMachine.Machine` (unbounded list tape, including reset moves)
to that circuit model with polynomial overhead.

No lower bound and no model simulation is assumed silently.  The capstone says exactly:

  `P ⊆ P/poly` for the faithful model
  + super-polynomial circuit complexity of the SAT slices
  ⇒ `SAT ∉ P`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Convert an `n`-bit vector into its canonical length-`n` list. -/
def wordOfFin {n : ℕ} (x : Fin n → Bool) : List Bool :=
  (List.finRange n).map x

@[simp] theorem wordOfFin_length {n : ℕ} (x : Fin n → Bool) :
    (wordOfFin x).length = n := by
  simp [wordOfFin]

/-- Read a finite word as a vector indexed by its length. -/
def finOfWord (w : List Bool) : Fin w.length → Bool :=
  fun i => w.get i

/-- The list/vector conversion loses no words. -/
@[simp] theorem wordOfFin_finOfWord (w : List Bool) :
    wordOfFin (finOfWord w) = w := by
  apply List.ext_get
  · simp
  · intro n h1 h2
    simp [wordOfFin, finOfWord]

/-- The fixed-length Boolean family induced by a language on finite words. -/
def lengthSlice (L : List Bool → Bool) (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x => L (wordOfFin x)

/-- The family of fixed-length slices is extensionally complete for the original word
language: every word is recovered at its own length. -/
@[simp] theorem lengthSlice_finOfWord (L : List Bool → Bool) (w : List Bool) :
    lengthSlice L w.length (finOfWord w) = L w := by
  simp [lengthSlice]

/-- SAT as a genuine length-indexed Boolean family, obtained directly from the same
`SATLang` used by the faithful target `SAT_not_in_P`. -/
noncomputable def SATFamily (n : ℕ) : (Fin n → Bool) → Bool :=
  lengthSlice SATLang n

@[simp] theorem SATFamily_apply {n : ℕ} (x : Fin n → Bool) :
    SATFamily n x = SATLang (wordOfFin x) := rfl

/-- The precise standard-model simulation still required by the circuit route:
every language in the repository's faithful uniform `P` has polynomial circuit budget
on its fixed-length slices.  This is a property of the already-defined models, not an
abstract machine predicate. -/
def ComposablePSubsetPpoly : Prop :=
  ∀ L : List Bool → Bool, InP L → PolyCBudget (lengthSlice L)

/-- The open SAT circuit lower bound is exactly non-membership of the SAT slices in the
`PolyCBudget` family class. -/
theorem sat_target_iff_not_poly_cbudget :
    NFrameCircuitLowerBoundTarget SATFamily ↔ ¬ PolyCBudget SATFamily := by
  exact superPoly_iff_not_poly SATFamily

/-- **The faithful circuit route to the actual target.**  Once the standard
`ComposableMachine`-to-circuit simulation is supplied, a super-polynomial circuit lower
bound for the exact SAT slices proves `SAT_not_in_P`. -/
theorem sat_target_implies_SAT_not_in_P
    (simulation : ComposablePSubsetPpoly)
    (hard : NFrameCircuitLowerBoundTarget SATFamily) :
    SAT_not_in_P := by
  intro hsatP
  have hpoly : PolyCBudget SATFamily := simulation SATLang hsatP
  exact (sat_target_iff_not_poly_cbudget.mp hard) hpoly

/-- Fully expanded capstone: no abstract complexity class or machine predicate remains.
The two premises are precisely the standard simulation theorem and the explicit SAT
circuit lower bound. -/
theorem faithful_separation_capstone
    (simulation : ∀ L : List Bool → Bool, InP L → PolyCBudget (lengthSlice L))
    (hard : ∀ k, ∃ n, n ^ k + k < cbudget (SATFamily n)) :
    ¬ InP SATLang := by
  exact sat_target_implies_SAT_not_in_P simulation hard

end PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge

#print axioms PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge.sat_target_implies_SAT_not_in_P
#print axioms PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge.faithful_separation_capstone
