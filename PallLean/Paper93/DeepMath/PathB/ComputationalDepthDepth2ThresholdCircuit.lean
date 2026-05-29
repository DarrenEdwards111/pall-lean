import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignRankFactorization

/-!
# Depth-2 threshold circuits (`THR ∘ LTF`): the base fragment of the UPP bridge

This file defines a genuine depth-2 threshold circuit (`THR` of `LTF`s) at the
communication-matrix level and proves the *base fragment* of the sign-rank bridge:
**every bottom `LTF` gate has sign-rank `≤ 2`.**

**What is PROVED here (clean, no carried field):**
* `Depth2Threshold` — a real `THR ∘ LTF` circuit type: a top threshold of `s`
  bottom linear-threshold gates, each gate split across the row/column
  (Alice/Bob) coordinates as `sign(αₖ i + βₖ j)`.
* `Depth2Threshold.eval` — its communication matrix
  `sign(∑ₖ wₖ · sign(αₖ i + βₖ j) − θ)`.
* `bottomGate_hasSignRankLE_two` — each bottom gate's matrix has sign-rank `≤ 2`
  (its argument is rank-≤2, via `bipartiteHalfspace_hasSignRankLE_two`).

**What is OPEN (the research-grade top-gate / UPP step — NOT proved, NOT faked):**
The whole-circuit bound `signRank (C.eval) ≤ poly(C.s)` does **not** follow from the
base fragment: the top gate takes `sign` of `∑ₖ wₖ · sign(…)`, and each
`sign(αₖ i + βₖ j)` is a **full-rank** `±1` matrix, so the combination is not
low-rank.  The only known route is unbounded-error (UPP) communication
(`signRank ≤ 2^{UPP}`, `UPP(maj of s halfspaces) = O(log s)`), which requires
probabilistic communication complexity that is **not in Mathlib**.  That bound is
the open frontier; it is deliberately left unstated here rather than carried as a
hypothesis socket.  See `signRank` Forster bound (`ForsterLowerBound`) for the
matching lower-bound side once the UPP upper bound exists.
-/

namespace PallLean.Paper93.DeepMath.PathB

open scoped BigOperators

/-- A depth-2 threshold circuit (`THR ∘ LTF`) over an `m × n` communication matrix.
Each of the `s` bottom linear-threshold gates is split across the row coordinate
(weights `α k`) and the column coordinate (weights `β k`); the top gate is a
weighted threshold with weights `w` and bias `θ`. -/
structure Depth2Threshold (m n : Nat) where
  s : Nat
  α : Fin s -> Fin m -> ℝ
  β : Fin s -> Fin n -> ℝ
  w : Fin s -> ℝ
  θ : ℝ

namespace Depth2Threshold

variable {m n : Nat}

/-- The `k`-th bottom gate's communication matrix: `sign(αₖ i + βₖ j)`. -/
noncomputable def bottomGate (C : Depth2Threshold m n) (k : Fin C.s) :
    Fin m -> Fin n -> Bool :=
  bipartiteHalfspace (C.α k) (C.β k)

/-- The communication matrix computed by the whole circuit:
`sign(∑ₖ wₖ · sign(αₖ i + βₖ j) − θ)`. -/
noncomputable def eval (C : Depth2Threshold m n) : Fin m -> Fin n -> Bool :=
  fun i j => decide (0 < (∑ k, C.w k * sgn (C.bottomGate k i j)) - C.θ)

/-- **Base fragment of the UPP bridge (PROVED).**  Each bottom `LTF` gate has
sign-rank `≤ 2`: its argument `αₖ i + βₖ j` is a rank-≤2 matrix, so the explicit
`Fin 2` factorization realizes its sign pattern. -/
theorem bottomGate_hasSignRankLE_two (C : Depth2Threshold m n) (k : Fin C.s)
    (hne : ∀ i j, C.α k i + C.β k j ≠ 0) :
    HasSignRankLE (C.bottomGate k) 2 :=
  bipartiteHalfspace_hasSignRankLE_two (C.α k) (C.β k) hne

/-- **The open whole-circuit target** (stated as a plain predicate for reference;
NOT proved here — bounding it is the UPP step described in the module docstring).
Defining the target does not assume it. -/
def WholeCircuitSignRankBound (C : Depth2Threshold m n) (B : Nat) : Prop :=
  HasSignRankLE C.eval B

#print axioms bottomGate_hasSignRankLE_two

end Depth2Threshold

end PallLean.Paper93.DeepMath.PathB
