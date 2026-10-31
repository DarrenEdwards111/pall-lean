import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Toward the TC⁰ frontier: single-threshold-gate SAT by maximizing (the honest sub-rung)

The pipeline's verify gate *rejects* general TC⁰-SAT — a fast algorithm for constant-depth threshold
circuits is an open problem (it would give `NEXP ⊄ TC⁰`).  But the *atom* of TC⁰, a single **linear
threshold function** (LTF) `[∑ wᵢ xᵢ ≥ θ]`, has an easy SAT: pick the assignment that maximizes the
weighted sum — `xᵢ = 1` exactly when `wᵢ > 0`.  So the LTF is satisfiable iff that maximum meets `θ`.
One pass, no search.

Built through the Mikoshi pipeline: mikoshilang/SymPy gated the maximization (`w=[3,-2,5,-1,4]`: brute
max `= 12 =` sum of positive weights) before this Lean proof.

## What is proved

* **`ltf_sat_iff`** — `(∃ x, θ ≤ ∑ᵢ [xᵢ]·wᵢ) ↔ θ ≤ ∑ᵢ [wᵢ>0]·wᵢ`.  The threshold is satisfiable iff the
  maximizing assignment (`xᵢ = 1 ⟺ wᵢ > 0`) meets it.  Forward: every term is `≤` the maximizing term
  (`Finset.sum_le_sum`, closed by `omega`).  Backward: the maximizing assignment is an input.

## Honest scope

A complete, real fast-SAT — for a **single** linear threshold gate (the atom of TC⁰).  It fills
`Attack.decides` for LTFs.  **General** (multi-layer) TC⁰-SAT is the open frontier the pipeline gate
rejected — that step is `NEXP ⊄ TC⁰`, above Williams' ACC⁰ result, and it is the wall.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LTFFastSAT

open Finset

variable {n : ℕ}

/-- The weighted sum an assignment achieves for weights `w`: `∑ᵢ (if xᵢ then wᵢ else 0)`. -/
def weightedSum (w : Fin n → ℤ) (x : Fin n → Bool) : ℤ := ∑ i, cond (x i) (w i) 0

/-- The maximizing assignment: take input `i` iff its weight is positive. -/
def maxAssign (w : Fin n → ℤ) : Fin n → Bool := fun i => decide (0 < w i)

/-- The linear threshold function `[∑ wᵢ xᵢ ≥ θ]` is satisfiable. -/
def LTFSat (w : Fin n → ℤ) (θ : ℤ) : Prop := ∃ x, θ ≤ weightedSum w x

/-- **Single-threshold-gate SAT by maximizing (proved).**  An LTF is satisfiable iff the maximizing
assignment (take `i` iff `wᵢ > 0`) meets the threshold — one pass, no `2^n` search. -/
theorem ltf_sat_iff (w : Fin n → ℤ) (θ : ℤ) :
    LTFSat w θ ↔ θ ≤ weightedSum w (maxAssign w) := by
  constructor
  · rintro ⟨x, hx⟩
    refine le_trans hx ?_
    unfold weightedSum
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hw : 0 < w i
    · have hm : maxAssign w i = true := by simp [maxAssign, hw]
      rw [hm]; cases x i <;> simp only [cond_true, cond_false] <;> omega
    · have hm : maxAssign w i = false := by simp [maxAssign, hw]
      rw [hm]; cases x i <;> simp only [cond_true, cond_false] <;> omega
  · exact fun h => ⟨maxAssign w, h⟩

end PallLean.Paper93.DeepMath.PathB.LTFFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.LTFFastSAT.ltf_sat_iff
