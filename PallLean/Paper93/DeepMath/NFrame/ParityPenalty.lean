/-
  PallLean/Paper93/DeepMath/NFrame/ParityPenalty.lean

  Paper §28.3 pp. 137–138 — β-term of the N-Frame Lagrangian.

  The N-Frame action of paper §28.3 reads

      S_NF[Φ; P]
        = α · ∑_{{u,v} ∈ E_n} (Φ_u - Φ_v)²
        + β · ∑_{v ∈ V_n} (1 - χ(v) · sgn Φ_v)_+
        + λ · B(A(P)).

  This file formalises the second summand: the per-vertex
  **parity-penalty** term `(1 - χ(v) · sgn(Φ(v)))_+` and its sum
  over a finite vertex set `Fin n`. The positive-part enforces that
  misaligned pairs `χ(v) · sgn(Φ(v)) < 1` incur penalty, while aligned
  pairs contribute zero.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * `#print axioms` on every theorem returns only kernel primitives
      (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Sign
import Mathlib.Tactic

namespace PallLean.Paper93.DeepMath.NFrame

/-- Per-vertex parity penalty: `(1 − χ(v)·sgn(Φ(v)))₊`.
    The positive-part enforces that `χ(v)·sgn(Φ(v)) < 1` incurs penalty. -/
noncomputable def parityTerm (chi_v phi_v : ℝ) : ℝ :=
  max 0 (1 - chi_v * Real.sign phi_v)

/-- β-term of the N-Frame Lagrangian: sum of per-vertex parity penalties. -/
noncomputable def parityPenalty {n : ℕ} (chi phi : Fin n → ℝ) : ℝ :=
  ∑ v, parityTerm (chi v) (phi v)

/-- Per-vertex penalty is nonneg. -/
theorem parityTerm_nonneg (a b : ℝ) : 0 ≤ parityTerm a b :=
  le_max_left _ _

/-- Total parity penalty is nonneg. -/
theorem parityPenalty_nonneg {n : ℕ} (chi phi : Fin n → ℝ) :
    0 ≤ parityPenalty chi phi :=
  Finset.sum_nonneg (fun _v _ => parityTerm_nonneg _ _)

/-- If `χ(v)·sgn(Φ(v)) ≥ 1` pointwise, the penalty vanishes. -/
theorem parityPenalty_eq_zero_of_aligned {n : ℕ} (chi phi : Fin n → ℝ)
    (h : ∀ v, 1 ≤ chi v * Real.sign (phi v)) :
    parityPenalty chi phi = 0 := by
  apply Finset.sum_eq_zero
  intros v _hv
  unfold parityTerm
  rw [max_eq_left]
  · linarith [h v]

end PallLean.Paper93.DeepMath.NFrame
