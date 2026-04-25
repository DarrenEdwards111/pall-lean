/-
  PallLean/Paper93/DeepMath/PathB/SNFAction.lean

  Paper §28.3 (pp. 137–138): the N-Frame Lagrangian action functional

      S_NF[Φ; P]
        = α · ∑_{(u,v) ∈ E_n} (Φ_u - Φ_v)²
        + β · ∑_{v ∈ V_n} (1 - χ(v) · sgn Φ_v)_+
        + λ · B(A(P)).

  This file gives a finite-dimensional, concrete formalisation of the
  action with:

    * vertex set `Fin n`,
    * edge set `E : Finset (Fin n × Fin n)`,
    * Tseitin charges `χ : Fin n → ℤ`,
    * potential field `Φ : Fin n → ℝ`,
    * compiled positive operator `A : Matrix (Fin m) (Fin m) ℝ`,
    * a generic barrier `B : Matrix (Fin m) (Fin m) ℝ → ℝ`
      passed as a parameter (the concrete log-det barrier is *not*
      defined here — see `PallLean.Paper93.DeepMath.NFrame.Barrier`).

  We prove only the "kernel" facts requested:

    * the action decomposes as a sum of three pieces,
    * the kinetic term vanishes at Φ = 0 and at any constant Φ,
    * separate linearity in each of the three coefficients α, β, λ.

  We do *not* prove convexity, optimality, existence of minimisers,
  or anything about the barrier `B`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * `#print axioms` on every theorem returns only kernel primitives
      (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Sign
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace PallLean.Paper93.DeepMath.PathB

/-! ### Kinetic term -/

/-- Kinetic (Dirichlet) term of the N-Frame action:
`α · ∑_{(u,v) ∈ E} (Φ_u − Φ_v)²`.

Edges are encoded as a `Finset (Fin n × Fin n)`; this matches the
paper's pair-sum `∑_{u,v ∈ E_n}` once an orientation is chosen. -/
def SNFKineticTerm (α : ℝ) (n : ℕ) (E : Finset (Fin n × Fin n))
    (Φ : Fin n → ℝ) : ℝ :=
  α * ∑ e ∈ E, (Φ e.1 - Φ e.2) ^ 2

/-! ### Parity (β) term -/

/-- Per-vertex parity penalty `(1 − χ(v)·sgn Φ_v)_+`, with `χ(v) ∈ ℤ`
cast into ℝ for the product against `Real.sign Φ_v`. -/
noncomputable def SNFParityVertex (χ_v : ℤ) (Φ_v : ℝ) : ℝ :=
  max 0 (1 - (χ_v : ℝ) * Real.sign Φ_v)

/-- Parity (β) term of the N-Frame action:
`β · ∑_{v ∈ V_n} (1 − χ(v)·sgn Φ_v)_+`. -/
noncomputable def SNFParityTerm (β : ℝ) (n : ℕ) (χ : Fin n → ℤ)
    (Φ : Fin n → ℝ) : ℝ :=
  β * ∑ v, SNFParityVertex (χ v) (Φ v)

/-! ### Full action -/

/-- The full N-Frame Lagrangian action with a generic barrier
parameter `B`:
`S_NF[Φ; P] = α·kinetic + β·parity + λ·B(A)`. -/
noncomputable def SNFAction
    (α β lam : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ) (Φ : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  SNFKineticTerm α n E Φ + SNFParityTerm β n χ Φ + lam * B A

/-! ### Basic facts -/

/-- The kinetic term is non-negative when `α ≥ 0`. -/
theorem SNFKineticTerm_nonneg {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (E : Finset (Fin n × Fin n)) (Φ : Fin n → ℝ) :
    0 ≤ SNFKineticTerm α n E Φ := by
  unfold SNFKineticTerm
  exact mul_nonneg hα (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The parity term is non-negative when `β ≥ 0`. -/
theorem SNFParityTerm_nonneg {n : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (χ : Fin n → ℤ) (Φ : Fin n → ℝ) :
    0 ≤ SNFParityTerm β n χ Φ := by
  unfold SNFParityTerm SNFParityVertex
  exact mul_nonneg hβ
    (Finset.sum_nonneg (fun _ _ => le_max_left _ _))

/-! ### Vanishing of the kinetic term at zero / constant fields -/

/-- At `Φ ≡ 0`, every edge contributes `(0 - 0)² = 0`, so the kinetic
term is zero. -/
theorem SNFKineticTerm_zero_field
    {n : ℕ} (α : ℝ) (E : Finset (Fin n × Fin n)) :
    SNFKineticTerm α n E (fun _ => (0 : ℝ)) = 0 := by
  unfold SNFKineticTerm
  simp

/-- At any constant field `Φ ≡ c`, every edge contributes `(c - c)² = 0`,
so the kinetic term is zero. -/
theorem SNFKineticTerm_constant_field
    {n : ℕ} (α c : ℝ) (E : Finset (Fin n × Fin n)) :
    SNFKineticTerm α n E (fun _ => c) = 0 := by
  unfold SNFKineticTerm
  simp

/-- At `Φ ≡ 0`, the full action reduces to the parity-at-zero piece
plus `λ · B(A)`; in particular the kinetic part vanishes. -/
theorem SNFAction_zero_field
    (α β lam : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction α β lam n m E χ (fun _ => (0 : ℝ)) B A
      = SNFParityTerm β n χ (fun _ => (0 : ℝ)) + lam * B A := by
  unfold SNFAction
  rw [SNFKineticTerm_zero_field]
  ring

/-- At any constant field `Φ ≡ c`, the kinetic term vanishes; the full
action reduces to the parity-at-`c` piece plus `λ · B(A)`. -/
theorem SNFAction_constant_field
    (α β lam c : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction α β lam n m E χ (fun _ => c) B A
      = SNFParityTerm β n χ (fun _ => c) + lam * B A := by
  unfold SNFAction
  rw [SNFKineticTerm_constant_field]
  ring

/-! ### Linearity in α, β, λ separately -/

/-- The kinetic term is linear in α: `SNFKineticTerm (α₁+α₂) … = … + …`. -/
theorem SNFKineticTerm_add_alpha
    {n : ℕ} (α₁ α₂ : ℝ) (E : Finset (Fin n × Fin n)) (Φ : Fin n → ℝ) :
    SNFKineticTerm (α₁ + α₂) n E Φ
      = SNFKineticTerm α₁ n E Φ + SNFKineticTerm α₂ n E Φ := by
  unfold SNFKineticTerm
  ring

/-- The kinetic term scales by α: `SNFKineticTerm (s*α) … = s · SNFKineticTerm α …`. -/
theorem SNFKineticTerm_smul_alpha
    {n : ℕ} (s α : ℝ) (E : Finset (Fin n × Fin n)) (Φ : Fin n → ℝ) :
    SNFKineticTerm (s * α) n E Φ = s * SNFKineticTerm α n E Φ := by
  unfold SNFKineticTerm
  ring

/-- The parity term is linear in β. -/
theorem SNFParityTerm_add_beta
    {n : ℕ} (β₁ β₂ : ℝ) (χ : Fin n → ℤ) (Φ : Fin n → ℝ) :
    SNFParityTerm (β₁ + β₂) n χ Φ
      = SNFParityTerm β₁ n χ Φ + SNFParityTerm β₂ n χ Φ := by
  unfold SNFParityTerm
  ring

/-- The parity term scales by β. -/
theorem SNFParityTerm_smul_beta
    {n : ℕ} (s β : ℝ) (χ : Fin n → ℤ) (Φ : Fin n → ℝ) :
    SNFParityTerm (s * β) n χ Φ = s * SNFParityTerm β n χ Φ := by
  unfold SNFParityTerm
  ring

/-- Linearity of the action in α (β, λ, Φ, χ, B, A all fixed). -/
theorem SNFAction_add_alpha
    (α₁ α₂ β lam : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ) (Φ : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction (α₁ + α₂) β lam n m E χ Φ B A
      = SNFAction α₁ β lam n m E χ Φ B A
        + SNFKineticTerm α₂ n E Φ := by
  unfold SNFAction
  rw [SNFKineticTerm_add_alpha]
  ring

/-- Linearity of the action in β (α, λ, Φ, χ, B, A all fixed). -/
theorem SNFAction_add_beta
    (α β₁ β₂ lam : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ) (Φ : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction α (β₁ + β₂) lam n m E χ Φ B A
      = SNFAction α β₁ lam n m E χ Φ B A
        + SNFParityTerm β₂ n χ Φ := by
  unfold SNFAction
  rw [SNFParityTerm_add_beta]
  ring

/-- Linearity of the action in λ (α, β, Φ, χ, B, A all fixed). -/
theorem SNFAction_add_lambda
    (α β lam₁ lam₂ : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ) (Φ : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction α β (lam₁ + lam₂) n m E χ Φ B A
      = SNFAction α β lam₁ n m E χ Φ B A
        + lam₂ * B A := by
  unfold SNFAction
  ring

/-- Scalar form of α-linearity: `S_NF[α; β; λ; …] = α · kinetic₁ + β·parity + λ·B(A)`,
where `kinetic₁` is the kinetic term at unit α. -/
theorem SNFAction_smul_alpha
    (s α β lam : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ) (Φ : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction (s * α) β lam n m E χ Φ B A
      = s * SNFKineticTerm α n E Φ
        + SNFParityTerm β n χ Φ + lam * B A := by
  unfold SNFAction
  rw [SNFKineticTerm_smul_alpha]

/-- Scalar form of β-linearity. -/
theorem SNFAction_smul_beta
    (α s β lam : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ) (Φ : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction α (s * β) lam n m E χ Φ B A
      = SNFKineticTerm α n E Φ
        + s * SNFParityTerm β n χ Φ + lam * B A := by
  unfold SNFAction
  rw [SNFParityTerm_smul_beta]

/-- Scalar form of λ-linearity. -/
theorem SNFAction_smul_lambda
    (α β s lam : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ) (Φ : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction α β (s * lam) n m E χ Φ B A
      = SNFKineticTerm α n E Φ
        + SNFParityTerm β n χ Φ + s * (lam * B A) := by
  unfold SNFAction
  ring

end PallLean.Paper93.DeepMath.PathB
