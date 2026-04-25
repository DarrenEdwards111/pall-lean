import PallLean.Paper93.DeepMath.PathB.SNFAction
import PallLean.Paper93.DeepMath.PathB.AmplituhedronBarrier
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetIsHessian
import PallLean.Paper93.DeepMath.PathB.EulerLagrangeStationarity
import PallLean.Paper93.DeepMath.PathB.BridgeBDetRankReduction

/-!
# `NFrameLagrangianBundle.lean` — single integration / audit surface for Paper §28.3

This file is the single-import audit surface that bundles the five
round-1 formalisations of paper §28.3 (the N-Frame Lagrangian
`S_NF[Φ; P]`) authored by agents 1-5 in this round:

| #   | File                            | Public theorem (re-exported below)                                  |
|-----|---------------------------------|---------------------------------------------------------------------|
| 1   | `SNFAction.lean`                | `SNFAction_zero_field`                                              |
| 2   | `AmplituhedronBarrier.lean`     | `amplituhedronBarrier_identity` + `principalMinor_pos_of_posDef`    |
| 3   | `CompiledGadgetIsHessian.lean`  | `compiledGadget_eq_alpha_smul_one_plus_kinetic`                     |
| 4   | `EulerLagrangeStationarity.lean`| `kineticTerm_gradient_eq_laplacian_action`                          |
| 5   | `BridgeBDetRankReduction.lean`  | `det_rank_inequality_from_eigenvalues`                              |

The bundle theorem `nFrameLagrangian_round1_pieces` below conjoins one
key public fact from each of the five files into a single proposition.
The companion theorem `NFrameLagrangian_kernel_only_witnesses` names
which §28.3 pieces have been formalised in this round and which remain
deferred (Bridge A in particular).

## Honest scope of round 1

What we DID formalise (kernel-only, `[propext, Classical.choice, Quot.sound]`):

  * **Action functional** `S_NF[Φ; P] = α·kinetic + β·parity + λ·B(A)`,
    with `S_NF` collapsing to `λ·B(A)` plus the parity-at-zero piece
    when the field is zero.
  * **Barrier** `B(A) = -∑_{J∈𝒥} log det(A[J,J])` is well-defined,
    vanishes at `A = 1`, and stays finite on positive-definite `A`.
  * **Gadget = ridge + (½)·kinetic-Hessian** identity:
    `compiledGadget α n = α•I + (1/2)•kineticTermHessian 1 n`, exposing
    the §28.3 compiled gadget as a Tikhonov-regularised kinetic term.
  * **Euler–Lagrange α-piece**: closed-form gradient of the kinetic
    term equals `2α·(L_{K_n} Φ)`; gradient-zero ⟺ `Φ ∈ ker L_{K_n}`.
  * **Bridge B (det/rank) — arithmetic core**:
    `∑ log(1 + θ λᵢ) ≤ rk · log(1 + θ ‖A‖)` whenever the
    eigenvalues `λᵢ ≥ 0` are bounded by `‖A‖` and `rk` counts the
    strictly positive eigenvalues; full diagonal-matrix instance via
    `Matrix.det_diagonal`.

What we did NOT formalise in this round (honest gaps — see comment at the
bottom of this file for an exhaustive list):

  * **Bridge A** — the local-energy-to-rank piece
    `E_v ≥ α_0  ⇒  local SPDP rank ≥ κ` is *not* in this round. It
    requires the local energy / SPDP-rank machinery of §28.3 that has
    not been built yet on this branch.
  * Convexity of `-∑ log det` (the barrier).
  * Existence of stationary points of `S_NF`.
  * The `sgn`-derivative content of the parity term (the `(β/2)·χ·∂sgn(Φ)`
    side of the full Euler–Lagrange identity).
  * The barrier monotonicity beyond the trivial identity-only case.
  * The full SPDP-rank bridge (Bridge A composed with Bridge B).

These remain open for a future round 2 of paper §28.3 formalisation.

## Build / axiom audit

* `lake build PallLean.Paper93.DeepMath.PathB.NFrameLagrangianBundle` — OK.
* `#print axioms` on `nFrameLagrangian_round1_pieces` and
  `NFrameLagrangian_kernel_only_witnesses` returns
  `[propext, Classical.choice, Quot.sound]`.
* No `sorry`. No bespoke axioms.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameLagrangianBundle

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.BridgeBDetRankReduction
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS

/-!
## Re-exports of the five round-1 public theorems

For each agent's file we package the headline public theorem under a
stable name in this bundle namespace, so downstream callers have a
single import / single namespace surface for paper §28.3 round 1.
-/

/-- **Agent 1 (`SNFAction`).** At the zero phase field `Φ ≡ 0`, the
N-Frame action reduces to the parity term at zero plus `λ·B(A)`. The
α-kinetic piece vanishes. -/
theorem snfAction_zero_field
    (α β lam : ℝ) (n m : ℕ)
    (E : Finset (Fin n × Fin n))
    (χ : Fin n → ℤ)
    (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) :
    SNFAction α β lam n m E χ (fun _ => (0 : ℝ)) B A
      = SNFParityTerm β n χ (fun _ => (0 : ℝ)) + lam * B A :=
  SNFAction_zero_field α β lam n m E χ B A

/-- **Agent 2a (`AmplituhedronBarrier`).** The barrier vanishes at the
identity matrix. -/
theorem amplituhedronBarrier_identity_at_one (n : ℕ)
    (𝒥 : Finset (Finset (Fin n))) :
    amplituhedronBarrier 𝒥 (1 : Matrix (Fin n) (Fin n) ℝ) = 0 :=
  amplituhedronBarrier_identity n 𝒥

/-- **Agent 2b (`AmplituhedronBarrier`).** Every principal minor of a
positive-definite matrix is strictly positive — so the barrier is finite
on the positive-definite cone. -/
theorem principalMinor_posDef_pos {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (J : Finset (Fin n)) :
    0 < PallLean.Paper93.DeepMath.PathB.Positroid.principalMinor A J :=
  principalMinor_pos_of_posDef hA J

/-- **Agent 3 (`CompiledGadgetIsHessian`).** The §28.3 compiled gadget
decomposes as `α·I + (1/2)·kineticTermHessian 1 n`. -/
theorem compiledGadget_tikhonov_decomposition (α : ℝ) (n : ℕ) :
    compiledGadget α n
      = α • (1 : Matrix (Fin n) (Fin n) ℝ)
          + ((1 : ℝ) / 2) • kineticTermHessian 1 n :=
  compiledGadget_eq_alpha_smul_one_plus_kinetic α n

/-- **Agent 4 (`EulerLagrangeStationarity`).** The closed-form partial
derivative of the kinetic term equals `2α·(L_{K_n} Φ)_i`. -/
theorem kineticTerm_gradient_is_laplacian_action
    (α : ℝ) (n : ℕ) (Φ : Fin n → ℝ) (i : Fin n) :
    kineticTerm_partialDeriv α n i Φ
      = 2 * α *
          ((PallLean.Paper93.DeepMath.GraphSpectral.laplacian
              (PallLean.Paper93.DeepMath.LPS.completeAdj n)).mulVec Φ i) :=
  kineticTerm_gradient_eq_laplacian_action α n Φ i

/-- **Agent 5 (`BridgeBDetRankReduction`).** Arithmetic core of the
det/rank inequality: `∑ log(1 + θ λᵢ) ≤ rk · log(1 + θ ‖A‖)` whenever
the eigenvalues `λᵢ ≥ 0` are bounded by `‖A‖`. -/
theorem detRank_inequality_eigenvalueForm
    (n : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (eigenvalues : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ eigenvalues i)
    (operator_norm : ℝ)
    (h_bound : ∀ i, eigenvalues i ≤ operator_norm)
    (rk : ℕ)
    (h_rk_count :
      rk = (Finset.filter (fun i => 0 < eigenvalues i) Finset.univ).card) :
    ∑ i, Real.log (1 + θ * eigenvalues i)
      ≤ (rk : ℝ) * Real.log (1 + θ * operator_norm) :=
  det_rank_inequality_from_eigenvalues n θ hθ eigenvalues h_nonneg
    operator_norm h_bound rk h_rk_count

/-!
## The single bundled integration theorem
-/

/-- **Round-1 integration theorem.** Conjunction of the five round-1
pieces of paper §28.3 — one headline fact per agent's file.

Reading clause-by-clause:

* (1) `SNFAction_zero_field`  — kinetic part of the action vanishes at
  the zero field, so `S_NF[0; P] = β·parity(0) + λ·B(A)`.
* (2) `amplituhedronBarrier_identity` — `B(I) = 0`.
* (3) `compiledGadget_eq_alpha_smul_one_plus_kinetic` — the §28.3
  compiled gadget is the sum of a Tikhonov ridge `α·I` and one half of
  the kinetic-term Hessian on `K_n`.
* (4) `kineticTerm_gradient_eq_laplacian_action` — the closed-form
  gradient of the kinetic term is `2α·L_{K_n}·Φ`.
* (5) `det_rank_inequality_from_eigenvalues` — the eigenvalue-form det/rank
  inequality from Bridge B.

The conjunction is stated existentially over arbitrary inputs of each
piece; the pointwise content is exactly the five public theorems. -/
theorem nFrameLagrangian_round1_pieces :
    -- (1) Action vanishes at zero field.
    (∀ (α β lam : ℝ) (n m : ℕ) (E : Finset (Fin n × Fin n))
        (χ : Fin n → ℤ) (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
        (A : Matrix (Fin m) (Fin m) ℝ),
        SNFAction α β lam n m E χ (fun _ => (0 : ℝ)) B A
          = SNFParityTerm β n χ (fun _ => (0 : ℝ)) + lam * B A)
  ∧ -- (2) Amplituhedron barrier vanishes at the identity matrix.
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
        amplituhedronBarrier 𝒥 (1 : Matrix (Fin n) (Fin n) ℝ) = 0)
  ∧ -- (3) Compiled gadget = α·I + (1/2)·kineticTermHessian 1 n.
    (∀ (α : ℝ) (n : ℕ),
        compiledGadget α n
          = α • (1 : Matrix (Fin n) (Fin n) ℝ)
              + ((1 : ℝ) / 2) • kineticTermHessian 1 n)
  ∧ -- (4) Closed-form kinetic gradient = 2α·(L Φ).
    (∀ (α : ℝ) (n : ℕ) (Φ : Fin n → ℝ) (i : Fin n),
        kineticTerm_partialDeriv α n i Φ
          = 2 * α *
              ((PallLean.Paper93.DeepMath.GraphSpectral.laplacian
                  (PallLean.Paper93.DeepMath.LPS.completeAdj n)).mulVec Φ i))
  ∧ -- (5) Bridge B arithmetic core.
    (∀ (n : ℕ) (θ : ℝ), 0 < θ →
        ∀ (eigenvalues : Fin n → ℝ),
            (∀ i, 0 ≤ eigenvalues i) →
        ∀ (operator_norm : ℝ),
            (∀ i, eigenvalues i ≤ operator_norm) →
        ∀ (rk : ℕ),
            rk = (Finset.filter (fun i => 0 < eigenvalues i) Finset.univ).card →
            ∑ i, Real.log (1 + θ * eigenvalues i)
              ≤ (rk : ℝ) * Real.log (1 + θ * operator_norm)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α β lam n m E χ B A
    exact SNFAction_zero_field α β lam n m E χ B A
  · intro n 𝒥
    exact amplituhedronBarrier_identity n 𝒥
  · intro α n
    exact compiledGadget_eq_alpha_smul_one_plus_kinetic α n
  · intro α n Φ i
    exact kineticTerm_gradient_eq_laplacian_action α n Φ i
  · intro n θ hθ eigenvalues h_nonneg operator_norm h_bound rk h_rk_count
    exact det_rank_inequality_from_eigenvalues n θ hθ eigenvalues h_nonneg
      operator_norm h_bound rk h_rk_count

/-!
## The single integration theorem naming what is in vs. what is out

`NFrameLagrangian_kernel_only_witnesses` is the bundle's main public
audit surface. Its statement is exactly `nFrameLagrangian_round1_pieces`
— this is the kernel-only witness theorem requested by the spec.

The doc-comment at the top of this file (and the fenced comment below)
honestly enumerate the §28.3 pieces NOT in this round, in particular
**Bridge A** (the local-energy-to-rank piece). -/
theorem NFrameLagrangian_kernel_only_witnesses :
    -- (1) Action vanishes at zero field.
    (∀ (α β lam : ℝ) (n m : ℕ) (E : Finset (Fin n × Fin n))
        (χ : Fin n → ℤ) (B : Matrix (Fin m) (Fin m) ℝ → ℝ)
        (A : Matrix (Fin m) (Fin m) ℝ),
        SNFAction α β lam n m E χ (fun _ => (0 : ℝ)) B A
          = SNFParityTerm β n χ (fun _ => (0 : ℝ)) + lam * B A)
  ∧ -- (2) Amplituhedron barrier vanishes at the identity matrix.
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
        amplituhedronBarrier 𝒥 (1 : Matrix (Fin n) (Fin n) ℝ) = 0)
  ∧ -- (3) Compiled gadget = α·I + (1/2)·kineticTermHessian 1 n.
    (∀ (α : ℝ) (n : ℕ),
        compiledGadget α n
          = α • (1 : Matrix (Fin n) (Fin n) ℝ)
              + ((1 : ℝ) / 2) • kineticTermHessian 1 n)
  ∧ -- (4) Closed-form kinetic gradient = 2α·(L Φ).
    (∀ (α : ℝ) (n : ℕ) (Φ : Fin n → ℝ) (i : Fin n),
        kineticTerm_partialDeriv α n i Φ
          = 2 * α *
              ((PallLean.Paper93.DeepMath.GraphSpectral.laplacian
                  (PallLean.Paper93.DeepMath.LPS.completeAdj n)).mulVec Φ i))
  ∧ -- (5) Bridge B arithmetic core.
    (∀ (n : ℕ) (θ : ℝ), 0 < θ →
        ∀ (eigenvalues : Fin n → ℝ),
            (∀ i, 0 ≤ eigenvalues i) →
        ∀ (operator_norm : ℝ),
            (∀ i, eigenvalues i ≤ operator_norm) →
        ∀ (rk : ℕ),
            rk = (Finset.filter (fun i => 0 < eigenvalues i) Finset.univ).card →
            ∑ i, Real.log (1 + θ * eigenvalues i)
              ≤ (rk : ℝ) * Real.log (1 + θ * operator_norm)) :=
  nFrameLagrangian_round1_pieces

/-!
## Honest gap log — what §28.3 we did NOT formalise in round 1
-----------------------------------------------------------------

```
================================================================
HONEST GAP LOG — Paper §28.3 round-1 NFrameLagrangianBundle
================================================================
The five files imported above cover the algebraic / structural
skeleton of the §28.3 N-Frame Lagrangian. The following pieces of
§28.3 are **NOT** formalised in this round and remain open:

  (G1) Bridge A — the local-energy-to-rank piece:
         E_v ≥ α_0  ⟹  local SPDP rank ≥ κ.
       This requires the local-energy functional and the SPDP
       (signed positive determinantal product) rank bound, neither
       of which exists yet on this branch. Future work for §28.3
       round 2.

  (G2) Convexity of the barrier  −∑_{J∈𝒥} log det(A[J,J]).
       The barrier is well-defined and finite on the positive-
       definite cone (proved here), but its convexity in the
       Loewner order is NOT formalised. This would require
       `Real.log` concavity + `Matrix.det` log-concavity + a
       summation-of-concave argument that we do not develop.

  (G3) Existence of stationary points of `S_NF`.
       We have the closed-form Euler–Lagrange α-piece (gradient
       of kinetic equals `2α·L Φ`, agent 4), but we do NOT
       construct any specific stationary `Φ` for the full
       three-term action. In particular, no minimiser is
       exhibited.

  (G4) The `sgn`-derivative content of the parity term:
       `(β/2)·χ·∂sgn(Φ)` (the right-hand side of the full
       Euler–Lagrange identity at line 6878 of the paper). Sgn is
       non-differentiable; a faithful treatment requires the
       subgradient of `sgn`, which is OUT of scope here.

  (G5) Barrier monotonicity beyond the trivial identity-only
       case. We prove `B(I) = 0` and a trivial mono on `𝒥` at the
       identity, but NOT general monotonicity in `A` along the
       Loewner cone.

  (G6) The full SPDP-rank bridge (Bridge A ∘ Bridge B).
       We have the arithmetic core of Bridge B (agent 5) and we
       have the kinetic-term Tikhonov decomposition (agent 3),
       but the composition step  E_v ≥ α_0  ⟹  log det bound
       (i.e. plumbing Bridge A through Bridge B) is NOT closed.
       This is the principal "round 2" deliverable.

================================================================
```

The integration theorem above honestly reflects this gap: the
conjunction `nFrameLagrangian_round1_pieces` references only the
five pieces (1)-(5) listed in the table at the top of this file,
and does NOT claim Bridge A or any of (G1)-(G6).
-/

end PallLean.Paper93.DeepMath.PathB.NFrameLagrangianBundle
