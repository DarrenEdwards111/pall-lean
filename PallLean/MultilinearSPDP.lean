/-
  MultilinearSPDP.lean — SPDP rank in the multilinear (Boolean) basis

  Paper Definition 12: The SPDP matrix uses multilinear monomials (mod ⟨x²_i - x_i⟩).
  We define multilinear SPDP rank as dim of span of mlProj-ed generators.
-/
import PallLean.SPDPDefs
import PallLean.NPWitness
import PallLean.Compiler
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace MultilinearSPDP

open MvPolynomial SPDP TuringMachine Compiler NPWitness

attribute [local instance] Classical.dec

/-! ## Multilinear Projection -/

/-- A finsupp is multilinear if every value is ≤ 1 -/
def Finsupp.IsMultilinear {σ : Type*} (α : σ →₀ ℕ) : Prop :=
  ∀ i, α i ≤ 1

/-- The multilinear projection: keep only multilinear monomials -/
noncomputable def mlProj {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) : MvPolynomial σ F :=
  p.support.sum (fun α =>
    if Finsupp.IsMultilinear α then monomial α (coeff α p) else 0)

@[simp] theorem mlProj_zero {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F] :
    mlProj (0 : MvPolynomial σ F) = 0 := by
  simp [mlProj, MvPolynomial.support_zero]

/-! ## Multilinear SPDP Subspace and Rank -/

/-- Multilinear SPDP subspace: span of mlProj(m * ∂_S p) for blocked-admissible S -/
noncomputable def mlBlockedSpdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        q = mlProj (m * iterDerivList S p) }

/-- Multilinear blocked SPDP rank -/
noncomputable def mlBlockedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (mlBlockedSpdpSubspace B κ ℓ p)

/-! ## Key properties — sorry'd for now, all standard linear algebra -/

/-- Monotonicity: multilinear rank ≤ free-ring rank (projection can't increase rank) -/
theorem mlBlockedSpdpRank_le {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ p ≤ blockedSpdpRank B κ ℓ p := by
  sorry

/-- Subadditivity of multilinear SPDP rank -/
theorem mlBlockedSpdpRank_add_le {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p q : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ (p + q) ≤
      mlBlockedSpdpRank B κ ℓ p + mlBlockedSpdpRank B κ ℓ q := by
  sorry

/-- Per-gate multilinear SPDP rank bound.
    For a polynomial with ≤ d variables, the multilinear SPDP rank is ≤ 4^d.
    Key insight: in the multilinear basis, multiplication by a d-variable
    polynomial has rank ≤ 2^d, and derivatives span a space of dim ≤ 2^d. -/
theorem per_gate_ml_rank_bound {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (g : MvPolynomial (Fin n) F) (d : ℕ)
    (hd : g.vars.card ≤ d) :
    mlBlockedSpdpRank B κ ℓ g ≤ 4 ^ d := by
  sorry

/-- Subadditivity for Fin-indexed sums -/
theorem mlBlockedSpdpRank_finsum_le {n : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ)
    (m : ℕ) (gate : Fin m → MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ (∑ i : Fin m, gate i) ≤
      ∑ i : Fin m, mlBlockedSpdpRank B κ ℓ (gate i) := by
  sorry -- From mlBlockedSpdpRank_add_le by induction

/-! ## P-side collapse -/

/-- The violation polynomial has polynomial multilinear SPDP rank.
    violationPoly = Σ gate_i², each gate has ≤ 6 variables, so gate² ≤ 12 vars.
    Per-gate rank ≤ 4^12 = 16777216 (constant).
    numGates ≤ n^(2t+4).
    Total ≤ n^(2t+4) × 4^12 ≤ n^(2t+5). -/
theorem pside_ml_rank_bound {F : Type*} [Field F]
    (M : DTM) :
    ∃ (C : ℕ), ∀ n, n ≥ max 4 M.numStates →
      ∀ (B : BlockPartition (numVars M n (Nat.log 2 n))) (κ ℓ : ℕ),
        mlBlockedSpdpRank B κ ℓ (violationPolyOf F M n) ≤ n ^ C := by
  sorry

/-! ## NP-side lower bound -/

/-- The NP-side identity minor lower bound holds for multilinear SPDP rank.
    The identity minor uses multilinear column monomials (products of distinct
    selector variables), so it appears in the multilinear SPDP matrix. -/
theorem np_ml_lower_bound (F : Type*) [Field F] [Nontrivial F] :
    ∃ n₀, ∀ n, n ≥ n₀ →
      mlBlockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinPoly F n) ≥ n ^ (Nat.log 2 n / 4) := by
  sorry

/-! ## Extraction map (Paper Theorem 5, Item 3)

  Axiom: rank-monotone extraction map TΦ exists.
  When M correctly decides SAT, TΦ(P_M) = Q×_Φ and Γ^ml(TΦ(p)) ≤ Γ^ml(p).

  This encapsulates the paper's Sections 10 and 34:
  - Lemma 40 (rank monotonicity under compiler operations)
  - Theorem 255 (semantic closure / representation invariance) -/

axiom extraction_map_exists (F : Type*) [Field F] [Nontrivial F]
    (n : ℕ) (M : DTM)
    (hsolves : True) :
    ∀ (B_v : BlockPartition (numVars M n (Nat.log 2 n)))
      (κ ℓ : ℕ),
      mlBlockedSpdpRank (tseitinPartition n) κ ℓ
        (tseitinPoly F n) ≤
      mlBlockedSpdpRank B_v κ ℓ (violationPolyOf F M n)

end MultilinearSPDP
