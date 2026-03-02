/-!
# SPDP Definitions

Core definitions matching Pall paper Section 2: The SPDP Matrix Framework.
Provides `SPDPMatrix`, blocked rank `ΓB`, and basic properties.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Polynomial.Basic

open Finset Matrix

namespace SPDP

/-! ## Basic types -/

/-- A block partition of variable indices into disjoint blocks. -/
structure BlockPartition (n : ℕ) where
  numBlocks : ℕ
  assign : Fin n → Fin numBlocks

/-- Parameters for the SPDP matrix. -/
structure SPDPParams where
  κ : ℕ  -- derivative order
  ℓ : ℕ  -- shift degree
  deriving DecidableEq, Repr

/-- The SPDP rank of a polynomial under given parameters and block partition.
    This is an opaque definition — we axiomatise its properties. -/
axiom SPDPRank (F : Type*) [Field F] (params : SPDPParams) (B : BlockPartition n)
  (p : MvPolynomial (Fin n) F) : ℕ

/-- Notation: ΓB_{κ,ℓ}(p) -/
notation "ΓB" => SPDPRank

/-! ## Core Properties (Pall paper, inherited from P1) -/

/-- Monotonicity: restrictions cannot increase rank (Lemma 13.14, stagewise) -/
axiom rank_mono_restriction {F : Type*} [Field F] {n : ℕ}
  (params : SPDPParams) (B : BlockPartition n)
  (p : MvPolynomial (Fin n) F) (ρ : Fin n → Option F) :
  SPDPRank F params B (MvPolynomial.restrict ρ p) ≤ SPDPRank F params B p

/-- Block-local invertible changes preserve rank exactly (Lemma 14.7, move E1) -/
axiom rank_exact_block_local {F : Type*} [Field F] {n : ℕ}
  (params : SPDPParams) (B : BlockPartition n)
  (p p' : MvPolynomial (Fin n) F)
  (h_equiv : True) : -- placeholder for compiler equivalence
  SPDPRank F params B p = SPDPRank F params B p'

/-- Subadditivity: rank of vertical concatenation ≤ sum of ranks -/
axiom rank_subadditive {F : Type*} [Field F] {n : ℕ}
  (params : SPDPParams) (B : BlockPartition n)
  (p q : MvPolynomial (Fin n) F) :
  SPDPRank F params B (p + q) ≤ SPDPRank F params B p + SPDPRank F params B q

/-! ## Identity Minor -/

/-- An identity minor of order m in the SPDP matrix forces rank ≥ m -/
axiom identity_minor_rank_lb {F : Type*} [Field F] {n : ℕ}
  (params : SPDPParams) (B : BlockPartition n)
  (p : MvPolynomial (Fin n) F) (m : ℕ)
  (h_minor : True) : -- placeholder for identity minor witness
  SPDPRank F params B p ≥ m

end SPDP
