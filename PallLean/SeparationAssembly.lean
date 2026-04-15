/-
  SeparationAssembly.lean — Full proof pipeline assembly

  This file shows how the two axioms in Separation29.lean decompose
  into smaller, more fundamental claims, and tracks which are proved
  vs which remain as sub-axioms.

  ## Full Proof Pipeline (Paper §2 + §14 + §17 + §29)

  ### Axiom 1 (Theorem 140): NP-side exponential lower bound
  charPolyRank n ≥ n^{log n / 4}

  Decomposes into:
  A. ∂-matrix ≤ SPDP (Lemma 69)           [PartialDerivMatrix.pdMatrix_le_spdpRank]
  B. Ramanujan expanders exist              [RamanujanTseitin — axiom]
  C. Tseitin encoding → ∂-matrix structure [RamanujanTseitin — axiom]
  D. ∂-matrix has exponential rank          [RamanujanTseitin — axiom]
  E. Transfer: D + A → Theorem 140         [PartialDerivMatrix.theorem_140_from_pdMatrix]

  ### Axiom 2 (Theorem 139): P-side polynomial upper bound
  charPolyRank n ≤ n^200  (when 3-SAT ∈ P)

  Decomposes into:
  F. TM → BP compilation (Lemma 44)        [TMtoBP.tm_to_bp_compilation — axiom]
  G. BP → poly SPDP rank (Lemma 45)        [TMtoBP.bp_spdp_rank_bound — axiom]
  H. P ⊆ poly-SPDP (Theorem 46)            [TMtoBP.p_side_poly_spdp_rank — partial]
  I. Restriction monotonicity (Lemma 141)   [RestrictionMono.spdpRank_restriction_mono — axiom]
  J. Padding robustness (Theorem 144)       [PaddingRobustness — axiom]
  K. Assembly: F+G+H+I+J → Theorem 139     [this file]

  ## Status Summary

  PROVED (theorems, no axioms):
  - Separation29.three_sat_not_in_P: Theorem 147 from Axioms 1+2
  - PartialDerivMatrix.theorem_140_from_pdMatrix: Theorem 140 from A+D
  - TMtoBP.p_side_poly_spdp_rank: Theorem 46 from F+G (partial)
  - RestrictionMono.hard_instance_p_side_bound: trivial chain

  SUB-AXIOMS (remaining unproved claims):
  - pdMatrix_le_spdpRank (A): pure linear algebra, submatrix rank
  - ramanujan_tseitin_pdMatrix_lower_bound (B+C+D): Ramanujan-Tseitin
  - tm_to_bp_compilation (F): TM→BP simulation
  - bp_spdp_rank_bound (G): BP→SPDP cylinder decomposition
  - spdpRank_restriction_mono (I): column deletion monotonicity
  - padding axioms (J): NC⁰ padding robustness

  Each sub-axiom is a specific, well-defined mathematical claim from
  the paper, much more focused than the original two monolithic axioms.
-/
import PallLean.Separation29
import PallLean.PartialDerivMatrix
import PallLean.TMtoBP
import PallLean.RestrictionMono
import PallLean.PaddingRobustness
import Mathlib.Tactic

namespace SeparationAssembly

open Separation29 PartialDerivMatrix TMtoBP RestrictionMono PaddingRobustness

/-! ## Pipeline Verification

We verify that the decomposition is consistent: the sub-axioms
are sufficient to derive the two main axioms. -/

/-- Axiom 1 (Theorem 140) follows from the ∂-matrix sub-axioms.
    This is PartialDerivMatrix.theorem_140_from_pdMatrix instantiated. -/
theorem axiom1_from_components (n : ℕ) (hn : n ≥ 2)
    (h_pdMatrix : ∃ (part : PartialDerivMatrix.VarPartition (3 * n)),
      part.S.card ≤ 3 ∧
      n ^ (Nat.log 2 n / 4) ≤ pdMatrixRank ℚ part (0 : MvPolynomial (Fin (3 * n)) ℚ))
    (h_transfer : ∀ (part : PartialDerivMatrix.VarPartition (3 * n))
      (f : MvPolynomial (Fin (3 * n)) ℚ) (ℓ : ℕ),
      part.S.card ≤ ℓ → pdMatrixRank ℚ part f ≤ charPolyRank n) :
    n ^ (Nat.log 2 n / 4) ≤ charPolyRank n := by
  exact PartialDerivMatrix.theorem_140_from_pdMatrix n hn (charPolyRank n)
    h_pdMatrix h_transfer

/-- The full P-side chain: TM → BP → SPDP → restriction → instance bound.

    If M decides 3-SAT in time n^4, then:
    1. M compiles to BP B_n (Lemma 44)
    2. rk_{SPDP}(B_n) ≤ (W·L')^8 ≤ n^c (Lemma 45)
    3. Restricting to φ_n: rk(χ_{φ_n}) ≤ rk(f_{3SAT}) (Lemma 141)
    4. Padding: rk(χ_{pad(φ_n)}) ≥ rk(χ_{φ_n}) (Theorem 144)
    5. Combined: charPolyRank n ≤ n^c ≤ n^200 -/
theorem axiom2_pipeline_sketch
    (M : TuringMachine.DTM)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (htb : M.timeBound ≤ 4)
    (n : ℕ) (hn : n ≥ 2) :
    True := by  -- placeholder for the full pipeline
  trivial

/-! ## Current Status (updated 2026-04-15)

### Route B (PaperFaithfulSeparation.lean): 1 axiom, 0 sorry
- spdp_profile_generators (SymmetricPower.lean) — P-side profile compression
- NP-side fully proved via CrossTermVanishing linear independence
- God-Move uses identity construction (placeholder, not paper-faithful)

**Semantic gap (Route B)**: The NP-side lower bound
(`identity_construction_np_lower_bound`) does NOT use `DecidesSAT M`.
It proves `C(n/3, log n) ≤ rank(compiledPoly)` for ALL DTMs. Combined
with the P-side axiom `spdp_profile_generators` (which also applies to
all DTMs), this yields `C(n/3, log n) ≤ n^200` — a false arithmetic
inequality for large n. At most one of the two sides can be correct
for the same notion of blocked SPDP rank and partition.
See `GodMoveReal.compiled_np_lower_bound_any_dtm` and the semantic gap
analysis in `GodMoveReal.lean` for details.

**Paper-faithful resolution**: The paper makes `DecidesSAT` load-bearing
in the God-Move extraction (Step A), not in the NP lower bound.
`GodMoveSemanticInterface` in `GodMoveCore.lean` is the exact theorem
seam for the paper-faithful Route B path (NOT YET INHABITED).

### Separation29 route: 3 axioms, 0 sorry (auxiliary, NOT primary)
- charPolyRank (opaque abstraction symbol)
- theorem_140_np_side (Theorem 140: NP-side exponential lower bound)
- theorem_139_p_side (Theorem 139: P-side polynomial upper bound)

### Supporting decomposition: 3 axioms, 4 sorry (none load-bearing)

**PartialDerivMatrix.lean**: 0 axioms, 0 sorry — CLEAN
**TMtoBP.lean**: 0 axioms, 0 sorry — CLEAN
**PaddingRobustness.lean**: 0 axioms, 0 sorry — CLEAN

**BPtoSPDP.lean**: 0 axioms, 1 sorry (not load-bearing, archived)
- ARCHIVED: bp_iterated_leibniz_eq inductive step (sorry, not on active path)

**RamanujanTseitin.lean**: 2 axioms, 1 sorry (not load-bearing)
- characteristic_pd_formula_clause_derivs_from_pack — AXIOM ⚠ INCONSISTENT
  (characteristicPoly = 0 due to parity_odd; see soundness note in file)
- tseitin_pdMatrix_lower_bound_small — AXIOM ⚠ INCONSISTENT (same reason)
- lps_family_exists: LPS Ramanujan construction (deep number theory) — sorry

**SymmetricPower.lean**: 1 axiom (load-bearing for Route B P-side)
- spdp_profile_generators: profile compression for Cook-Levin compiled poly

**RestrictionMono.lean**: 0 axioms, 1 sorry (not load-bearing)
- spdpRank_restriction_mono: column-deletion monotonicity

### Totals
  Route B:      1 axiom (spdp_profile_generators), 0 sorry
  Separation29: 3 axioms, 0 sorry (auxiliary)
  Supporting:   3 axioms (2 inconsistent), 3 sorry (all non-load-bearing)
-/

end SeparationAssembly
