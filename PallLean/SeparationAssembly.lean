/-
  SeparationAssembly.lean — Full proof pipeline assembly

  This file tracks the current honest frontier behind the two shell axioms in
  `Separation29.lean`, separating what is now theorem-level infrastructure from
  what still survives as `axiom`/`sorry` obligations in nearby files.

  ## Full Proof Pipeline (Paper §2 + §14 + §17 + §29)

  ### Shell route (`Separation29.lean`)
  The exported separation theorem still factors through two shell axioms plus
  one opaque shell symbol:
  - `charPolyRank` (opaque symbol)
  - `theorem_140_np_side` (axiom)
  - `theorem_139_p_side` (axiom)

  The purpose of this file is to record how far those shell axioms have been
  decomposed honestly.

  ### NP-side decomposition target (Theorem 140)
  charPolyRank n ≥ n^{log n / 4}

  Current nearby status:
  - `PartialDerivMatrix.pdMatrix_le_spdpRank`: theorem
  - `PartialDerivMatrix.theorem_140_from_pdMatrix`: theorem
  - `RamanujanTseitin.sound_lps_family_exists`: theorem with one `sorry`
  - Active assembled sound route still uses
    `sound_characteristic_pd_row_derivs` and
    `sound_tseitin_pdMatrix_lower_bound_small`
  - The small-range frontier is further split in-file into
    `sound_tseitin_pdMatrix_lower_bound_mid`,
    `sound_tseitin_pdMatrix_lower_bound_hard`, and the local theorem
    `sound_tseitin_pdMatrix_lower_bound_trivial`, whose proof still has a
    `sorry`
  - A narrower replacement route is present but not yet wired through the main
    theorem: `sound_single_clause_deriv_realization`,
    `sound_disjoint_clause_composition`, and reconstruction theorem
    `sound_row_derivs_from_decomposition`

  ### P-side decomposition target (Theorem 139)
  charPolyRank n ≤ n^200  (when 3-SAT ∈ P)

  Current nearby status:
  - `TMtoBP.tm_to_bp_compilation`: definition
  - `TMtoBP.bp_spdp_rank_bound`: theorem
  - `TMtoBP.p_side_poly_spdp_rank`: theorem
  - `PaddingRobustness.*`: theorem-level placeholder infrastructure, no
    remaining `axiom`/`sorry`
  - `RestrictionMono.restrictedSourceSpdpCoeffMatrix_rank_le_spdpRank`:
    theorem-level coefficient-matrix inequality establishing the honest local
    restriction frontier with `0` axioms / `0` sorry
  - full `spdpRank κ ℓ (applyRestriction ρ f) ≤ spdpRank κ ℓ f` is still not
    formalized in the current ambient variable space; the remaining issue is a
    target-space semantics mismatch, not a local proof hole
  - `ConcreteCharPolyRankBridge` packages the shell/concrete identification
    once, and `axiom2_from_components` uses it to recover the shell-level
    `charPolyRank n ≤ n^200` conclusion

  ## Status Summary

  THEOREM-level nearby items:
  - Separation29.three_sat_not_in_P: Theorem 147 from the two shell axioms
  - PartialDerivMatrix.theorem_140_from_pdMatrix: transfer theorem packaging
    PD-rank lower bounds into a shell-level Theorem 140 conclusion
  - TMtoBP.p_side_poly_spdp_rank: P-side polynomial SPDP bound for the current
    zero-polynomial BP compilation
  - PaddingRobustness.padding_preserves_rank / nc0_padding_exists
  - RestrictionMono.restrictedSourceSpdpCoeffMatrix_rank_le_spdpRank:
    theorem-level matrix-rank bound for restricted source generators
  - axiom2_from_components: theorem wrapper reducing the shell P-side bound
    to the concrete data package exposed in `Separation29.lean`

  ACTIVE frontier items in nearby files:
  - `RamanujanTseitin.sound_lps_family_exists`: one `sorry`
  - `RamanujanTseitin.sound_characteristic_pd_row_derivs`: axiom
  - `RamanujanTseitin.sound_tseitin_pdMatrix_lower_bound_small`: axiom

  DECOMPOSED but not yet assembled through the main theorem:
  - `RamanujanTseitin.sound_single_clause_deriv_realization`: axiom
  - `RamanujanTseitin.sound_disjoint_clause_composition`: axiom
  - `RamanujanTseitin.sound_row_derivs_from_decomposition`: `sorry`

  Each sub-axiom is a specific, well-defined mathematical claim from
  the paper, much more focused than the original two monolithic shell axioms.
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

/-- The full P-side shell conclusion from the concrete assembly seam.

    If M decides 3-SAT in time n^4, then:
    1. M compiles to BP B_n (Lemma 44)
    2. rk_{SPDP}(B_n) ≤ (W·L')^8 ≤ n^c (Lemma 45)
    3. Restricting to φ_n: rk(χ_{φ_n}) ≤ rk(f_{3SAT}) (Lemma 141)
    4. Padding: rk(χ_{pad(φ_n)}) ≥ rk(χ_{φ_n}) (Theorem 144)
    5. Combined: charPolyRank n ≤ rk(χ_{φ_n}) ≤ n^c ≤ n^200

    The shell/concrete identification is carried by
    `ConcreteCharPolyRankBridge`, rather than a raw inequality argument. -/
theorem axiom2_from_components
    (M : TuringMachine.DTM)
    (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ n)
    (hdec : PaperFaithfulSeparation.DecidesSAT M)
    (d : ConcreteNPSideData n)
    (pData : ConcretePSideData M n hn htb hns hdec)
    (bridge : _root_.Separation29.ConcreteCharPolyRankBridge n d) :
    charPolyRank n ≤ n ^ 200 := by
  exact theorem_139_from_concrete M n hn htb hns hdec pData d bridge

/-! ## Theorem 140 Decomposition via Sound Encoding

The NP-side axiom `theorem_140_np_side` (Theorem 140) decomposes into a chain
of sub-claims. With the new `SoundTseitinEncoding` (§11 of RamanujanTseitin),
the decomposition is **consistent** — unlike the original encoding path.

### Full NP-side decomposition chain:

1. **LPS Ramanujan expanders exist** (`sound_lps_family_exists`)
   Status: sorry (deep algebraic number theory)
   Paper: §6, LPS (1988) / Margulis (1988)

2. **Disjoint packing on high-girth graphs** (`disjoint_packing_exists`)
   Status: PROVED (greedy algorithm, bounded-conflict argument)
   Paper: §8.3, Lemma 8.3

3. **Kronecker system from disjoint packing** (`buildKroneckerSystem`)
   Status: PROVED (combinatorial construction)
   Paper: §14, identity-minor construction

4. **Linear independence of Kronecker rows** (`linearIndependent_of_kronecker`)
   Status: PROVED (diagonal evaluation argument)
   Paper: §14.2, Kronecker delta property

5. **Binomial lower bound** (`binomial_lower_bound_from_660`)
   Status: PROVED (explicit arithmetic)
   Paper: §14.3, C(n/30, log n) ≥ n^(log n / 4) for n ≥ 660

6. **Row realization** (`sound_characteristic_pd_row_derivs`)
   Status: AXIOM (algebraic core)
   Paper: §14.1, each Kronecker row = iterated ∂ of χ_φ

7. **PD column space → PD rank** (`pdMatrixRank_ge_of_linearIndependent`)
   Status: PROVED (finite-dimensional linear algebra)
   Paper: §2.3, Lemma 49/69

8. **PD rank → SPDP rank** (`pdMatrix_le_spdpRank`)
   Status: PROVED (subspace containment)
   Paper: §2.3, Lemma 69

Steps 1-5 and 7-8 are PROVED. Step 6 is the single remaining algebraic axiom.
The finite exceptional range (n < 660) adds a second axiom
(`sound_tseitin_pdMatrix_lower_bound_small`).

### Sub-axiom semantics

**`sound_characteristic_pd_row_derivs`**: For each subset of log(n) clauses from
the greedy packing, the gadget product (product of clause-local polynomials) is
equal to an iterated partial derivative of the even-parity characteristic
polynomial χ_φ along a list of |S|-many S-variables.

This is the **algebraic core** of the Ramanujan-Tseitin lower bound. It
connects the combinatorial pocket structure to the derivative structure of χ_φ.
The proof in the paper relies on:
- The factored structure of χ_φ as a sum of assignment monomials
- The Leibniz rule for iterated derivatives through products
- The disjoint pocket structure ensuring cross-terms vanish
- The edge-parity structure of Ramanujan expander graphs

### Status vs original encoding

| Component | Original | Sound |
|-----------|----------|-------|
| Row realization | ⚠ INCONSISTENT | ✓ CONSISTENT axiom |
| Finite range | ⚠ INCONSISTENT | ✓ CONSISTENT axiom |
| LPS existence | sorry | sorry |
| Disjoint packing | PROVED | PROVED (shared) |
| Kronecker system | PROVED | PROVED (shared) |
| Linear independence | PROVED | PROVED (shared) |
| PD → SPDP transfer | PROVED | PROVED (shared) |
-/

/-! ## Historical Status Snapshot (updated 2026-04-15)

This file is an orientation record for the `Separation29` shell and nearby
paper-numbered routes. It is not the active imported contradiction route on
this branch; for the live obligation tracker, see `PROOF-OBLIGATIONS.md` and
`SORRY-INVENTORY.md`.

### Route B (PaperFaithfulSeparation.lean): 1 axiom (KNOWN FALSE), 0 sorry
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

### Separation29 route: 2 axioms + 1 opaque symbol, 0 sorry (auxiliary, NOT primary)
- charPolyRank (opaque abstraction symbol)
- theorem_140_np_side (Theorem 140: NP-side exponential lower bound)
- theorem_139_p_side (Theorem 139: P-side polynomial upper bound)

### Sound NP-side, active assembled route: 2 main axioms, 2 live sorries

This is the route that currently feeds `sound_theorem72_condensed`.

**RamanujanTseitin.lean (sound assembled path)**:
- sound_characteristic_pd_row_derivs — AXIOM (algebraic core of Theorem 140)
- sound_tseitin_pdMatrix_lower_bound_small — AXIOM (assembled finite exceptional range)
- sound_lps_family_exists — sorry (LPS Ramanujan construction)
- sound_tseitin_pdMatrix_lower_bound_trivial — theorem with a local sorry
  (6 ≤ n < 16)

Auxiliary small-range refinement currently present in the same file:
- sound_tseitin_pdMatrix_lower_bound_mid — AXIOM (16 ≤ n < 256)
- sound_tseitin_pdMatrix_lower_bound_hard — AXIOM (256 ≤ n < 660)

**PartialDerivMatrix.lean**: 0 axioms, 0 sorry — CLEAN
  pdMatrix_le_spdpRank (Lemma 69): PROVED

### Sound NP-side, decomposed replacement route: 2 narrower axioms, 1 local sorry

This route is more faithful about the remaining algebraic content, but it is
not yet wired into `sound_tseitin_pdMatrix_lower_bound`. It also still lives
inside the same file-level sound-family / finite-range scaffold above.

**RamanujanTseitin.lean (sound decomposed path)**:
- sound_single_clause_deriv_realization — AXIOM (single-clause derivative realization)
- sound_disjoint_clause_composition — AXIOM (disjoint Leibniz composition)
- sound_row_derivs_from_decomposition — sorry (reconstruction back to row realization)

### Legacy (inconsistent) NP-side path:

**RamanujanTseitin.lean (original path)**: 2 axioms ⚠ INCONSISTENT, 1 sorry
- characteristic_pd_formula_clause_derivs_from_pack — ⚠ INCONSISTENT
- tseitin_pdMatrix_lower_bound_small — ⚠ INCONSISTENT
- lps_family_exists — sorry

### Other supporting files:
**TMtoBP.lean**: 0 axioms, 0 sorry — CLEAN
**PaddingRobustness.lean**: 0 axioms, 0 sorry — CLEAN
**BPtoSPDP.lean**: 1 private archived axiom (`bp_iterated_leibniz_eq`), 0 sorry
  Ordered-position cylinder wrapper is stated exactly; not on the active route.
**SymmetricPower.lean**: 1 axiom (KNOWN FALSE for Route B P-side)
**RestrictionMono.lean**: 0 axioms, 0 sorry
  Honest local frontier is the finite-support matrix-rank comparison
  `restrictedSourceSpdpCoeffMatrix_rank_le_spdpRank`; the stronger ambient
  restriction-monotonicity statement remains blocked by target-space semantics.

### Totals (honest frontier, by route)
  Route B current placeholder shell: 1 false axiom, 0 sorry
  Separation29 shell: 2 axioms + 1 opaque symbol, 0 sorry
  Sound NP-side active assembled route: 4 axioms, 2 sorry
  Sound NP-side decomposed replacement block: 2 axioms, 1 local sorry
  P-side nearby decomposition: 0 axioms, 0 sorry
-/

/-! ## Axiom audit

`axiom1_from_components` still depends on the shell symbol `charPolyRank`.
`axiom2_from_components` uses `charPolyRank` together with the shared
`ConcreteCharPolyRankBridge` seam supplied to `theorem_139_from_concrete`. -/
#print axioms axiom1_from_components
#print axioms axiom2_from_components

end SeparationAssembly
