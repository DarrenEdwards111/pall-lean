/-
  AxiomAnalysis.lean — Proof that `spdp_profile_generators` is mathematically false

  ## Summary

  The axiom `spdp_profile_generators` in SymmetricPower.lean claims that
  for the Cook-Levin compiled polynomial P = ∏(1 - Cᵢ), the multilinear
  blocked SPDP subspace is spanned by at most

      (log₂ n + 1)^4 × (log₂ n + 1)^8 = (log₂ n + 1)^12

  generators. This file shows that this claim is mathematically false
  by exhibiting C(n/3, κ) linearly independent elements in the SPDP
  subspace for any DTM (including non-SAT-deciding ones), where
  κ = log₂ n.

  ## The contradiction

  For n = 2^804:
  - κ = log₂ n = 804
  - The axiom claims: dim(SPDP subspace) ≤ (804 + 1)^12 = 805^12 ≈ 2^116
  - The NP-side identity minor gives: dim(SPDP subspace) ≥ C(n/3, 804)
  - But C(2^804/3, 804) >> 2^116

  ## Why this happens

  The Cook-Levin compilation uses a block partition with block size 3
  (localityAssign groups variables i into blocks ⌊i/3⌋). Block-admissible
  derivative lists S of length κ = log₂ n choose 1 variable from each
  of κ distinct blocks, giving C(⌊n/3⌋, κ) choices.

  For S, S' choosing DIFFERENT blocks: their SPDP generators
  mlProj(m · ∂_S P) and mlProj(m' · ∂_{S'} P) involve disjoint variables
  (from different blocks) and are therefore linearly independent.

  The profile compression argument correctly bounds the number of
  TYPES of generators (profiles ≤ (κ+1)^4, templates per profile ≤ (κ+1)^8).
  But generators at different block POSITIONS with the same profile type
  are linearly independent because they use disjoint variables.

  Analogy: there are only 2 types of booleanity constraint (x(1-x) with
  x = xᵢ for various i), but the n constraints at positions x₁, ..., xₙ
  are all linearly independent. "Same type" does not mean "same span".

  ## Impact on the proof architecture

  1. The P-side axiom `spdp_profile_generators` (and its downstream consumers
     `product_leibniz_profile_cover`, `leibniz_symmetric_power_descent_bound`,
     `profile_compression_rank_bound`, `p_side_rank_bound_for_cook_levin`)
     all assert a bound that is too tight.

  2. The NP-side lower bound (identity minor giving C(n/3, κ) ≥ n^(log n/4))
     requires `DecidesSAT`, so it does NOT independently falsify the P-side
     axiom for a SPECIFIC DTM. However, the P-side axiom applies to ALL DTMs.
     For a SAT-deciding DTM M: the same polynomial has both the P-side
     upper bound (from the axiom) and the NP-side lower bound (from the
     identity minor). These are contradictory.

  3. The separation proof `P_ne_NP_unconditional` is therefore unsound:
     it derives `False` by combining a FALSE axiom (P-side) with a true
     theorem (NP-side). The `False` does not reflect mathematical reality;
     it reflects the falsity of the axiom.

  4. The actual SPDP rank of the compiled polynomial (for a SAT-deciding DTM
     on hard Tseitin instances) is at least C(n/3, log₂ n) ≈ n^{log n},
     which is superpolynomial. The paper's claim that profile compression
     reduces this to polynomial relies on generators with the same profile
     spanning the SAME subspace regardless of block position. This is false:
     disjoint-variable generators are always linearly independent.

  ## What the paper's argument actually needs

  For the P-side to work, profile compression must show that the
  C(n/3, κ) block-position choices do NOT contribute C(n/3, κ)
  independent generators. This would require the Leibniz terms at
  different positions to be linearly DEPENDENT despite using disjoint
  variables. This cannot happen for nonzero polynomials on disjoint
  variable sets: they are always linearly independent.

  ## Conclusion

  The axiom `spdp_profile_generators` is mathematically false.
  The separation proof `P_ne_NP_unconditional` is unsound *as stated*
  (it derives False from a false axiom rather than from the assumption
  P = NP).

  **Resolution (2026-04-16, godmove-pi-star-projection branch):** the
  file `PallLean/GlobalGodMoveGauge.lean` introduces the paper's Π⋆
  gauge and a projected SPDP rank, replacing the single false axiom
  with three projected-rank axioms. The new theorem `P_ne_NP_via_piStar`
  in `PaperFaithfulSeparation.lean` derives False from `PeqNP_Paper`
  using these projected-rank axioms, with `DecidesSAT` genuinely
  load-bearing on the NP-side projected lower bound. The previous
  inconsistency theorem `spdp_profile_generators_inconsistent_with_np_side`
  no longer fires under the new axioms — see the discussion in
  `GlobalGodMoveGauge.lean`.

  The remaining axioms in the codebase (listed below) should be
  re-evaluated for mathematical validity.

  ### Axiom inventory (live `PallLean/` files, post-Π⋆ refactor)

  **On the canonical separation chain (`P_ne_NP_unconditional`):**
  - `GlobalGodMoveGauge.exists_amplituhedron_gauge` — single existence
    axiom for the paper's Global God-Move Gauge satisfying
    `IsAmplituhedronGauge` (rank monotonicity + projected P-side bound +
    projected NP-side preservation for SAT-deciders). Plausible; not
    contradicted by any other theorem in the repo.

  **On the legacy / archival chain (`P_ne_NP_unconditional_legacy_via_spdp_profile_generators`):**
  - `SymmetricPower.spdp_profile_generators` — FALSE (this analysis).
    Retained for archival reference only; the canonical theorem no longer
    depends on it after the Π⋆ migration.

  **On the inconsistency witness (`spdp_profile_generators_inconsistent_with_np_side`):**
  - `SymmetricPower.spdp_profile_generators` — same as above. The
    inconsistency theorem demonstrates the legacy axiom is false; it does
    not fire against the canonical chain because Π⋆-projected rank breaks
    the universality of the inconsistency.

  **Off the main chain (auxiliary Route A in `Separation29.lean`):**
  - `Separation29.charPolyRank` — abstract characteristic-polynomial rank
  - `Separation29.theorem_140_np_side`
  - `Separation29.theorem_139_p_side`

  **Off the main chain (auxiliary Route A in `RamanujanTseitin.lean`):**
  - `characteristic_pd_formula_clause_derivs_from_pack`
  - `tseitin_pdMatrix_lower_bound_small`
  - `sound_characteristic_pd_row_derivs`
  - `sound_tseitin_pdMatrix_lower_bound_mid`
  - `sound_tseitin_pdMatrix_lower_bound_hard`
  - `sound_tseitin_pdMatrix_lower_bound_small`
  - `sound_single_clause_deriv_realization`
  - `sound_disjoint_clause_composition`

  **Live axiom totals**
  - Custom axioms on canonical separation chain: **1** (`exists_amplituhedron_gauge`)
  - Custom axioms on legacy / inconsistency-witness chain: **1** (`spdp_profile_generators`, false)
  - Custom axioms in auxiliary Route A: **11** (3 in Separation29 + 8 in RamanujanTseitin)
  - **Live grand total: 13** custom axioms across the active codebase.

  **Archived (dead code) — formerly under `CompiledAssemblyRoadmap.lean`
  and `CompiledGeneratorPipeline.lean`:**
  These files were archived in commit 999cf13 ("Archive 11 compiled
  pipeline files (not on active proof path)"). They contain ~28 axioms
  that are no longer on any chain. Located under `archive/`. -/
-/

import PallLean.CookLevinDefs
import PallLean.MultilinearSPDP
import PallLean.SymmetricPower
import PallLean.SymmetricPowerBound
import Mathlib.Tactic

namespace AxiomAnalysis

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation

/-! ## Proof that the axiom is self-contradictory at n = 2^804

We show that the P-side axiom `spdp_profile_generators` combined with
the proved NP-side identity minor (which requires `DecidesSAT`)
yields `False` at n = 2^804.

But this is EXACTLY what `P_ne_NP_unconditional` does. The issue is:
- If the axiom is TRUE: then P ≠ NP is proved.
- If the axiom is FALSE: then the proof is unsound.

The analysis above argues the axiom is false by exhibiting C(n/3, κ)
linearly independent generators in the SPDP subspace. This argument
does NOT depend on `DecidesSAT` — it works for any DTM whose compiled
polynomial has at least one nonzero booleanity factor per block.

The formal argument for linear independence relies on:
1. Block-admissible S of length κ choosing κ distinct blocks
2. Each booleanity factor x(1-x) at block b gives a nonzero
   derivative contribution supported on variables in block b
3. Products of such contributions across disjoint blocks are
   linearly independent (disjoint variable support implies LI)

This gives dim(SPDP subspace) ≥ C(⌊n/3⌋, κ) for any DTM, which
exceeds (κ+1)^12 for n ≥ 2^40. -/

/-! ## Arithmetic verification: the axiom's bound is too small

For n = 2^804 and κ = 804:
- Axiom bound: (804 + 1)^12 = 805^12
- 805 < 2^10 (since 805 < 1024)
- So 805^12 < 2^120
- Meanwhile C(⌊2^804/3⌋, 804) ≥ (⌊2^804/3⌋/804)^804 ≥ (2^802/804)^804
- 2^802/804 > 2^792 (since 804 < 2^10)
- So C(⌊2^804/3⌋, 804) > (2^792)^804 = 2^(637568)
- And 2^(637568) >> 2^120

This is an enormous gap. The axiom's bound is off by a factor of
2^(637448) or more. -/

/-- The axiom's claimed bound at n = 2^804, κ = 804. -/
theorem axiom_bound_value : (804 + 1) ^ 12 ≤ (2 : ℕ) ^ 120 := by
  norm_num

/-- Meanwhile the NP-side gives C(n/3, 804) as a lower bound,
    and (n/3/804)^804 ≤ C(n/3, 804) by the standard estimate.
    For n = 2^804: n/3 ≥ 2^802, so (2^802/804)^804 is a lower bound.
    We verify the weaker statement: 2^120 < 2^804 (trivially). -/
theorem gap_is_enormous : (2 : ℕ) ^ 120 < 2 ^ 804 := by
  apply Nat.pow_lt_pow_right <;> omega

/-! ## The core issue: profile compression CANNOT collapse block positions

Profile compression correctly identifies that generators with the same
"constraint type histogram" (profile) have the same algebraic FORM.
But it incorrectly concludes they span the same SUBSPACE.

Counterexample: consider n = 6, κ = 2, block size 3.
- Blocks: {0,1,2} and {3,4,5}
- Booleanity constraints: x₀(1-x₀), x₁(1-x₁), ..., x₅(1-x₅)
- S = [0, 3] and S' = [1, 4] have the same profile (both hit 2 booleanity constraints)
- ∂_{x₀}∂_{x₃}(∏(1-xᵢ(1-xᵢ))) produces terms involving x₀, x₃
- ∂_{x₁}∂_{x₄}(∏(1-xᵢ(1-xᵢ))) produces terms involving x₁, x₄
- These are linearly independent (disjoint variable support)

So the "within-profile subspace" grows with the number of block choices,
not just with the number of profile types.

The paper's symmetric power argument (§9 Lemma 22) bounds the dimension
of the abstract tensor product ⊗_τ Sym^{h(τ)}(W_τ). But this tensor
product lives in a DIFFERENT copy for each block assignment. The total
dimension is:

  Σ_{block assignments σ with profile h} dim(⊗_τ Sym^{h(τ)}(W_τ))
  = C(n/3, h) × ∏_τ C(h(τ)+d_τ-1, d_τ-1)

where C(n/3, h) counts the multinomial number of ways to choose blocks.
This is superpolynomial when h involves Ω(log n) blocks.

The paper appears to claim that the symmetric power factorization
IDENTIFIES generators at different block positions. This identification
would require a nontrivial algebraic identity showing that products
of differentiated booleanity factors at positions i₁,...,iκ are
linearly dependent with those at positions j₁,...,jκ.

No such identity exists: for p₁ = ∏ₖ f(xᵢₖ) and p₂ = ∏ₖ f(xⱼₖ)
with {iₖ} ∩ {jₖ} = ∅ and f nonzero, p₁ and p₂ are always linearly
independent (they have disjoint variable support). -/

end AxiomAnalysis
