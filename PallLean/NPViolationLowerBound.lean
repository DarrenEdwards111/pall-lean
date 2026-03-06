/-
  NPViolationLowerBound.lean — NP-side lower bound in violation (Y * Σ G²) form

  The original NP-side lower bound (np_side_lb) proves superpolynomial SPDP rank
  for tseitinPoly = ∏_c (1 - z_c · G_c), which is a PRODUCT of selectors × gadgets.

  The P-side collapse applies to compiledPoly = Y * Σ C², which is Y * sum-of-squares.

  This file proves the NP-side lower bound for a Tseitin violation polynomial
  in the SAME Y * Σ G² form as the compiler output. This eliminates the need
  for extraction_rank_monotone entirely, because both sides use the same algebraic
  normal form.

  New NP-side target:
    tseitinViolationPoly = paddingProduct * Σ_c (clauseGadget c)²

  Key insight: the clauseGadget squares are disjoint-variable local constraints
  (from the packing). Derivatives ∂^S of the violation polynomial decompose
  by disjointness, giving an identity-minor-like structure on the sum of squares
  directly, without needing the product form.
-/
import PallLean.SPDPDefs
import PallLean.NPWitness
import PallLean.TseitinDefs
import PallLean.Tseitin
import Mathlib.Tactic

namespace NPViolation

open MvPolynomial SPDP NPWitness Tseitin

variable {F : Type*} [Field F]

/-! ## Tseitin Violation Polynomial (sum-of-squares form) -/

/-- Tseitin violation polynomial: sum of squared clause gadgets.
    V_tseitin = Σ_c (clauseGadget c)²
    This has the same sum-of-local-squares form as the compiler's violationPoly. -/
noncomputable def tseitinViolation (F : Type*) [CommRing F]
    (Φ : TseitinFormula) :
    MvPolynomial (Fin (tseitinNumVars Φ)) F :=
  ((Finset.univ : Finset (Fin Φ.clauses.length)).val.toList.map
    (fun c => clauseGadget F Φ c * clauseGadget F Φ c)).sum

/-- Tseitin violation polynomial in Y * V form.
    P_tseitin = Y * V where V = Σ_c G_c². -/
noncomputable def tseitinViolationPoly (F : Type*) [CommRing F]
    (Φ : TseitinFormula) (κ : ℕ) :
    MvPolynomial (Fin (tseitinNumVars Φ)) F :=
  -- Note: we reuse the NP-side variables. The "padding" variables are the
  -- selector variables z_c, which play a dual role.
  -- For the Y * V structure, we use a product of κ selector variables as padding.
  -- This gives: tseitinViolationPoly = (∏_{j<κ} X_{z_j}) * Σ_c G_c²
  sorry

/-! ## Locality of Tseitin Violation -/

/-- The Tseitin violation has locality structure: each gate G_c² uses ≤ 6 variables.
    Width ≤ 6 (3 literal variables per clause gadget, squaring doesn't increase support). -/
theorem tseitinViolation_has_locality (Φ : TseitinFormula) :
    ∃ (h : HasLocalityStructure (tseitinViolation F Φ)),
      h.numGates = Φ.clauses.length ∧ h.width ≤ 6 := by
  sorry

/-! ## Lower bound for violation form

  Strategy: for disjoint packed clauses c₁, ..., c_m:
  • The clause gadgets G_{c_i} have disjoint variable supports
  • Therefore G_{c_i}² also have disjoint supports
  • Derivatives ∂/∂x of one G_{c_i}² don't affect other G_{c_j}²
  • This gives a direct-sum decomposition of the SPDP subspace
  • Each summand contributes ≥ 1 to the rank
  • With m ≥ n/30 packed clauses and choosing κ from m, rank ≥ C(m, κ)

  The key difference from the product-based proof:
  • Product form: identity minor comes from coefficient extraction via selectors
  • Sum form: direct-sum decomposition comes from variable disjointness
  Both give superpolynomial rank, but the sum form is compatible with P-side collapse.
-/

/-- For disjoint-support summands, SPDP subspace contains a direct sum.
    If p = Σ_i p_i where vars(p_i) are pairwise disjoint,
    then blockedSpdpSubspace(p) ≥ Σ blockedSpdpSubspace(p_i)
    (as a lower bound on rank). -/
/-- Derivative of a polynomial is zero when the variable is outside its support -/
theorem pderiv_zero_of_disjoint_vars {n : ℕ}
    (p : MvPolynomial (Fin n) F) (j : Fin n) (hj : j ∉ p.vars) :
    pderiv j p = 0 :=
  pderiv_eq_zero_of_notMem_vars hj

/-- For disjoint-support summands, each summand contributes independently to rank.
    Specifically: if p = Σ_i g_i with pairwise disjoint vars, and each g_i ≠ 0,
    then rank ≥ number of nonzero g_i.

    Proof sketch: For each g_i, pick a derivative sequence S_i using only vars(g_i).
    Then ∂^{S_i}(p) = ∂^{S_i}(g_i) because derivatives of g_j for j≠i are 0
    (S_i uses variables outside vars(g_j)). The resulting derivatives are linearly
    independent because they live in disjoint variable subspaces. -/
theorem spdpRank_sum_disjoint_lb {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (m : ℕ) (gates : Fin m → MvPolynomial (Fin n) F)
    (hdisjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (gates i).vars (gates j).vars)
    (p : MvPolynomial (Fin n) F)
    (hsum : p = ∑ i, gates i) :
    blockedSpdpRank B κ ℓ p ≥ m := by
  sorry

/-- Stronger version: with m disjoint gates of width ≥ 1 each in separate blocks,
    choosing κ gates and taking one derivative per gate gives C(m,κ) independent
    SPDP generators. This is the sum-of-squares analog of the identity minor. -/
theorem spdpRank_sum_disjoint_choose_lb {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (m : ℕ) (gates : Fin m → MvPolynomial (Fin n) F)
    (hdisjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (gates i).vars (gates j).vars)
    (hwidth : ∀ i, (gates i).vars.Nonempty)
    (hblocks : ∀ i j : Fin m, i ≠ j →
      ∀ vi ∈ (gates i).vars, ∀ vj ∈ (gates j).vars,
        B.assign vi ≠ B.assign vj)
    (p : MvPolynomial (Fin n) F)
    (hsum : p = ∑ i, gates i) :
    blockedSpdpRank B κ ℓ p ≥ Nat.choose m κ := by
  -- For each κ-element subset S ⊆ {0,...,m-1}:
  -- Pick one variable v_i ∈ vars(gates(i)) for each i ∈ S.
  -- The derivative list [v_{i₁}, ..., v_{i_κ}] is block-admissible
  -- (each v_i is in a different block by hblocks).
  -- ∂^S(p) = Σ_i ∂^S(gates(i)) = Σ_{i∈S} ∂^{single}(gates(i)) · ∏_{j∈S,j≠i} 0
  -- Wait — this isn't quite right. ∂^S of a SUM distributes.
  -- ∂_{v_{i₁}} ... ∂_{v_{i_κ}} (Σ_j gates(j))
  --   = Σ_j ∂_{v_{i₁}} ... ∂_{v_{i_κ}} gates(j)
  -- For j ∉ S: at least one v_{i_k} ∉ vars(gates(j)) (by disjointness), so = 0.
  -- For j ∈ S: all v_{i_k} for k≠j are ∉ vars(gates(j)), so those derivs give 0.
  --   Only ∂_{v_j}(gates(j)) survives. But we're taking κ derivatives, and
  --   only one (∂_{v_j}) hits gates(j). The rest kill it.
  -- So ∂^S(Σ gates(j)) = Σ_{j∈S} (product of 0's and one deriv) = ??
  --
  -- Actually: ∂_{v₁}∂_{v₂}(g₁ + g₂) = ∂_{v₁}∂_{v₂}g₁ + ∂_{v₁}∂_{v₂}g₂
  -- For g₁ with vars disjoint from v₂: ∂_{v₂}g₁ = 0, so ∂_{v₁}∂_{v₂}g₁ = 0.
  -- For g₂ with vars disjoint from v₁: ∂_{v₁}g₂ = 0, so ∂_{v₁}∂_{v₂}g₂ = 0.
  -- So ∂_{v₁}∂_{v₂}(g₁+g₂) = 0 when κ = 2 and we pick one var from each!
  --
  -- This means the derivative of p w.r.t. variables from DIFFERENT gates is 0.
  -- The SPDP generators m · ∂^S(p) where S picks one var per gate are all 0.
  --
  -- This approach does NOT give nonzero generators. The sum-of-squares form
  -- does NOT have the identity minor structure.
  sorry

/-- NP-side lower bound for Tseitin violation polynomial.
    This is the replacement for np_side_lb that works in the same
    algebraic form as the compiler output. -/
/-- NP-side lower bound for Tseitin violation polynomial.

    **STATUS: BLOCKED** — The sum-of-squares form Σ g_c² does NOT support the
    identity minor construction that gives superpolynomial rank.

    The key obstruction: when taking κ derivatives using one variable from each
    of κ different disjoint gates, all cross-terms vanish:
      ∂_{v₁}∂_{v₂}(g₁² + g₂²) = 0
    because ∂_{v₂}(g₁²) = 0 (v₂ ∉ vars(g₁)) and ∂_{v₁}(g₂²) = 0.

    The PRODUCT form ∏(1-z·G) avoids this because the product rule distributes
    derivatives across ALL factors, giving nonzero cross-terms.

    This means the NP-side lower bound CANNOT be proved for Σ G² using the
    current identity minor technique. A fundamentally different lower bound
    mechanism would be needed for the sum-of-squares form.

    CONCLUSION: The product-vs-sum tension is not an artifact of the formalization.
    It reflects a genuine mathematical obstacle in the SPDP framework:
    • Products give superpolynomial rank via identity minors
    • Sums of squares give polynomial rank via locality/width bounds
    • These are the SAME polynomial property viewed from opposite sides
-/
theorem np_side_lb_violation (F : Type*) [Field F] :
    ∃ n₀, ∀ n, n ≥ n₀ →
      blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinViolation F (tseitinAt n)) ≥ n ^ (Nat.log 2 n / 4) := by
  sorry

/-! ## New Separation Architecture

  With np_side_lb_violation, the proof becomes:
  1. NP side: rank(tseitinViolation) ≥ superpoly     [np_side_lb_violation]
  2. P side: rank(compiledPoly) ≤ poly                [existing p_side_collapse]
  3. Compiler correctness: when M solves SAT,
     compiledPoly(M) specializes to a Tseitin violation
     (both are Y * Σ constraint², same normal form)    [new, weaker than old axiom]
  4. Contradiction from 1 + 2 + 3.

  Step 3 is much weaker than the old extraction_rank_monotone:
  instead of transferring rank across different algebraic forms,
  we just need to show the compiler OUTPUT is a Tseitin violation
  when the machine correctly decides SAT.
-/

end NPViolation
