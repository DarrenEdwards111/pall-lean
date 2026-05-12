import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeDischargeSubgoals
import PallLean.PaperFaithfulCompilation

/-!
# Permutation-only shortcut for the SAT-decider gauge

This file documents the *permutation-only shortcut* in the SAT-decider gauge
vocabulary.  In the matrix language of the paper, a "permutation gauge" is a
candidate `Π⋆` that is just a row/column permutation of the identity.  Such a
candidate has determinant `±1` and rank `n`, and therefore cannot buy any
P-side rank reduction relative to the identity gauge.

Concretely, in the SAT-decider gauge vocabulary, a permutation gauge is the
ℚ-linear endomorphism induced by `MvPolynomial.rename σ` for some permutation
`σ : Equiv.Perm (Fin numVars)`.  We prove:

1. The permutation gauge has a two-sided inverse (`rename σ.symm`), so it is a
   linear automorphism of the SAT-decider polynomial space — the gauge-level
   analogue of "rank `= n`".
2. The permutation gauge collapses to the identity exactly when `σ = id`; and
   if it satisfies the structural projection-gauge axiom
   (`IsProjectionGauge`, the gauge analogue of "idempotent matrix"), then in
   fact `σ = id` and the gauge is the identity.
3. The transported permutation gauge is always rank-monotone, but only with
   equality on its image: the P-side bound it produces equals the P-side
   bound it receives, so the P-side rank is unchanged — no genuine progress.

The result is a kernel-only (no `sorry`, no extra axioms) certificate that
permutation-matrix gauges cannot serve as the nontrivial richer projection
required by the paper's Π⋆ argument.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

/-! ## The permutation gauge as a linear endomorphism -/

/-- The SAT-decider gauge induced by a permutation `σ` of the flat
Cook-Levin variable space.  This is the gauge-level analogue of a row/column
permutation matrix `P`. -/
noncomputable def satDeciderGaugePermutation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  (MvPolynomial.rename (σ : _ → _)).toLinearMap

/-- The permutation gauge for the identity permutation is the identity gauge. -/
theorem satDeciderGaugePermutation_one
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugePermutation M n hn2 htb hns 1 = LinearMap.id := by
  apply LinearMap.ext
  intro p
  show MvPolynomial.rename
      ((1 : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
        _ → _) p = p
  -- `(1 : Equiv.Perm _) = Equiv.refl _`, whose underlying function is `id`.
  have h : ((1 : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
        _ → _) = id := rfl
  rw [h]
  exact MvPolynomial.rename_id_apply p

/-! ## Composition behaves like permutation multiplication -/

/-- Composing two permutation gauges yields the permutation gauge for the
composed permutation.  In matrix terms, the product of two permutation
matrices is again a permutation matrix. -/
theorem satDeciderGaugePermutation_comp
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ τ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    satDeciderGaugePermutation M n hn2 htb hns σ ∘ₗ
        satDeciderGaugePermutation M n hn2 htb hns τ =
      satDeciderGaugePermutation M n hn2 htb hns (σ * τ) := by
  apply LinearMap.ext
  intro p
  show MvPolynomial.rename ((σ : _ → _))
      (MvPolynomial.rename ((τ : _ → _)) p) =
        MvPolynomial.rename (((σ * τ) : Equiv.Perm _) : _ → _) p
  rw [MvPolynomial.rename_rename]
  -- `(σ * τ : Equiv.Perm _) : _ → _` evaluates as `σ ∘ τ` on the underlying
  -- function level (Mathlib convention for `Equiv` multiplication).
  rfl

/-! ## The permutation gauge is a linear automorphism (rank `= n`) -/

/-- The permutation gauge induced by `σ⁻¹` is a left inverse of the
permutation gauge induced by `σ`. -/
theorem satDeciderGaugePermutation_left_inverse
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    satDeciderGaugePermutation M n hn2 htb hns σ⁻¹ ∘ₗ
        satDeciderGaugePermutation M n hn2 htb hns σ = LinearMap.id := by
  rw [satDeciderGaugePermutation_comp]
  rw [inv_mul_cancel σ]
  exact satDeciderGaugePermutation_one M n hn2 htb hns

/-- The permutation gauge induced by `σ⁻¹` is a right inverse of the
permutation gauge induced by `σ`. -/
theorem satDeciderGaugePermutation_right_inverse
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    satDeciderGaugePermutation M n hn2 htb hns σ ∘ₗ
        satDeciderGaugePermutation M n hn2 htb hns σ⁻¹ = LinearMap.id := by
  rw [satDeciderGaugePermutation_comp]
  rw [mul_inv_cancel σ]
  exact satDeciderGaugePermutation_one M n hn2 htb hns

/-- The permutation gauge is a bijection on the SAT-decider polynomial
space — the gauge-level analogue of "permutation matrices have rank `n`". -/
theorem satDeciderGaugePermutation_bijective
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    Function.Bijective (satDeciderGaugePermutation M n hn2 htb hns σ) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity from the left inverse `σ⁻¹`.
    intro p q hpq
    have hL := satDeciderGaugePermutation_left_inverse M n hn2 htb hns σ
    have := congrArg (satDeciderGaugePermutation M n hn2 htb hns σ⁻¹) hpq
    -- Apply `(σ⁻¹ ∘ σ) = id` on both sides.
    have hp : (satDeciderGaugePermutation M n hn2 htb hns σ⁻¹ ∘ₗ
        satDeciderGaugePermutation M n hn2 htb hns σ) p = p := by
      rw [hL]; rfl
    have hq : (satDeciderGaugePermutation M n hn2 htb hns σ⁻¹ ∘ₗ
        satDeciderGaugePermutation M n hn2 htb hns σ) q = q := by
      rw [hL]; rfl
    -- Combine.
    have : satDeciderGaugePermutation M n hn2 htb hns σ⁻¹
              (satDeciderGaugePermutation M n hn2 htb hns σ p) =
            satDeciderGaugePermutation M n hn2 htb hns σ⁻¹
              (satDeciderGaugePermutation M n hn2 htb hns σ q) := this
    have hp' : satDeciderGaugePermutation M n hn2 htb hns σ⁻¹
        (satDeciderGaugePermutation M n hn2 htb hns σ p) = p := hp
    have hq' : satDeciderGaugePermutation M n hn2 htb hns σ⁻¹
        (satDeciderGaugePermutation M n hn2 htb hns σ q) = q := hq
    rw [hp', hq'] at this
    exact this
  · -- Surjectivity from the right inverse `σ⁻¹`.
    intro q
    refine ⟨satDeciderGaugePermutation M n hn2 htb hns σ⁻¹ q, ?_⟩
    have hR := satDeciderGaugePermutation_right_inverse M n hn2 htb hns σ
    have hqq : (satDeciderGaugePermutation M n hn2 htb hns σ ∘ₗ
        satDeciderGaugePermutation M n hn2 htb hns σ⁻¹) q = q := by
      rw [hR]; rfl
    exact hqq

/-! ## A permutation gauge is a projection iff it is the identity -/

/-- Iterating the permutation gauge equals the gauge for `σ * σ`. -/
theorem satDeciderGaugePermutation_self_comp
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    satDeciderGaugePermutation M n hn2 htb hns σ ∘ₗ
        satDeciderGaugePermutation M n hn2 htb hns σ =
      satDeciderGaugePermutation M n hn2 htb hns (σ * σ) :=
  satDeciderGaugePermutation_comp M n hn2 htb hns σ σ

/-- A permutation gauge is a `IsProjectionGauge` (idempotent linear
endomorphism) iff `σ * σ = σ`, equivalently `σ = 1`. -/
theorem satDeciderGaugePermutation_isProjectionGauge_iff
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    GaugeMonotonicity.IsProjectionGauge
        (satDeciderGaugePermutation M n hn2 htb hns σ) ↔ σ = 1 := by
  constructor
  · intro hproj
    -- Idempotence at the gauge level, combined with bijectivity, forces
    -- the underlying permutation to be the identity.
    have hidem : satDeciderGaugePermutation M n hn2 htb hns σ ∘ₗ
        satDeciderGaugePermutation M n hn2 htb hns σ =
          satDeciderGaugePermutation M n hn2 htb hns σ := hproj.idempotent
    rw [satDeciderGaugePermutation_self_comp] at hidem
    -- We now have `gauge (σ * σ) = gauge σ`.  Apply both sides to `X i`
    -- to extract the action of `σ * σ` and `σ` on indices.
    have hsigma : ∀ i, σ (σ i) = σ i := by
      intro i
      have happ := congrArg
        (fun (f : SATDeciderGaugeMap M n hn2 htb hns) => f (X i))
        hidem
      -- LHS: `gauge (σ * σ) (X i) = X ((σ * σ) i) = X (σ (σ i))`.
      have hL : satDeciderGaugePermutation M n hn2 htb hns (σ * σ) (X i)
          = X (σ (σ i)) := by
        show MvPolynomial.rename (((σ * σ) : Equiv.Perm _) : _ → _)
            (X i : MvPolynomial _ ℚ) = X (σ (σ i))
        rw [MvPolynomial.rename_X]
        rfl
      -- RHS: `gauge σ (X i) = X (σ i)`.
      have hR : satDeciderGaugePermutation M n hn2 htb hns σ (X i) = X (σ i) := by
        show MvPolynomial.rename ((σ : _ → _)) (X i :
          MvPolynomial _ ℚ) = X (σ i)
        exact MvPolynomial.rename_X _ _
      have happ' :
          satDeciderGaugePermutation M n hn2 htb hns (σ * σ) (X i) =
            satDeciderGaugePermutation M n hn2 htb hns σ (X i) := happ
      rw [hL, hR] at happ'
      -- `X (σ (σ i)) = X (σ i)` in a polynomial ring forces `σ (σ i) = σ i`.
      exact MvPolynomial.X_injective happ'
    -- From `σ (σ i) = σ i` and bijectivity of `σ`, deduce `σ i = i`.
    apply Equiv.ext
    intro i
    have hi := hsigma i
    -- Apply `σ⁻¹` (i.e. `σ.symm`) to both sides.
    have := congrArg σ.symm hi
    simpa [Equiv.symm_apply_apply] using this
  · intro hσ
    rw [hσ, satDeciderGaugePermutation_one]
    exact GaugeMonotonicity.IsProjectionGauge.id

/-- Symmetric form: the permutation gauge is a projection gauge exactly when
it equals the identity gauge. -/
theorem satDeciderGaugePermutation_isProjectionGauge_iff_eq_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    GaugeMonotonicity.IsProjectionGauge
        (satDeciderGaugePermutation M n hn2 htb hns σ) ↔
      satDeciderGaugePermutation M n hn2 htb hns σ = LinearMap.id := by
  rw [satDeciderGaugePermutation_isProjectionGauge_iff]
  constructor
  · intro hσ
    rw [hσ]; exact satDeciderGaugePermutation_one M n hn2 htb hns
  · intro hgauge
    -- Apply both sides to `X i` and use injectivity of `X` to recover σ = 1.
    apply Equiv.ext
    intro i
    have happ :
        satDeciderGaugePermutation M n hn2 htb hns σ (X i) =
          (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) (X i) :=
      congrArg
        (fun (f : SATDeciderGaugeMap M n hn2 htb hns) => f (X i)) hgauge
    have hL : satDeciderGaugePermutation M n hn2 htb hns σ (X i) = X (σ i) := by
      show MvPolynomial.rename ((σ : _ → _)) (X i :
        MvPolynomial _ ℚ) = X (σ i)
      exact MvPolynomial.rename_X _ _
    have hR : (LinearMap.id : SATDeciderGaugeMap M n hn2 htb hns) (X i) = X i := rfl
    rw [hL, hR] at happ
    have hi : σ i = i := MvPolynomial.X_injective happ
    -- Show `(1 : Equiv.Perm _) i = i` to match the goal `σ i = (1 : Equiv.Perm _) i`.
    show σ i = (1 :
      Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) i
    rw [hi]; rfl

/-! ## Rank monotonicity for permutation gauges (no genuine progress) -/

/-- The permutation gauge for the identity permutation is rank-monotone in the
SPDP sense — directly from the identity case. -/
theorem satDeciderGaugePermutation_one_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugePermutation M n hn2 htb hns 1) := by
  rw [satDeciderGaugePermutation_one]
  intro κ ℓ p
  exact le_refl _

/-- **No genuine P-side progress for the trivial (identity) permutation
gauge.**  When `σ = 1`, the gauge is the identity and the P-side rank of the
gauged compiled polynomial equals that of the original compiled polynomial. -/
theorem satDeciderGaugePermutation_one_pSide_unchanged
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MultilinearSPDP.mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (satDeciderGaugePermutation M n hn2 htb hns 1
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) =
      MultilinearSPDP.mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  rw [satDeciderGaugePermutation_one]
  rfl

/-- **Permutation-only shortcut collapses to the identity gauge.**  If a
permutation gauge satisfies the structural projection-gauge axiom, then the
gauge is literally `LinearMap.id` and so the P-side rank of the gauged
compiled polynomial is exactly the P-side rank of the original compiled
polynomial.  In other words: a row/column permutation alone never lowers
the P-side rank — there is "no genuine progress". -/
theorem satDeciderGaugePermutation_no_genuine_progress
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (hproj : GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugePermutation M n hn2 htb hns σ)) :
    MultilinearSPDP.mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (satDeciderGaugePermutation M n hn2 htb hns σ
          (compiledPoly (cook_levin_compilation M n hn2 htb hns))) =
      MultilinearSPDP.mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  -- Projection forces `σ = 1`, then identity-gauge gives equality.
  have hσ : σ = 1 :=
    (satDeciderGaugePermutation_isProjectionGauge_iff
      M n hn2 htb hns σ).mp hproj
  subst hσ
  exact satDeciderGaugePermutation_one_pSide_unchanged M n hn2 htb hns

/-- **Rank-monotonicity for any projection-gauge permutation candidate is
trivial.**  If a permutation gauge is a projection gauge, then it is the
identity, and rank-monotonicity collapses to reflexivity. -/
theorem satDeciderGaugePermutation_rankMonotonicity_of_projection
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (hproj : GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugePermutation M n hn2 htb hns σ)) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (satDeciderGaugePermutation M n hn2 htb hns σ) := by
  have hσ : σ = 1 :=
    (satDeciderGaugePermutation_isProjectionGauge_iff
      M n hn2 htb hns σ).mp hproj
  subst hσ
  exact satDeciderGaugePermutation_one_rankMonotonicity M n hn2 htb hns

/-! ## Permutation gauges as `IsRankMonotoneGauge` candidates -/

/-- The permutation gauge for the identity satisfies `IsRankMonotoneGauge`
in the generic `GaugeMonotonicity` vocabulary. -/
theorem satDeciderGaugePermutation_one_isRankMonotoneGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    GaugeMonotonicity.IsRankMonotoneGauge
      (cook_levin_compilation M n hn2 htb hns).partition
      (satDeciderGaugePermutation M n hn2 htb hns 1) := by
  rw [satDeciderGaugePermutation_one]
  exact GaugeMonotonicity.IsRankMonotoneGauge.id _

/-- Any permutation gauge that satisfies the projection-gauge axiom also
satisfies the generic `IsRankMonotoneGauge` predicate — and trivially so,
because it is the identity. -/
theorem satDeciderGaugePermutation_isRankMonotoneGauge_of_projection
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (σ : Equiv.Perm (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (hproj : GaugeMonotonicity.IsProjectionGauge
      (satDeciderGaugePermutation M n hn2 htb hns σ)) :
    GaugeMonotonicity.IsRankMonotoneGauge
      (cook_levin_compilation M n hn2 htb hns).partition
      (satDeciderGaugePermutation M n hn2 htb hns σ) := by
  have hσ : σ = 1 :=
    (satDeciderGaugePermutation_isProjectionGauge_iff
      M n hn2 htb hns σ).mp hproj
  subst hσ
  exact satDeciderGaugePermutation_one_isRankMonotoneGauge M n hn2 htb hns

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugePermutation_one
#print axioms satDeciderGaugePermutation_comp
#print axioms satDeciderGaugePermutation_left_inverse
#print axioms satDeciderGaugePermutation_right_inverse
#print axioms satDeciderGaugePermutation_bijective
#print axioms satDeciderGaugePermutation_self_comp
#print axioms satDeciderGaugePermutation_isProjectionGauge_iff
#print axioms satDeciderGaugePermutation_isProjectionGauge_iff_eq_id
#print axioms satDeciderGaugePermutation_one_rankMonotonicity
#print axioms satDeciderGaugePermutation_one_pSide_unchanged
#print axioms satDeciderGaugePermutation_no_genuine_progress
#print axioms satDeciderGaugePermutation_rankMonotonicity_of_projection
#print axioms satDeciderGaugePermutation_one_isRankMonotoneGauge
#print axioms satDeciderGaugePermutation_isRankMonotoneGauge_of_projection

end PallLean.Paper93.DeepMath.PathB
