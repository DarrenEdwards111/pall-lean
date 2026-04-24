/-
  PallLean/Paper93/Canonical/ProfileSubspaceStructure.lean

  Agent R8: structural simplification of the Cook-Levin profile subspace
  at a "mass 1 at τ, 0 elsewhere" histogram.

  Paper §9 Lemma 31 produces the profile subspace

      V_h  =  span { ∏_σ f σ | f σ ∈ Sym^{h σ}(W σ) } .

  For the ProfileMatches shape `bp.toHistogram τ = 1` and
  `bp.toHistogram τ' = 0` for all `τ' ≠ τ`, this reduces to

      V_h  =  Sym^1(W τ) ⊗ Sym^0(others)  =  W τ  .

  Consequently `row ∈ cookLevinProfileSubspace bp W` reduces to
  `row ∈ W τ = concreteW n hn4 σ τ`, which is a far simpler obligation.

  Kernel-only: no `sorry`, only `[propext, Classical.choice, Quot.sound]`.
-/
import PallLean.Paper93.CookLevinProfileSubspace
import PallLean.Paper93.Wiring.ConcreteW

namespace PallLean.Paper93.Canonical

open scoped BigOperators
open MvPolynomial
open PallLean PallLean.Paper93 PallLean.Paper93.Wiring
open PallLean.SymTensorPowerDim (symPower)
open SymmetricPowerBound (ConstraintType ProfileHistogram)
open WithinProfileBound (BoundedProfile)

/-! ## `symPower` at degenerate exponents

Two pointwise identities we need:

  * `symPower ℚ 0 W = Submodule.span ℚ {(1 : MvPolynomial _ ℚ)}`
    (the 0-fold product is the empty product `= 1`).
  * `symPower ℚ 1 W = W` as submodules
    (the 1-fold product `∏ i : Fin 1, f i = f 0`).

We prove them locally because the rest of the file depends on them. -/

private theorem symPower_zero_eq_span_one
    {n : ℕ} (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) :
    symPower ℚ 0 W = Submodule.span ℚ ({(1 : MvPolynomial (Fin n) ℚ)} : Set _) := by
  classical
  unfold symPower
  congr 1
  apply Set.eq_of_subset_of_subset
  · -- Every empty-product witness equals `1`.
    rintro p ⟨f, _, rfl⟩
    simp
  · -- Conversely, `1 = ∏ i : Fin 0, f i` for any `f`.
    intro p hp
    rcases hp with rfl
    refine ⟨(fun i => (0 : MvPolynomial (Fin n) ℚ)), ?_, ?_⟩
    · intro i; exact absurd i.isLt (by omega)
    · simp

private theorem symPower_one_eq
    {n : ℕ} (W : Submodule ℚ (MvPolynomial (Fin n) ℚ)) :
    symPower ℚ 1 W = W := by
  classical
  unfold symPower
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro p ⟨f, hf, rfl⟩
    -- `∏ i : Fin 1, f i = f 0 ∈ W`.
    have hprod : (∏ i : Fin 1, f i) = f 0 := by
      simp
    rw [hprod]
    exact hf 0
  · intro w hw
    refine Submodule.subset_span ?_
    refine ⟨fun _ => w, ?_, ?_⟩
    · intro i; exact hw
    · simp

/-! ## Structural simplification of `profileSubspace` at a `ProfileMatches`
histogram shape.

Given `h : ProfileHistogram` with `h τ = 1` and `h τ' = 0` for `τ' ≠ τ`,
`profileSubspace h W = W τ` as submodules. -/

/-- Reduce a product over `ConstraintType` to the factor at `τ` when all
other factors are constants times `1`. -/
private theorem prod_constraint_type_eq_factor_at
    {n : ℕ} (τ : ConstraintType)
    (f : ConstraintType → MvPolynomial (Fin n) ℚ)
    (c : ConstraintType → ℚ)
    (hother : ∀ σ, σ ≠ τ → f σ = (c σ) • (1 : MvPolynomial (Fin n) ℚ)) :
    (∏ σ : ConstraintType, f σ) =
      ((∏ σ ∈ (Finset.univ.erase τ), c σ) : ℚ) • f τ := by
  classical
  -- Split off the τ factor.
  have hsplit :
      (∏ σ : ConstraintType, f σ)
        = f τ * ∏ σ ∈ (Finset.univ.erase τ), f σ := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ConstraintType) f
          (Finset.mem_univ τ)]
  rw [hsplit]
  -- Rewrite each other factor as `c σ • 1`.
  have hprod_other :
      (∏ σ ∈ (Finset.univ.erase τ), f σ)
        = ((∏ σ ∈ (Finset.univ.erase τ), c σ)
              : ℚ) • (1 : MvPolynomial (Fin n) ℚ) := by
    have hcongr :
        (∏ σ ∈ (Finset.univ.erase τ), f σ)
          = ∏ σ ∈ (Finset.univ.erase τ),
                ((c σ) • (1 : MvPolynomial (Fin n) ℚ)) := by
      refine Finset.prod_congr rfl ?_
      intro σ hσ
      have hσne : σ ≠ τ := by
        have := Finset.mem_erase.mp hσ
        exact this.1
      exact hother σ hσne
    rw [hcongr]
    -- Now compute ∏_σ (c σ • 1) = (∏ c σ) • 1 for scalar-times-one products.
    induction (Finset.univ.erase τ) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, ih]
        -- Goal: (c a • 1) * ((∏ s) • 1) = ((c a * ∏ s)) • 1
        rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, map_mul]
        ring
  rw [hprod_other]
  -- f τ * (s • 1) = s • f τ
  rw [mul_comm, Algebra.smul_mul_assoc]
  congr 1
  simp

/-- The key structural lemma: if `h τ = 1` and `h τ' = 0` for all
`τ' ≠ τ`, then `profileSubspace h W = W τ`. -/
theorem profileSubspace_of_mass_one_eq
    {n : ℕ} (h : ProfileHistogram)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (τ : ConstraintType)
    (h1 : h τ = 1) (h0 : ∀ τ' : ConstraintType, τ' ≠ τ → h τ' = 0) :
    profileSubspace h W = W τ := by
  classical
  apply le_antisymm
  · -- ≤ direction: every spanning element is in `W τ`.
    unfold profileSubspace
    refine Submodule.span_le.mpr ?_
    rintro p ⟨f, hf, rfl⟩
    -- For σ = τ: `f τ ∈ symPower 1 (W τ) = W τ`.
    have hfτ : f τ ∈ W τ := by
      have : f τ ∈ symPower ℚ (h τ) (W τ) := hf τ
      rw [h1, symPower_one_eq] at this
      exact this
    -- For each σ ≠ τ: `f σ ∈ symPower 0 (W σ) = span {1}`.
    -- Hence `f σ = c σ • 1` for some `c σ : ℚ`.
    have hcσ : ∀ σ : ConstraintType, σ ≠ τ →
        ∃ c : ℚ, f σ = c • (1 : MvPolynomial (Fin n) ℚ) := by
      intro σ hσ
      have hfσ : f σ ∈ symPower ℚ (h σ) (W σ) := hf σ
      rw [h0 σ hσ, symPower_zero_eq_span_one] at hfσ
      -- `hfσ : f σ ∈ span {1}`; extract the scalar.
      rcases (Submodule.mem_span_singleton).mp hfσ with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← hc]
    -- Choose the scalars.
    choose! c hcEq using hcσ
    -- Rewrite the product and conclude.
    have hprod := prod_constraint_type_eq_factor_at τ f c hcEq
    rw [hprod]
    -- `(scalar) • f τ ∈ W τ` since `f τ ∈ W τ`.
    exact Submodule.smul_mem _ _ hfτ
  · -- ≥ direction: every `w ∈ W τ` is in `profileSubspace h W`.
    intro w hw
    -- Build `f : ConstraintType → MvPoly` with `f τ = w` and `f σ = 1` otherwise.
    refine Submodule.subset_span ?_
    refine ⟨fun σ => if σ = τ then w else 1, ?_, ?_⟩
    · intro σ
      by_cases hσ : σ = τ
      · subst hσ
        -- `if τ = τ then w else 1 = w`, in `symPower 1 (W τ) = W τ`.
        rw [h1, symPower_one_eq]
        simp only [if_true]
        exact hw
      · -- `if σ = τ then w else 1 = 1`, in `symPower 0 (W σ) = span {1}`.
        rw [h0 σ hσ, symPower_zero_eq_span_one]
        simp only [if_neg hσ]
        exact Submodule.subset_span (Set.mem_singleton _)
    · -- Product of `(if σ = τ then w else 1)` over all σ is `w`.
      have hprod_eq :
          (∏ σ : ConstraintType, (if σ = τ then w else (1 : MvPolynomial (Fin n) ℚ))) = w := by
        rw [Fintype.prod_eq_single τ]
        · simp
        · intro σ hσ
          simp [hσ]
      exact hprod_eq.symm

/-! ## Specialisation to `cookLevinProfileSubspace` at `concreteW`.

This is the deliverable for Agent R8. -/

/-- **Structural simplification at ProfileMatches shape.**

    Given a bounded profile `bp : BoundedProfile (Nat.log 2 n)` whose
    underlying histogram has mass `1` on a single constraint type `τ`
    and mass `0` elsewhere, the Cook-Levin profile subspace
    `cookLevinProfileSubspace bp concreteW` reduces to the single
    factor `concreteW n hn4 (Fin.castLEEmb hn4) τ`.

    This is the structural content behind
    `Sym^1(W τ) ⊗ Sym^0(others) = W τ`
    in the commutative polynomial realisation: every other factor is
    `Sym^0 = span {1}` = constants, and the single nontrivial factor
    is `Sym^1 = W τ`. Row-membership in the profile subspace thus
    collapses to row-membership in `concreteW n hn4 σ τ`. -/
theorem cookLevinProfileSubspace_at_mass_one_eq
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n)) (τ : ConstraintType)
    (h1 : bp.toHistogram τ = 1)
    (h0 : ∀ τ' : ConstraintType, τ' ≠ τ → bp.toHistogram τ' = 0) :
    PallLean.Paper93.cookLevinProfileSubspace (n := n) bp
        (fun τ' => PallLean.Paper93.Wiring.concreteW n hn4
          (Fin.castLEEmb hn4) τ')
      = PallLean.Paper93.Wiring.concreteW n hn4
          (Fin.castLEEmb hn4) τ := by
  -- Let `M` and `hn,htb,hns` be unused; the statement is purely about
  -- the profile subspace structure.
  let _ := M
  let _ := hn
  let _ := htb
  let _ := hns
  unfold PallLean.Paper93.cookLevinProfileSubspace
  exact profileSubspace_of_mass_one_eq (n := n) bp.toHistogram
    (fun τ' => PallLean.Paper93.Wiring.concreteW n hn4
      (Fin.castLEEmb hn4) τ') τ h1 h0

#print axioms cookLevinProfileSubspace_at_mass_one_eq

end PallLean.Paper93.Canonical
