import PallLean.CookLevinDefs
import PallLean.CompiledBoolFactorBridge
import PallLean.SymmetricPower
import PallLean.Paper93.Paper283.BridgeACookLevinLocalQvCandidate
import PallLean.Paper93.Paper283.ListProdDerivativeConstantCoeff

/-!
# Bridge A: derivative of `cookLevinLocalBlockQ` does not vanish at the origin

This file closes the load-bearing anti-cancellation step for Bridge A at
`κ = 1`.  Concretely we prove

```
MvPolynomial.coeff 0
    (MvPolynomial.pderiv v (cookLevinLocalBlockQ M n hn htb hns
        ((cook_levin_compilation M n hn htb hns).partition.assign v))) ≠ 0
```

i.e. the constant term of the partial derivative of the real
compiler-local block polynomial at the all-zero assignment is nonzero.

Strategy.  At `X = 0`, every constraint factor `1 - c.poly` has constant
term `1` (booleanity, adjacency, and transition-skeleton constraints all
have polynomials with vanishing constant term).  Differentiating the
list product gives a sum of constant coefficients of derivatives of the
individual factors.  All these summands lie in `{0, -1}`:

* For the booleanity factor `1 - X_v(1 - X_v)` differentiated by `v`,
  the constant term is `-1`.
* For other booleanity factors `1 - X_w(1 - X_w)` with `w ≠ v`, the
  derivative by `v` is the zero polynomial, contributing `0`.
* For adjacency / transition-skeleton factors of shape
  `1 - c · X_i · X_{i+1}`, the derivative has zero constant term because
  every monomial picks up an `X` factor.

The booleanity factor for `v` is genuinely present in
`cookLevinConstraintsTouchingBlock` for the block `assign v`, so the sum
contains at least one `-1` summand.  The total sum is therefore
`≤ -1 ≠ 0`.

This result is the κ = 1 polynomial-side anti-cancellation step.  No
sorries, axioms remain in the kernel-only set
`[propext, Classical.choice, Quot.sound]`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulSeparation
open MultilinearSPDP

attribute [local instance] Classical.dec

/-! ## Constant-coefficient lemmas for individual constraint factors -/

/-- Every booleanity factor `1 - X_w(1 - X_w)` has constant term `1`. -/
theorem coeff_zero_boolLC_factor (n : ℕ) (w : Fin n) :
    MvPolynomial.coeff 0
        ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly) = 1 := by
  rw [CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor]
  exact SymmetricPower.coeff_zero_boolFactor w

/-- Differentiating a booleanity factor `1 - X_w(1 - X_w)` by `v` gives a
polynomial whose constant term is `-1` if `v = w` and `0` otherwise. -/
theorem coeff_zero_pderiv_boolLC_factor (n : ℕ) (v w : Fin n) :
    MvPolynomial.coeff 0
        (MvPolynomial.pderiv v
          ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n w).poly)) =
      (if v = w then (-1 : ℚ) else 0) := by
  rw [CompiledBoolFactorBridge.boolConstraint_factor_eq_boolFactor]
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl]
    exact SymmetricPower.coeff_zero_pderiv_boolFactor v
  · rw [if_neg hvw, SymmetricPower.pderiv_boolFactor_of_ne n v w hvw]
    simp

/-- The Leibniz expansion of `pderiv s (C c · X_i · X_j)`. -/
private theorem pderiv_C_mul_X_mul_X' {n : ℕ} (c : ℚ) (i j s : Fin n) :
    MvPolynomial.pderiv s
        (MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j) :
          MvPolynomial (Fin n) ℚ) =
      MvPolynomial.C c *
        (((if s = i then (1 : MvPolynomial (Fin n) ℚ) else 0) *
            MvPolynomial.X j) +
          (MvPolynomial.X i * (if s = j then 1 else 0))) := by
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
    MvPolynomial.pderiv_mul]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, @eq_comm _ s]

/-- The constant term of `pderiv s (1 - C c · X_i · X_j)` is `0`. -/
theorem coeff_zero_pderiv_cadj_factor_zero' {n : ℕ}
    (c : ℚ) (i j s : Fin n) :
    MvPolynomial.coeff 0
        (MvPolynomial.pderiv s
          ((1 : MvPolynomial (Fin n) ℚ) -
            MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j))) = 0 := by
  rw [← MvPolynomial.constantCoeff_eq]
  rw [map_sub, MvPolynomial.pderiv_one, zero_sub, pderiv_C_mul_X_mul_X']
  -- We now have: constantCoeff (-(C c * inner)) = 0.  Reduce via ring map laws.
  rw [map_neg, map_mul, MvPolynomial.constantCoeff_C]
  -- It remains to show constantCoeff of the inner sum is `0`, hence `-(c * 0) = 0`.
  rw [map_add]
  have h1 :
      MvPolynomial.constantCoeff
          (((if s = i then (1 : MvPolynomial (Fin n) ℚ) else 0) *
            MvPolynomial.X j) :
            MvPolynomial (Fin n) ℚ) = 0 := by
    rw [map_mul, MvPolynomial.constantCoeff_X, mul_zero]
  have h2 :
      MvPolynomial.constantCoeff
          ((MvPolynomial.X i * (if s = j then (1 : MvPolynomial (Fin n) ℚ) else 0)) :
            MvPolynomial (Fin n) ℚ) = 0 := by
    rw [map_mul, MvPolynomial.constantCoeff_X, zero_mul]
  rw [h1, h2, add_zero, mul_zero, neg_zero]

/-- Constant term of any non-booleanity (adjacency or transition-skeleton)
factor is `1`. -/
theorem coeff_zero_rest_factor (M : TuringMachine.DTM) (n : ℕ)
    (lc : LocalConstraint n)
    (hlc : lc ∈ adjConstraintList n ++ transSkelConstraintList M n) :
    MvPolynomial.coeff 0
        ((1 : MvPolynomial (Fin n) ℚ) - lc.poly) = 1 := by
  rw [← MvPolynomial.constantCoeff_eq]
  rw [map_sub, map_one, MvPolynomial.constantCoeff_eq]
  obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc hlc
  rw [hpoly]
  simp [MvPolynomial.coeff_mul]

/-- Constant term of `pderiv v` of any non-booleanity factor is `0`. -/
theorem coeff_zero_pderiv_rest_factor_zero (M : TuringMachine.DTM) (n : ℕ)
    (v : Fin n) (lc : LocalConstraint n)
    (hlc : lc ∈ adjConstraintList n ++ transSkelConstraintList M n) :
    MvPolynomial.coeff 0
        (MvPolynomial.pderiv v
          ((1 : MvPolynomial (Fin n) ℚ) - lc.poly)) = 0 := by
  obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc hlc
  rw [hpoly]
  exact coeff_zero_pderiv_cadj_factor_zero' c i ⟨i.val + 1, hi⟩ v

/-- Every `Cook-Levin` constraint factor has constant term `1`. -/
theorem coeff_zero_cookLevin_factor (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (lc : LocalConstraint n)
    (hlc : lc ∈ (cook_levin_compilation M n hn htb hns).constraints) :
    MvPolynomial.coeff 0
        ((1 : MvPolynomial (Fin n) ℚ) - lc.poly) = 1 := by
  rw [cook_levin_constraints_split M n hn htb hns] at hlc
  rw [List.mem_append] at hlc
  rcases hlc with hlc | hlc
  · rw [List.mem_append] at hlc
    rcases hlc with hlc | hlc
    · unfold boolConstraintList at hlc
      rw [List.mem_map] at hlc
      obtain ⟨w, _hw, rfl⟩ := hlc
      exact coeff_zero_boolLC_factor n w
    · exact coeff_zero_rest_factor M n lc
        (List.mem_append.mpr (Or.inl hlc))
  · exact coeff_zero_rest_factor M n lc
      (List.mem_append.mpr (Or.inr hlc))

/-- Constant term of `pderiv v` of every Cook-Levin constraint factor is
either `0` or `-1` (the latter only for the booleanity factor at `v`). -/
theorem coeff_zero_pderiv_cookLevin_factor_zero_or_neg_one
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) (lc : LocalConstraint n)
    (hlc : lc ∈ (cook_levin_compilation M n hn htb hns).constraints) :
    MvPolynomial.coeff 0
        (MvPolynomial.pderiv v
          ((1 : MvPolynomial (Fin n) ℚ) - lc.poly)) = 0 ∨
    MvPolynomial.coeff 0
        (MvPolynomial.pderiv v
          ((1 : MvPolynomial (Fin n) ℚ) - lc.poly)) = -1 := by
  rw [cook_levin_constraints_split M n hn htb hns] at hlc
  rw [List.mem_append] at hlc
  rcases hlc with hlc | hlc
  · rw [List.mem_append] at hlc
    rcases hlc with hlc | hlc
    · unfold boolConstraintList at hlc
      rw [List.mem_map] at hlc
      obtain ⟨w, _hw, rfl⟩ := hlc
      rw [coeff_zero_pderiv_boolLC_factor n v w]
      by_cases hvw : v = w
      · right; simp [hvw]
      · left; simp [hvw]
    · left
      exact coeff_zero_pderiv_rest_factor_zero M n v lc
        (List.mem_append.mpr (Or.inl hlc))
  · left
    exact coeff_zero_pderiv_rest_factor_zero M n v lc
      (List.mem_append.mpr (Or.inr hlc))

/-! ## Booleanity constraint membership in the touching-block list -/

/-- For the locality block `assign v`, the booleanity constraint at `v`
touches that block (its support is `{v}` and `assign v = b`). -/
theorem boolLC_touches_assign_block
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) :
    cookLevinConstraintTouchesBlock (cook_levin_compilation M n hn htb hns)
        ((cook_levin_compilation M n hn htb hns).partition.assign v)
        (boolLC n v) := by
  unfold cookLevinConstraintTouchesBlock
  refine ⟨v, ?_, rfl⟩
  -- show v ∈ (boolLC n v).support
  show v ∈ ({v} : Finset (Fin n))
  simp

/-- The booleanity constraint at `v` is a member of the global compiler
constraint list. -/
theorem boolLC_mem_cookLevin_constraints'
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) :
    boolLC n v ∈ (cook_levin_compilation M n hn htb hns).constraints := by
  rw [cook_levin_constraints_split M n hn htb hns]
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_append.mpr
  apply Or.inl
  unfold boolConstraintList
  exact List.mem_map.mpr ⟨v, by simp, rfl⟩

/-- The booleanity constraint at `v` belongs to the filtered constraint
list for the locality block `assign v`. -/
theorem boolLC_mem_cookLevinConstraintsTouchingBlock
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) :
    boolLC n v ∈
      cookLevinConstraintsTouchingBlock (cook_levin_compilation M n hn htb hns)
        ((cook_levin_compilation M n hn htb hns).partition.assign v) := by
  classical
  unfold cookLevinConstraintsTouchingBlock
  rw [List.mem_filter]
  refine ⟨boolLC_mem_cookLevin_constraints' M n hn htb hns v, ?_⟩
  exact decide_eq_true (boolLC_touches_assign_block M n hn htb hns v)

/-- A constraint that appears in the filtered list is in particular a
constraint of the original Cook-Levin tableau. -/
theorem cookLevinConstraintsTouchingBlock_subset_constraints
    {M : TuringMachine.DTM} {n : ℕ} (T : CompiledTableau M n)
    (b : Fin T.partition.numBlocks) {c : LocalConstraint T.numVars}
    (hc : c ∈ cookLevinConstraintsTouchingBlock T b) :
    c ∈ T.constraints := by
  classical
  unfold cookLevinConstraintsTouchingBlock at hc
  exact (List.mem_filter.mp hc).1

/-! ## Splitting the filtered list around the booleanity factor -/

/-- The mapped (factor) list for the touched-block constraints. -/
private noncomputable def touchingBlockFactors
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks) :
    List (MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ) :=
  let T := cook_levin_compilation M n hn htb hns
  (cookLevinConstraintsTouchingBlock T b).map
    (fun c => (1 : MvPolynomial (Fin T.numVars) ℚ) - c.poly)

/-- `cookLevinLocalBlockQ` is the product of `touchingBlockFactors`. -/
theorem cookLevinLocalBlockQ_eq_prod
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks) :
    cookLevinLocalBlockQ M n hn htb hns b =
      (touchingBlockFactors M n hn htb hns b).prod := by
  rfl

/-- Every element of `touchingBlockFactors` has constant term `1`. -/
theorem coeff_zero_touchingBlockFactor (M : TuringMachine.DTM) (n : ℕ)
    (hn : n ≥ 2) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (p : MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ)
    (hp : p ∈ touchingBlockFactors M n hn htb hns b) :
    MvPolynomial.coeff 0 p = 1 := by
  unfold touchingBlockFactors at hp
  rw [List.mem_map] at hp
  obtain ⟨lc, hlc, rfl⟩ := hp
  exact coeff_zero_cookLevin_factor M n hn htb hns lc
    (cookLevinConstraintsTouchingBlock_subset_constraints _ _ hlc)

/-- For the block `assign v`, the booleanity factor `1 - (boolLC n v).poly`
appears in the mapped factor list. -/
theorem boolLC_factor_mem_touchingBlockFactors_self
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) :
    ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) ∈
      touchingBlockFactors M n hn htb hns
        ((cook_levin_compilation M n hn htb hns).partition.assign v) := by
  unfold touchingBlockFactors
  exact List.mem_map.mpr
    ⟨boolLC n v, boolLC_mem_cookLevinConstraintsTouchingBlock M n hn htb hns v,
      rfl⟩

/-! ## Main result: the load-bearing anti-cancellation step -/

/-- The load-bearing nonzero-derivative-at-zero step.

The constant term of `pderiv v` applied to `cookLevinLocalBlockQ` for the
locality block containing `v` is nonzero.  This is what Bridge A needs at
`κ = 1` to certify a surviving first-order multilinear SPDP row.

The proof works as follows:

1.  Every factor of the list product has constant term `1`
    (`coeff_zero_touchingBlockFactor`).
2.  Therefore the constant term of `pderiv v` of the product equals the
    sum of constant terms of `pderiv v` applied to each factor
    (`coeff_zero_pderiv_list_prod_eq_sum_deriv_coeff`).
3.  Each summand lies in `{0, -1}`
    (`coeff_zero_pderiv_cookLevin_factor_zero_or_neg_one`).
4.  The booleanity factor `1 - X_v(1 - X_v)` is in the filtered list
    (`boolLC_factor_mem_touchingBlockFactors_self`), and its derivative
    summand equals `-1`.  Therefore `-1` is a member of the summand list.
5.  A sum of values in `{0, -1}` containing at least one `-1` is `≤ -1`,
    in particular nonzero
    (`rat_sum_ne_zero_of_mem_neg_one_and_all_zero_or_neg_one`).
-/
theorem coeff_zero_pderiv_cookLevinLocalBlockQ_ne_zero
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin n) :
    MvPolynomial.coeff 0
        (MvPolynomial.pderiv v
          (cookLevinLocalBlockQ M n hn htb hns
            ((cook_levin_compilation M n hn htb hns).partition.assign v))) ≠
      0 := by
  classical
  -- Notational shorthand.
  set T := cook_levin_compilation M n hn htb hns with hT
  set b := T.partition.assign v with hb
  set fs : List (MvPolynomial (Fin T.numVars) ℚ) :=
    touchingBlockFactors M n hn htb hns b with hfs
  -- Step 1: rewrite the polynomial as the list product.
  have hQ : cookLevinLocalBlockQ M n hn htb hns b = fs.prod := rfl
  rw [hQ]
  -- Step 2: every factor has coeff 0 equal to 1.
  have hconst : ∀ p, p ∈ fs → MvPolynomial.coeff 0 p = 1 := by
    intro p hp
    exact coeff_zero_touchingBlockFactor M n hn htb hns b p hp
  -- Step 3: the constant term of `pderiv v` of the product equals the sum
  -- of the constant terms of the per-factor derivatives.
  rw [ListProdDerivativeConstantCoeff.coeff_zero_pderiv_list_prod_eq_sum_deriv_coeff
        v fs hconst]
  -- Step 4: the summand list has values in `{0, -1}` and contains at least
  -- one `-1` (the booleanity-factor-at-`v` summand).
  set S : List ℚ :=
    fs.map (fun p => MvPolynomial.coeff 0 (MvPolynomial.pderiv v p)) with hS
  have hall : ∀ x, x ∈ S → x = 0 ∨ x = -1 := by
    intro x hx
    rw [hS, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [hfs] at hp
    unfold touchingBlockFactors at hp
    rw [List.mem_map] at hp
    obtain ⟨lc, hlc, rfl⟩ := hp
    exact coeff_zero_pderiv_cookLevin_factor_zero_or_neg_one M n hn htb hns v lc
      (cookLevinConstraintsTouchingBlock_subset_constraints _ _ hlc)
  -- Booleanity factor `1 - (boolLC n v).poly` is present, and its
  -- per-factor summand is `-1`.
  have hbool_factor_mem :
      ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly) ∈ fs := by
    rw [hfs]
    exact boolLC_factor_mem_touchingBlockFactors_self M n hn htb hns v
  have hbool_summand :
      MvPolynomial.coeff 0
          (MvPolynomial.pderiv v
            ((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly)) =
        -1 := by
    rw [coeff_zero_pderiv_boolLC_factor n v v]
    simp
  have hneg_one_mem : (-1 : ℚ) ∈ S := by
    rw [hS]
    refine List.mem_map.mpr
      ⟨((1 : MvPolynomial (Fin n) ℚ) - (boolLC n v).poly),
        hbool_factor_mem, ?_⟩
    exact hbool_summand
  -- Step 5: conclude that the sum of the summand list is nonzero.
  exact ListProdDerivativeConstantCoeff.rat_sum_ne_zero_of_mem_neg_one_and_all_zero_or_neg_one
    S hneg_one_mem hall

/-! ## Axiom audit anchors -/

#print axioms coeff_zero_boolLC_factor
#print axioms coeff_zero_pderiv_boolLC_factor
#print axioms coeff_zero_pderiv_cadj_factor_zero'
#print axioms coeff_zero_rest_factor
#print axioms coeff_zero_pderiv_rest_factor_zero
#print axioms coeff_zero_cookLevin_factor
#print axioms coeff_zero_pderiv_cookLevin_factor_zero_or_neg_one
#print axioms boolLC_touches_assign_block
#print axioms boolLC_mem_cookLevin_constraints'
#print axioms boolLC_mem_cookLevinConstraintsTouchingBlock
#print axioms cookLevinConstraintsTouchingBlock_subset_constraints
#print axioms cookLevinLocalBlockQ_eq_prod
#print axioms coeff_zero_touchingBlockFactor
#print axioms boolLC_factor_mem_touchingBlockFactors_self
#print axioms coeff_zero_pderiv_cookLevinLocalBlockQ_ne_zero

end PallLean.Paper93.Paper283
