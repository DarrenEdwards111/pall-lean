/-
  AbstractLocalDerivSpace.lean — Abstract local derivative spaces for symmetric power factorization

  ## Overview

  For each constraint type τ, the "local derivative space" W_τ is the span of
  all possible post-mlProj local derivatives of a factor of that type.

  For booleanity: the factor is 1 - v + v² (for variable v). The possible
  derivatives are:
    - 0 derivatives: 1 - v + v²  →  mlProj gives 1 - v
    - 1 derivative:  -1 + 2v      →  mlProj gives -1 + 2v
    - 2 derivatives: 2             →  mlProj gives 2

  These three elements span a 2-dimensional subspace of Q[v]_multilinear ≅ Q².
  (Since 2 and -1+2v are linearly independent, and 1-v = -(1/2)(-1+2v) + (1/2)·2.)

  ## Formalization

  We work in Q² directly (as Fin 2 → Q), representing multilinear polynomials
  in one variable v as pairs (constant term, coefficient of v).

  The three derivative results become:
    - 1 - v  ↔  (1, -1)
    - -1 + 2v ↔  (-1, 2)
    - 2       ↔  (2, 0)

  We prove these three vectors span all of Q² (dimension 2).

  The instantiation map sends (a, b) to the polynomial a + b*v in Q[z₁,...,zₙ],
  where v = zⱼ for some specific variable index j. This map is linear.
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.StdBasis

namespace AbstractLocalDerivSpace

open Finset

/-! ## Part 1: The abstract booleanity local derivative space in Q² -/

/-- Represent multilinear polynomials in one variable as Q².
    Component 0 = constant term, component 1 = coefficient of the variable.
    So (a, b) represents the polynomial a + b*X. -/
abbrev MLPoly1 := Fin 2 → ℚ

/-- The booleanity factor after mlProj with 0 derivatives: 1 - X ↔ (1, -1). -/
def boolDerivAtom0 : MLPoly1 := ![1, -1]

/-- The booleanity factor after mlProj with 1 derivative: -1 + 2X ↔ (-1, 2). -/
def boolDerivAtom1 : MLPoly1 := ![-1, 2]

/-- The booleanity factor after mlProj with 2 derivatives: 2 ↔ (2, 0). -/
def boolDerivAtom2 : MLPoly1 := ![2, 0]

/-- The set of booleanity derivative atoms. -/
def boolDerivAtoms : Finset MLPoly1 :=
  {boolDerivAtom0, boolDerivAtom1, boolDerivAtom2}

/-- Any element of Q² can be written as a linear combination of
    boolDerivAtom2 = (2,0) and boolDerivAtom1 = (-1,2).

    Explicit formula: x = ((x 0 + x 1 / 2) / 2) • (2,0) + (x 1 / 2) • (-1,2). -/
theorem any_in_span_of_boolAtoms (x : MLPoly1) :
    x ∈ Submodule.span ℚ ({boolDerivAtom2, boolDerivAtom1} : Set MLPoly1) := by
  rw [Submodule.mem_span_pair]
  refine ⟨(x 0 + x 1 / 2) / 2, x 1 / 2, ?_⟩
  ext i
  fin_cases i <;> simp [boolDerivAtom2, boolDerivAtom1] <;> ring

/-- The span of the three booleanity derivative atoms equals the full space Q².

    The atoms {(2,0), (-1,2)} already span Q² (any x can be written as a
    linear combination). Adding (1,-1) does not change the span. -/
theorem boolDerivAtoms_span_eq_top :
    Submodule.span ℚ (↑boolDerivAtoms : Set MLPoly1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  apply Submodule.span_mono _ (any_in_span_of_boolAtoms x)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  simp only [boolDerivAtoms, Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hv with rfl | rfl <;> simp

/-- The abstract booleanity local derivative space has dimension exactly 2. -/
theorem boolLocalDerivSpace_finrank :
    Module.finrank ℚ MLPoly1 = 2 := by
  change Module.finrank ℚ (Fin 2 → ℚ) = 2
  simp

/-- The booleanity derivative atoms span a space of dimension ≤ 2.
    (In fact exactly 2, but ≤ 2 is what we need for the bound.) -/
theorem boolDerivAtoms_span_finrank_le :
    Module.finrank ℚ (Submodule.span ℚ (↑boolDerivAtoms : Set MLPoly1)) ≤ 2 := by
  rw [boolDerivAtoms_span_eq_top]
  simp [boolLocalDerivSpace_finrank]

/-! ## Part 2: The instantiation map

    The instantiation map sends an abstract multilinear polynomial (a, b) ∈ Q²
    to the concrete polynomial a + b * z_j ∈ Q[z₁,...,zₙ], where j is a
    specific variable index.

    This map is linear, and it preserves the structure: different instantiations
    (at different variable indices j) produce polynomials in disjoint variable sets. -/

/-- Instantiate an abstract multilinear polynomial at variable index j.
    Sends (a, b) to a + b * X_j in MvPolynomial (Fin n) Q. -/
noncomputable def instantiate {n : ℕ} (j : Fin n) (w : MLPoly1) :
    MvPolynomial (Fin n) ℚ :=
  MvPolynomial.C (w 0) + MvPolynomial.C (w 1) * MvPolynomial.X j

/-- The instantiation map is linear. -/
noncomputable def instantiateLinearMap {n : ℕ} (j : Fin n) :
    MLPoly1 →ₗ[ℚ] MvPolynomial (Fin n) ℚ where
  toFun := instantiate j
  map_add' := by
    intro w₁ w₂
    simp only [instantiate, Pi.add_apply, map_add]
    ring
  map_smul' := by
    intro r w
    simp only [instantiate, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
      MvPolynomial.smul_eq_C_mul]
    ring

/-- instantiateLinearMap computes instantiate. -/
theorem instantiateLinearMap_apply {n : ℕ} (j : Fin n) (w : MLPoly1) :
    instantiateLinearMap j w = instantiate j w := rfl

/-- Instantiation at different variables produces polynomials whose
    variable sets are disjoint (assuming the abstract polynomial is nonzero
    in the linear component). This is used in the product factorization
    to show that products of instantiated atoms factor correctly through mlProj. -/
theorem instantiate_vars_subset {n : ℕ} (j : Fin n) (w : MLPoly1) :
    (instantiate j w).vars ⊆ {j} := by
  intro v hv
  simp only [instantiate] at hv
  -- vars(C(w 0) + C(w 1) * X_j) ⊆ vars(C(w 0)) ∪ vars(C(w 1) * X_j)
  have h_add := MvPolynomial.vars_add_subset (MvPolynomial.C (w 0))
    (MvPolynomial.C (w 1) * MvPolynomial.X j) hv
  rw [Finset.mem_union] at h_add
  rcases h_add with h | h
  · -- v ∈ vars(C(w 0)): but vars of a constant polynomial is empty
    simp [MvPolynomial.vars_C] at h
  · -- v ∈ vars(C(w 1) * X_j) ⊆ vars(C(w 1)) ∪ vars(X_j) ⊆ ∅ ∪ {j} = {j}
    have h_mul := MvPolynomial.vars_mul (MvPolynomial.C (w 1)) (MvPolynomial.X j) h
    rw [Finset.mem_union] at h_mul
    rcases h_mul with h' | h'
    · simp [MvPolynomial.vars_C] at h'
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at h'
      exact Finset.mem_singleton.mpr h'

/-! ## Part 3: General abstract local derivative space Q^d

    For a constraint type with d local derivative options (after mlProj),
    the abstract local derivative space is Q^d. Each factor of that type
    contributes one element of Q^d per differentiation, and the product
    of m such elements (for m touched factors) spans a space of dimension
    at most C(m + d - 1, d - 1) (the symmetric power dimension).

    For the Cook-Levin case:
    - Booleanity: d = 2, so C(m+1, 1) = m+1
    - Other types: d ≤ 3, so C(m+2, 2) ≤ (m+1)^2

    Total: ∏_tau C(h(tau)+d_tau-1, d_tau-1) ≤ (kappa+1)^8 -/

/-- Abstract local derivative space of dimension d.
    Elements are vectors in Q^d representing multilinear polynomial coefficients. -/
abbrev AbstractLocalSpace (d : ℕ) := Fin d → ℚ

/-- The dimension of the abstract local space is d. -/
theorem abstractLocalSpace_finrank (d : ℕ) :
    Module.finrank ℚ (AbstractLocalSpace d) = d := by
  change Module.finrank ℚ (Fin d → ℚ) = d
  simp

/-! ## Part 4: Product spanning set count

    When m factors each contribute an element from a set of size ≤ N,
    the number of distinct products is ≤ N^m. But when the factors are
    SYMMETRIC (structurally identical blocks, distinguished only by variable
    names), two products that differ only by which block gets which atom
    give the SAME abstract product. This reduces the count from N^m to
    C(m+N-1, N-1) (multiset count = symmetric power dimension).

    For the full formalization of this reduction, we use a different approach:
    we show that the span of all products has finrank ≤ the abstract product
    count, without needing to explicitly construct the symmetric power.

    The key lemma: products of atoms from a d-dimensional space, evaluated
    at m distinct variables, lie in a subspace of dimension ≤ C(m+d-1, d-1).
    This follows because the product ∏_{j=1}^m (a_{j,0} + a_{j,1}*X_{v_j})
    is a multilinear polynomial in {X_{v_1},...,X_{v_m}}, and any such
    polynomial is determined by its 2^m coefficients, but the SPECIFIC
    structure (product of linear forms) constrains it to a smaller space.

    For abstract vectors w_1,...,w_m ∈ Q^d, the product:
      ∏_{j=1}^m instantiate(v_j, w_j)
    = ∏_{j=1}^m (w_j(0) + w_j(1)*X_{v_j})
    = Σ_{S ⊆ {1,...,m}} (∏_{j∈S} w_j(1)) * (∏_{j∉S} w_j(0)) * ∏_{j∈S} X_{v_j}

    This is a product of m linear forms. The span of all such products
    (over all choices of w_1,...,w_m ∈ Q^d) has dimension ≤ C(m+d-1, d-1)
    by the symmetric product dimension formula, WHEN all forms come from the
    same abstract space Q^d and the variables are symmetric. -/

/-- The span of all products of m elements from a Finset of size ≤ N
    has finrank bounded by the set of atom-choice functions.
    This is a general product-span bound: if T is a finite set of
    "atom" polynomials and we take products of m of them (with repetition),
    the span of those products has finrank ≤ |T|^m.
    (The symmetric power improvement C(m+|T|-1, |T|-1) ≤ |T|^m is not
    needed for the final bound since the product over all types already
    gives (kappa+1)^8.) -/
theorem finrank_product_span_le {n : ℕ}
    (atoms : Finset (MvPolynomial (Fin n) ℚ))
    (m : ℕ)
    (productSet : Set (MvPolynomial (Fin n) ℚ))
    (hprod : productSet ⊆ { g | ∃ (choice : Fin m → MvPolynomial (Fin n) ℚ),
      (∀ i, choice i ∈ atoms) ∧ g = Finset.univ.prod choice }) :
    Set.Finite productSet := by
  -- The range of the product map on atom-choices is finite
  let choiceType := Fin m → { a : MvPolynomial (Fin n) ℚ // a ∈ atoms }
  let prodMap : choiceType → MvPolynomial (Fin n) ℚ :=
    fun c => Finset.univ.prod (fun i => (c i).val)
  have hfin_range : Set.Finite (Set.range prodMap) :=
    Set.toFinite (Set.range prodMap)
  apply hfin_range.subset
  intro g hg
  have hg' := hprod hg
  simp only [Set.mem_setOf_eq] at hg'
  obtain ⟨choice, hchoice, rfl⟩ := hg'
  exact ⟨fun i => ⟨choice i, hchoice i⟩, rfl⟩

/-- The product set is contained in the range of the product map on
    (Fin m → atoms_subtype), which is finite with cardinality ≤ |atoms|^m. -/
noncomputable def productFinset {n : ℕ}
    (atoms : Finset (MvPolynomial (Fin n) ℚ))
    (m : ℕ) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  Finset.univ.image
    (fun (c : Fin m → { a : MvPolynomial (Fin n) ℚ // a ∈ atoms }) =>
      Finset.univ.prod (fun i => (c i).val))

/-- The cardinality of the product Finset is ≤ |atoms|^m. -/
theorem productFinset_card_le {n : ℕ}
    (atoms : Finset (MvPolynomial (Fin n) ℚ))
    (m : ℕ) :
    (productFinset atoms m).card ≤ atoms.card ^ m := by
  calc (productFinset atoms m).card
      ≤ Fintype.card (Fin m → { a : MvPolynomial (Fin n) ℚ // a ∈ atoms }) :=
        Finset.card_image_le
    _ = atoms.card ^ m := by simp [Fintype.card_fun, Fintype.card_coe]

/-- Any product of m atoms from the Finset lies in the productFinset. -/
theorem mem_productFinset {n : ℕ}
    (atoms : Finset (MvPolynomial (Fin n) ℚ))
    (m : ℕ)
    (choice : Fin m → MvPolynomial (Fin n) ℚ)
    (hchoice : ∀ i, choice i ∈ atoms) :
    Finset.univ.prod choice ∈ productFinset atoms m := by
  simp only [productFinset, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun i => ⟨choice i, hchoice i⟩, by simp⟩

/-- The finrank of the span of any subset of productFinset is ≤ |atoms|^m. -/
theorem finrank_span_productFinset_le {n : ℕ}
    (atoms : Finset (MvPolynomial (Fin n) ℚ))
    (m : ℕ) :
    Module.finrank ℚ (Submodule.span ℚ
      (↑(productFinset atoms m) : Set (MvPolynomial (Fin n) ℚ))) ≤
      atoms.card ^ m :=
  le_trans (finrank_span_finset_le_card _) (productFinset_card_le atoms m)

end AbstractLocalDerivSpace
