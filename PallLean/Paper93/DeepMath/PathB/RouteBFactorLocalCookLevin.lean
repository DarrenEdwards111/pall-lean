import PallLean.Paper93.DeepMath.PathB.RouteBPlainCookLevinQPSide

/-!
# Route B factor-local Cook--Levin product seam

This file pins the remaining P-side work to the actual Cook--Levin factor
product.  The target is no longer an abstract `HasCEWBound` claim on the
expanded polynomial.  Instead, we expose:

* the concrete product `compiledPoly (cook_levin_compilation M n ...)`;
* its factor-local structural facts (each constraint touches ≤ 10 variables,
  each factor has degree/CEW ≤ 6, and the factor list has polynomial length);
* the exact Khatri--Rao row-span surface that implies the plain `cookLevinQ`
  P-side bound.

The only remaining mathematical content after this file is the real
factor-local Khatri--Rao spanning-set construction for that product.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- The concrete Cook--Levin tableau used by the Route B P-side. -/
noncomputable abbrev cookLevinTableau
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CompiledTableau M n :=
  cook_levin_compilation M n hn2 htb hns

/-- The concrete product polynomial before the `UVSplit` cast used by
`cookLevinQ`. -/
noncomputable abbrev cookLevinCompiledProduct
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
  compiledPoly (cookLevinTableau M n hn2 htb hns)

/-- Rank target on the uncast compiled product at the Cook--Levin partition. -/
def CookLevinCompiledProductPSideBound
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  MultilinearSPDP.mlBlockedSpdpRank
    (cookLevinTableau M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (cookLevinCompiledProduct M n hn2 htb hns) ≤ n ^ 200

/-- The product is exactly the product of local factors `(1 - Cᵢ)`. -/
theorem cookLevinCompiledProduct_eq_factor_product
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    cookLevinCompiledProduct M n hn2 htb hns =
      ((cookLevinTableau M n hn2 htb hns).constraints.map
        (fun c => (1 : MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) - c.poly)).prod :=
  rfl

/-- Each Cook--Levin constraint polynomial touches at most 10 variables. -/
theorem cookLevinConstraint_vars_card_le_ten
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∀ c ∈ (cookLevinTableau M n hn2 htb hns).constraints,
      c.poly.vars.card ≤ 10 :=
  Step225.compiledPoly_radius_1_vars (cookLevinTableau M n hn2 htb hns)

/-- Each Cook--Levin factor `(1 - Cᵢ)` has total degree at most 6. -/
theorem cookLevinFactor_totalDegree_le_six
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∀ c ∈ (cookLevinTableau M n hn2 htb hns).constraints,
      ((1 : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
        - c.poly).totalDegree ≤ 6 :=
  Step225.compiledPoly_gadget_degree_bounded
    (cookLevinTableau M n hn2 htb hns)

/-- Each Cook--Levin factor `(1 - Cᵢ)` has the local CEW/degree bound 6 under
Lean's current `HasCEWBound = totalDegree ≤ target` approximation. -/
theorem cookLevinFactor_hasCEWBound_six
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∀ c ∈ (cookLevinTableau M n hn2 htb hns).constraints,
      HasCEWBound
        ((1 : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
          - c.poly) 6 :=
  Step225.compiledPoly_gadget_cew_bounded
    (cookLevinTableau M n hn2 htb hns)

/-- The Cook--Levin factor list has polynomial length. -/
theorem cookLevin_constraints_length_le_n_pow_ten
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    (cookLevinTableau M n hn2 htb hns).constraints.length ≤ n ^ 10 :=
  (cookLevinTableau M n hn2 htb hns).constraints_poly

/-- The exact factor-local Khatri--Rao row-span surface needed for the compiled
product.  This is the paper §40.2 proof obligation in finite-spanning form. -/
def CookLevinFactorLocalKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    MultilinearSPDP.mlBlockedSpdpSubspace
      (cookLevinTableau M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (cookLevinCompiledProduct M n hn2 htb hns) ≤
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) ∧
    G.card ≤ n ^ 200

/-- Factor-local Khatri--Rao data implies the compiled-product P-side bound. -/
theorem cookLevinCompiledProductPSideBound_of_factorLocalKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hKR : CookLevinFactorLocalKRData M n hn2 htb hns) :
    CookLevinCompiledProductPSideBound M n hn2 htb hns := by
  rcases hKR with ⟨G, hspan, hcard⟩
  exact width_implies_rank_bound_interface
    (cookLevinTableau M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (cookLevinCompiledProduct M n hn2 htb hns)
    G hspan (n ^ 200) hcard

/-- The compiled-product rank bound is definitionally the same P-side target as
plain `cookLevinQ`, after rewriting the pullback partition to the Cook--Levin
partition and reducing the `UVSplit` cast. -/
theorem plainCookLevinQPSideBound_of_compiledProductPSideBound
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hP : CookLevinCompiledProductPSideBound M n hn2 htb hns) :
    PlainCookLevinQPSideBound M n hn2 htb hns := by
  unfold PlainCookLevinQPSideBound
  have hpart := pullback_eq_cook_levin_partition M n hn2 htb hns
  rw [hpart]
  convert hP using 2

/-- Factor-local Khatri--Rao data implies the plain `cookLevinQ` P-side bound
consumed by Route B. -/
theorem plainCookLevinQPSideBound_of_factorLocalKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hKR : CookLevinFactorLocalKRData M n hn2 htb hns) :
    PlainCookLevinQPSideBound M n hn2 htb hns :=
  plainCookLevinQPSideBound_of_compiledProductPSideBound
    M n hn2 htb hns
    (cookLevinCompiledProductPSideBound_of_factorLocalKRData
      M n hn2 htb hns hKR)

/-- Uniform factor-local KR data at paper scale. -/
def Step247UniformFactorLocalKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinFactorLocalKRData M n hn2 htb hns

/-- Uniform factor-local KR data discharges the Route B plain-Q P-side surface. -/
theorem step247UniformPlainCookLevinQPSideBound_of_factorLocalKRData
    (hKR : Step247UniformFactorLocalKRData) :
    Step247UniformPlainCookLevinQPSideBound := by
  intro M n hn hn2 htb hns
  exact plainCookLevinQPSideBound_of_factorLocalKRData
    M n hn2 htb hns (hKR M n hn hn2 htb hns)

/-- Uniform factor-local KR data closes the `T_Φ` Route B no-decider surface. -/
theorem noBoundedSATDeciderAtPaperScale_of_factorLocalKRData_TPhi
    (hKR : Step247UniformFactorLocalKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_plainCookLevinQPSideBound_TPhi
    (step247UniformPlainCookLevinQPSideBound_of_factorLocalKRData hKR)

/-! ## Axiom audit anchors -/

#print axioms cookLevinCompiledProduct_eq_factor_product
#print axioms cookLevinConstraint_vars_card_le_ten
#print axioms cookLevinFactor_totalDegree_le_six
#print axioms cookLevinFactor_hasCEWBound_six
#print axioms cookLevin_constraints_length_le_n_pow_ten
#print axioms cookLevinCompiledProductPSideBound_of_factorLocalKRData
#print axioms plainCookLevinQPSideBound_of_compiledProductPSideBound
#print axioms plainCookLevinQPSideBound_of_factorLocalKRData
#print axioms step247UniformPlainCookLevinQPSideBound_of_factorLocalKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_factorLocalKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
