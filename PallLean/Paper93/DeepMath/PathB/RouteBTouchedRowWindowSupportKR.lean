import PallLean.Paper93.DeepMath.PathB.RouteBTouchedLocalWindowSupportKR
import PallLean.Paper93.DeepMath.PathB.RouteBConcreteLocalDerivativeFacts

/-!
# Route B touched row-window support

This file lifts the concrete radius-1 Cook--Levin support theorem from one
factor to the product-rule rows used in the touched KR seam.  Every touched
allocated derivative factor lives inside the union of the three-point local
windows around the SPDP row variables.  This is the precise locality input for
the paper's finite local chart; it does not count transition-state factors and
it does not drop the untouched background product.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Radius-1 row window: union of local windows around all row variables. -/
noncomputable def cookLevinRowLocalWindow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars) :=
  S.toFinset.biUnion
    (fun v => cookLevinVarLocalWindow
      (cookLevinTableau M n hn2 htb hns).numVars v)

/-- The row local window has at most three variables per row entry. -/
theorem cookLevinRowLocalWindow_card_le_three_mul
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (cookLevinRowLocalWindow M n hn2 htb hns S).card ≤ 3 * S.toFinset.card := by
  classical
  unfold cookLevinRowLocalWindow
  calc
    (S.toFinset.biUnion
      (fun v => cookLevinVarLocalWindow
        (cookLevinTableau M n hn2 htb hns).numVars v)).card
        ≤ ∑ v ∈ S.toFinset,
            (cookLevinVarLocalWindow
              (cookLevinTableau M n hn2 htb hns).numVars v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ S.toFinset, 3 := by
      exact Finset.sum_le_sum (fun v _hv =>
        cookLevinVarLocalWindow_card_le_three
          (cookLevinTableau M n hn2 htb hns).numVars v)
    _ = S.toFinset.card * 3 := by simp
    _ = 3 * S.toFinset.card := by rw [mul_comm]

/-- At paper row length, the row local window has size at most `3 log₂ n`. -/
theorem cookLevinRowLocalWindow_card_le_three_mul_log
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n) :
    (cookLevinRowLocalWindow M n hn2 htb hns S).card ≤ 3 * Nat.log 2 n := by
  exact (cookLevinRowLocalWindow_card_le_three_mul M n hn2 htb hns S).trans
    (Nat.mul_le_mul_left 3 (by
      simpa [hlen] using List.toFinset_card_le S))

/-- A touched constraint has a source row variable whose local window contains
its whole support. -/
theorem cookLevinTouchedConstraint_support_subset_rowLocalWindow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : i ∈ cookLevinTouchedConstraints M n hn2 htb hns S) :
    ((cookLevinTableau M n hn2 htb hns).constraints.get i).support ⊆
      cookLevinRowLocalWindow M n hn2 htb hns S := by
  classical
  unfold cookLevinTouchedConstraints at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with ⟨v, hv⟩
  rcases Finset.mem_inter.mp hv with ⟨hvsupp, hvS⟩
  intro w hw
  unfold cookLevinRowLocalWindow
  rw [Finset.mem_biUnion]
  refine ⟨v, hvS, ?_⟩
  exact cookLevinConstraint_support_subset_localWindow_of_mem
    M n hn2 htb hns i v hvsupp hw

/-- Variables of an allocated derivative of a touched factor lie in the row
local window. -/
theorem cookLevinTouchedAllocatedFactor_vars_subset_rowLocalWindow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : i ∈ cookLevinTouchedConstraints M n hn2 htb hns S) :
    (SPDP.iterDerivList (alloc i)
      (cookLevinConstraintFactor M n hn2 htb hns i)).vars ⊆
        cookLevinRowLocalWindow M n hn2 htb hns S := by
  intro w hw
  have hiter := Step222.vars_iterDerivList_subset (alloc i)
    (cookLevinConstraintFactor M n hn2 htb hns i) hw
  have hfactor := cookLevinConstraintFactor_vars_subset_support
    M n hn2 htb hns i hiter
  exact cookLevinTouchedConstraint_support_subset_rowLocalWindow
    M n hn2 htb hns S i hi hfactor

/-- The touched allocated product alone.  The untouched background product is
kept separate: it is handled by profile/monoid compression, not by this local
support theorem. -/
noncomputable def touchedAllocatedProductOnly
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ :=
  ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
    (fun i => i ∈ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
      (fun i => SPDP.iterDerivList (alloc i)
        (cookLevinConstraintFactor M n hn2 htb hns i))

/-- The touched allocated product uses only the row local window. -/
theorem touchedAllocatedProductOnly_vars_subset_rowLocalWindow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (touchedAllocatedProductOnly M n hn2 htb hns S alloc).vars ⊆
      cookLevinRowLocalWindow M n hn2 htb hns S := by
  classical
  intro w hw
  unfold touchedAllocatedProductOnly at hw
  have hsubset := MvPolynomial.vars_prod
    (s := ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
      (fun i => i ∈ cookLevinTouchedConstraints M n hn2 htb hns S)))
    (fun i => SPDP.iterDerivList (alloc i)
      (cookLevinConstraintFactor M n hn2 htb hns i))
  have hbi := hsubset hw
  rw [Finset.mem_biUnion] at hbi
  rcases hbi with ⟨i, hi, hwi⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact cookLevinTouchedAllocatedFactor_vars_subset_rowLocalWindow
    M n hn2 htb hns S alloc i hi hwi

/-- The monomial shift support is contained in the row local window whenever its
support is contained in the row. -/
theorem touchedShiftMonomial_vars_subset_rowLocalWindow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S) :
    (touchedShiftMonomial T).vars ⊆
      cookLevinRowLocalWindow M n hn2 htb hns S.toList := by
  intro w hw
  unfold touchedShiftMonomial at hw
  have hsubset := MvPolynomial.vars_prod
    (s := T) (fun v => MvPolynomial.X v : Fin (cookLevinTableau M n hn2 htb hns).numVars →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
  have hprod := hsubset hw
  rw [Finset.mem_biUnion] at hprod
  rcases hprod with ⟨v, hvT, hwv⟩
  simp only [MvPolynomial.vars_X, Finset.mem_singleton] at hwv
  subst w
  unfold cookLevinRowLocalWindow
  rw [Finset.mem_biUnion]
  refine ⟨v, ?_, mem_cookLevinVarLocalWindow_self _ v⟩
  simpa using hT hvT

/-- The touched monomial local product before multiplying by untouched background
factors is supported in the row local window. -/
theorem touchedMonomialLocalPart_vars_subset_rowLocalWindow
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S) :
    (touchedShiftMonomial T *
      touchedAllocatedProductOnly M n hn2 htb hns S.toList alloc).vars ⊆
      cookLevinRowLocalWindow M n hn2 htb hns S.toList := by
  intro w hw
  have hmul := MvPolynomial.vars_mul
    (touchedShiftMonomial T)
    (touchedAllocatedProductOnly M n hn2 htb hns S.toList alloc) hw
  simp only [Finset.mem_union] at hmul
  rcases hmul with hleft | hright
  · exact touchedShiftMonomial_vars_subset_rowLocalWindow M n hn2 htb hns S T hT hleft
  · exact touchedAllocatedProductOnly_vars_subset_rowLocalWindow M n hn2 htb hns S.toList alloc hright

/-! ## Axiom audit anchors -/

#print axioms cookLevinRowLocalWindow_card_le_three_mul
#print axioms cookLevinRowLocalWindow_card_le_three_mul_log
#print axioms cookLevinTouchedConstraint_support_subset_rowLocalWindow
#print axioms cookLevinTouchedAllocatedFactor_vars_subset_rowLocalWindow
#print axioms touchedAllocatedProductOnly_vars_subset_rowLocalWindow
#print axioms touchedShiftMonomial_vars_subset_rowLocalWindow
#print axioms touchedMonomialLocalPart_vars_subset_rowLocalWindow

end PallLean.Paper93.DeepMath.PathB
