import PallLean.Paper93.DeepMath.PathB.RouteBTouchedSplitKR

/-!
# Route B touched-incidence count KR seam

This file pushes the final Khatri--Rao obligation down to the paper-faithful
incidence-counting surface.

A constraint is touched exactly because one of the row variables `v ∈ S` lies in
that constraint's local support.  Therefore the touched set is covered by the
union, over `v ∈ S`, of the local incidence fibres `{ i | v ∈ support(C_i) }`.
This is the correct combinatorial counting target before constructing the final
KR generator family; no global coordinate span or all-profile shortcut is used.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Concrete Cook--Levin constraints whose local support contains a fixed
variable `v`. -/
noncomputable def cookLevinConstraintsTouchingVar
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin (cookLevinTableau M n hn2 htb hns).numVars) :
    Finset (cookLevinConstraintIdx M n hn2 htb hns) :=
  (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
    (fun i => v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support)

/-- Every touched constraint lies in the incidence fibre of some row variable. -/
theorem cookLevinTouchedConstraints_subset_rowIncidenceUnion
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    cookLevinTouchedConstraints M n hn2 htb hns S ⊆
      S.toFinset.biUnion
        (fun v => cookLevinConstraintsTouchingVar M n hn2 htb hns v) := by
  classical
  intro i hi
  unfold cookLevinTouchedConstraints at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with ⟨v, hv⟩
  have hpair := Finset.mem_inter.mp hv
  rcases hpair with ⟨hvsupp, hvS⟩
  rw [Finset.mem_biUnion]
  refine ⟨v, hvS, ?_⟩
  unfold cookLevinConstraintsTouchingVar
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hvsupp

/-- The touched-constraint count is bounded by the sum of row-variable incidence
fibre sizes.  This is the exact union-bound counting step. -/
theorem cookLevinTouchedConstraints_card_le_rowIncidenceSum
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (cookLevinTouchedConstraints M n hn2 htb hns S).card ≤
      ∑ v ∈ S.toFinset,
        (cookLevinConstraintsTouchingVar M n hn2 htb hns v).card := by
  classical
  exact (Finset.card_le_card
    (cookLevinTouchedConstraints_subset_rowIncidenceUnion M n hn2 htb hns S)).trans
    (Finset.card_biUnion_le)

/-- If every row variable has at most `B` incident constraints, then the touched
set has at most `|S| * B` constraints. -/
theorem cookLevinTouchedConstraints_card_le_rowCard_mul_incidenceBound
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : ℕ)
    (hInc : ∀ v ∈ S.toFinset,
      (cookLevinConstraintsTouchingVar M n hn2 htb hns v).card ≤ B) :
    (cookLevinTouchedConstraints M n hn2 htb hns S).card ≤ S.toFinset.card * B := by
  classical
  calc
    (cookLevinTouchedConstraints M n hn2 htb hns S).card
        ≤ ∑ v ∈ S.toFinset,
            (cookLevinConstraintsTouchingVar M n hn2 htb hns v).card :=
          cookLevinTouchedConstraints_card_le_rowIncidenceSum M n hn2 htb hns S
    _ ≤ ∑ _v ∈ S.toFinset, B := by
          exact Finset.sum_le_sum (fun v hv => hInc v hv)
    _ = S.toFinset.card * B := by
          simp

/-- Every single-variable incidence fibre is bounded by the total number of
Cook--Levin constraints, hence by the polynomial constraint-count bound. -/
theorem cookLevinConstraintsTouchingVar_card_le_n_pow_ten
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin (cookLevinTableau M n hn2 htb hns).numVars) :
    (cookLevinConstraintsTouchingVar M n hn2 htb hns v).card ≤ n ^ 10 := by
  classical
  calc
    (cookLevinConstraintsTouchingVar M n hn2 htb hns v).card
        ≤ (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).card := by
          unfold cookLevinConstraintsTouchingVar
          exact Finset.card_filter_le _ _
    _ = (cookLevinTableau M n hn2 htb hns).constraints.length := by
          simp [cookLevinConstraintIdx]
    _ ≤ n ^ 10 := cookLevin_constraints_length_le_n_pow_ten M n hn2 htb hns

/-- With the actual SPDP row length hypothesis, a uniform per-variable incidence
bound `B` gives the paper row-size count `log₂(n) * B`. -/
theorem cookLevinTouchedConstraints_card_le_log_mul_incidenceBound
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (B : ℕ)
    (hlen : S.length = Nat.log 2 n)
    (hInc : ∀ v ∈ S.toFinset,
      (cookLevinConstraintsTouchingVar M n hn2 htb hns v).card ≤ B) :
    (cookLevinTouchedConstraints M n hn2 htb hns S).card ≤ Nat.log 2 n * B := by
  classical
  exact (cookLevinTouchedConstraints_card_le_rowCard_mul_incidenceBound
    M n hn2 htb hns S B hInc).trans
    (Nat.mul_le_mul_right B (by
      simpa [hlen] using List.toFinset_card_le S))

/-- The paper-faithful touched set has at most `log₂(n) * n^10` constraints:
one union-bound over row variables, and one global Cook--Levin constraint-count
bound for each single-variable incidence fibre. -/
theorem cookLevinTouchedConstraints_card_le_log_mul_n_pow_ten
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n) :
    (cookLevinTouchedConstraints M n hn2 htb hns S).card ≤
      Nat.log 2 n * n ^ 10 := by
  exact cookLevinTouchedConstraints_card_le_log_mul_incidenceBound
    M n hn2 htb hns S (n ^ 10) hlen
    (fun v _hv => cookLevinConstraintsTouchingVar_card_le_n_pow_ten
      M n hn2 htb hns v)

/-- Touched-incidence split KR data.

This packages the exact split KR cover together with the real incidence-count
side condition for touched constraints.  The remaining proof obligation is now:
construct the split-row KR family while proving the local incidence fibres are
small enough for the paper's polynomial budget.
-/
def CookLevinTouchedIncidenceSplitKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    G.card ≤ n ^ 200 ∧
    (∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      S.length = Nat.log 2 n →
      (cookLevinTouchedConstraints M n hn2 htb hns S).card ≤
        Nat.log 2 n * n ^ 10) ∧
    ∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (cookLevinTableau M n hn2 htb hns).partition S →
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
      (∀ i, ∀ v ∈ alloc i,
        v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) →
      (∀ i, (alloc i).length ≤ 6) →
      (∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []) →
      MultilinearSPDP.mlProj
          (m *
            (((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
              (fun i => i ∈ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
                (fun i => SPDP.iterDerivList (alloc i)
                  (cookLevinConstraintFactor M n hn2 htb hns i)) *
            ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
              (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
                (fun i => SPDP.iterDerivList (alloc i)
                  (cookLevinConstraintFactor M n hn2 htb hns i)))) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- The incidence-count split seam implies the split KR seam. -/
theorem touchedSplitKRData_of_touchedIncidenceSplitKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedIncidenceSplitKRData M n hn2 htb hns) :
    CookLevinTouchedSplitKRData M n hn2 htb hns := by
  rcases hData with ⟨G, hcard, _hcount, hcover⟩
  exact ⟨G, hcard, hcover⟩

/-- The split KR seam automatically supplies the incidence-count split seam;
the touched-constraint count is proved above, not assumed. -/
theorem touchedIncidenceSplitKRData_of_touchedSplitKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hSplit : CookLevinTouchedSplitKRData M n hn2 htb hns) :
    CookLevinTouchedIncidenceSplitKRData M n hn2 htb hns := by
  rcases hSplit with ⟨G, hcard, hcover⟩
  exact ⟨G, hcard,
    (fun S hlen => cookLevinTouchedConstraints_card_le_log_mul_n_pow_ten
      M n hn2 htb hns S hlen), hcover⟩

/-- Uniform touched-incidence split KR data at paper scale. -/
def Step247UniformTouchedIncidenceSplitKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedIncidenceSplitKRData M n hn2 htb hns

/-- Uniform incidence-count split data implies the split-touched seam. -/
theorem step247UniformTouchedSplitKRData_of_touchedIncidenceSplitKRData
    (hData : Step247UniformTouchedIncidenceSplitKRData) :
    Step247UniformTouchedSplitKRData := by
  intro M n hn hn2 htb hns
  exact touchedSplitKRData_of_touchedIncidenceSplitKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform incidence-count split data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedIncidenceSplitKRData_TPhi
    (hData : Step247UniformTouchedIncidenceSplitKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedSplitKRData_TPhi
    (step247UniformTouchedSplitKRData_of_touchedIncidenceSplitKRData hData)

/-! ## Axiom audit anchors -/

#print axioms cookLevinTouchedConstraints_subset_rowIncidenceUnion
#print axioms cookLevinTouchedConstraints_card_le_rowIncidenceSum
#print axioms cookLevinTouchedConstraints_card_le_rowCard_mul_incidenceBound
#print axioms cookLevinConstraintsTouchingVar_card_le_n_pow_ten
#print axioms cookLevinTouchedConstraints_card_le_log_mul_incidenceBound
#print axioms cookLevinTouchedConstraints_card_le_log_mul_n_pow_ten
#print axioms touchedSplitKRData_of_touchedIncidenceSplitKRData
#print axioms touchedIncidenceSplitKRData_of_touchedSplitKRData
#print axioms step247UniformTouchedSplitKRData_of_touchedIncidenceSplitKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedIncidenceSplitKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
