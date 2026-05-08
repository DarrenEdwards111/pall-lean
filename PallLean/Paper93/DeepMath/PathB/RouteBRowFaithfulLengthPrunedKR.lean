import PallLean.Paper93.DeepMath.PathB.RouteBLengthPrunedAllocationCover

/-!
# Route B row-faithful length-pruned KR seam

The earlier allocation seams intentionally over-exposed the distributed Leibniz
terms.  This file restores the exact SPDP-row hypotheses from
`CookLevinFactorRowCoverData` at the allocation/Khatri--Rao level:

* `S.length = log₂ n`,
* `m.totalDegree ≤ log₂ n`,
* `m.vars ⊆ S.toFinset`,
* block admissibility of `S`.

This is the honest paper §40.2 target: construct one finite family `G` of size
`≤ n^200` covering only the nonzero, support-compatible, length≤6 distributed
Leibniz rows that arise from actual strict-κ SPDP generators.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- Row-faithful length-pruned allocation cover data.

This is now the precise finite KR obligation for Route B: for each genuine SPDP
row `(S,m)` and each nonzero distributed allocation over the concrete
Cook--Levin constraint factors, the projected product lies in `span G`. -/
def CookLevinRowFaithfulLengthPrunedKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    G.card ≤ n ^ 200 ∧
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
      MultilinearSPDP.mlProj
          (m * (Finset.univ : Finset
            (cookLevinConstraintIdx M n hn2 htb hns)).prod
              (fun i => SPDP.iterDerivList (alloc i)
                (cookLevinConstraintFactor M n hn2 htb hns i))) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Row-faithful length-pruned KR data directly implies the row-cover seam.

The proof uses the concrete product presentation and the landed iterated
Leibniz theorem.  Allocations outside support or of local length >6 are zero
rows, so the KR hypothesis only needs to cover the genuinely nonzero cases. -/
theorem cookLevinFactorRowCoverData_of_rowFaithfulLengthPrunedKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hKR : CookLevinRowFaithfulLengthPrunedKRData M n hn2 htb hns) :
    CookLevinFactorRowCoverData M n hn2 htb hns := by
  rcases hKR with ⟨G, hcard, hcover⟩
  refine ⟨G, hcard, ?_⟩
  intro S m hlen hdeg hmvars hadm
  have hLeib : SPDP.iterDerivList S (cookLevinCompiledProduct M n hn2 htb hns) ∈
      Submodule.span ℚ
        (LeibnizProduct.distribDerivProds
          (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns))
          (cookLevinConstraintFactor M n hn2 htb hns) S) := by
    rw [cookLevinCompiledProduct_eq_constraintIdx_prod M n hn2 htb hns]
    exact LeibnizProduct.iterDerivList_finset_prod_mem_span
      (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns))
      (cookLevinConstraintFactor M n hn2 htb hns) S
  refine mlProj_mul_mem_of_span_le_cover
    m (SPDP.iterDerivList S (cookLevinCompiledProduct M n hn2 htb hns))
    (LeibnizProduct.distribDerivProds
      (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns))
      (cookLevinConstraintFactor M n hn2 htb hns) S)
    (Submodule.span ℚ (↑G : Set (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)))
    hLeib
    ?_
  intro q hq
  rcases hq with ⟨alloc, hall, rfl⟩
  by_cases hcompat : ∀ i, ∀ v ∈ alloc i,
      v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support
  · by_cases hlenAlloc : ∀ i, (alloc i).length ≤ 6
    · exact hcover S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc
    · have hbad : ∃ i, 6 < (alloc i).length := by
        push_neg at hlenAlloc
        exact hlenAlloc
      rw [mlProj_allocatedProduct_eq_zero_of_factor_length_gt_six
        M n hn2 htb hns m alloc hbad]
      exact Submodule.zero_mem _
  · have hbad : ∃ i, ∃ v ∈ alloc i,
        v ∉ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support := by
      push_neg at hcompat
      exact hcompat
    rw [mlProj_allocatedProduct_eq_zero_of_not_supportCompatible
      M n hn2 htb hns m alloc hbad]
    exact Submodule.zero_mem _

/-- Uniform row-faithful length-pruned KR data at paper scale. -/
def Step247UniformRowFaithfulLengthPrunedKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinRowFaithfulLengthPrunedKRData M n hn2 htb hns

/-- Uniform row-faithful KR data implies the original factor row-cover seam. -/
theorem step247UniformFactorRowCoverData_of_rowFaithfulLengthPrunedKRData
    (hKR : Step247UniformRowFaithfulLengthPrunedKRData) :
    Step247UniformFactorRowCoverData := by
  intro M n hn hn2 htb hns
  exact cookLevinFactorRowCoverData_of_rowFaithfulLengthPrunedKRData
    M n hn2 htb hns (hKR M n hn hn2 htb hns)

/-- Uniform row-faithful length-pruned KR data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_rowFaithfulLengthPrunedKRData_TPhi
    (hKR : Step247UniformRowFaithfulLengthPrunedKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_factorRowCoverData_TPhi
    (step247UniformFactorRowCoverData_of_rowFaithfulLengthPrunedKRData hKR)

/-! ## Axiom audit anchors -/

#print axioms cookLevinFactorRowCoverData_of_rowFaithfulLengthPrunedKRData
#print axioms step247UniformFactorRowCoverData_of_rowFaithfulLengthPrunedKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_rowFaithfulLengthPrunedKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
