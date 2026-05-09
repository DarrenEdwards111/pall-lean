import PallLean.Paper93.DeepMath.PathB.RouteBTouchedConstraintKR

/-!
# Route B touched split KR seam

The previous touched-constraint seam proved the support fact that every
support-compatible allocation is empty outside the constraints whose local
support intersects the SPDP row `S`.

This file makes the next paper-faithful reduction explicit: the concrete
Cook--Levin product is split into the product over touched constraints and the
product over untouched constraints.  Nothing is discarded and no global/common
span is introduced; the new KR obligation covers the exact split row.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- Exact split of the allocated Cook--Levin product into the factors whose
constraint index is touched by the SPDP row `S` and its complement. -/
theorem cookLevinAllocatedProduct_split_touched
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) :
    (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).prod
        (fun i => SPDP.iterDerivList (alloc i)
          (cookLevinConstraintFactor M n hn2 htb hns i)) =
      ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
        (fun i => i ∈ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
          (fun i => SPDP.iterDerivList (alloc i)
            (cookLevinConstraintFactor M n hn2 htb hns i)) *
      ((Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)).filter
        (fun i => i ∉ cookLevinTouchedConstraints M n hn2 htb hns S)).prod
          (fun i => SPDP.iterDerivList (alloc i)
            (cookLevinConstraintFactor M n hn2 htb hns i)) := by
  classical
  simpa using
    (Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset (cookLevinConstraintIdx M n hn2 htb hns)))
      (p := fun i => i ∈ cookLevinTouchedConstraints M n hn2 htb hns S)
      (f := fun i => SPDP.iterDerivList (alloc i)
        (cookLevinConstraintFactor M n hn2 htb hns i))).symm

/-- Split-touched KR data.

This is the same row-faithful object as `CookLevinTouchedConstraintKRData`, but
with the product written in the paper's exact touched/untouched form.  The
untouched product is kept explicitly; later counting work must control it by
the actual Cook--Levin locality/type structure, not by pretending it is absent.
-/
def CookLevinTouchedSplitKRData
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

/-- The exact touched/untouched split KR seam implies the previous touched KR
seam by the product-splitting identity. -/
theorem touchedConstraintKRData_of_touchedSplitKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hSplit : CookLevinTouchedSplitKRData M n hn2 htb hns) :
    CookLevinTouchedConstraintKRData M n hn2 htb hns := by
  rcases hSplit with ⟨G, hcard, hcover⟩
  refine ⟨G, hcard, ?_⟩
  intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
  rw [cookLevinAllocatedProduct_split_touched M n hn2 htb hns S alloc]
  exact hcover S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform split-touched KR data at paper scale. -/
def Step247UniformTouchedSplitKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedSplitKRData M n hn2 htb hns

/-- Uniform split-touched KR data implies the touched-constraint seam. -/
theorem step247UniformTouchedConstraintKRData_of_touchedSplitKRData
    (hSplit : Step247UniformTouchedSplitKRData) :
    Step247UniformTouchedConstraintKRData := by
  intro M n hn hn2 htb hns
  exact touchedConstraintKRData_of_touchedSplitKRData
    M n hn2 htb hns (hSplit M n hn hn2 htb hns)

/-- Uniform split-touched KR data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedSplitKRData_TPhi
    (hSplit : Step247UniformTouchedSplitKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedConstraintKRData_TPhi
    (step247UniformTouchedConstraintKRData_of_touchedSplitKRData hSplit)

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllocatedProduct_split_touched
#print axioms touchedConstraintKRData_of_touchedSplitKRData
#print axioms step247UniformTouchedConstraintKRData_of_touchedSplitKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedSplitKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
