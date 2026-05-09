import PallLean.Paper93.DeepMath.PathB.RouteBTouchedActualTypeKR

/-!
# Route B touched canonical-source KR seam

This file removes the arbitrary `sourceOf` selector from the actual-type seam.
For each KR position `j`, the source is now the canonical least constraint in
the actual support fibre of the row variable at `j`; if the fibre is empty, the
window is dormant.

Thus the source word is no longer proof-supplied data.  It is computed from the
concrete Cook--Levin support relation:

`{ i | rowVarAt(j) ∈ support(C_i) }`.

The remaining data is the local normal-form state (`Fin 4`) and the exact
interpretation identity, i.e. the real local-gadget normal-form theorem.
-/

set_option exponentiation.threshold 1024

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- Canonical source index for one window position: the least constraint in the
row-variable support fibre, if such a constraint exists. -/
noncomputable def canonicalTouchedSourceIdx
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) :
    Option (cookLevinConstraintIdx M n hn2 htb hns) :=
  let F := touchedWindowSupportFibre M n hn2 htb hns S hlen j
  if h : F.Nonempty then some (F.min' h) else none

/-- The canonical source, when present, belongs to the actual support fibre. -/
theorem canonicalTouchedSourceIdx_mem_fibre
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n))
    (i : cookLevinConstraintIdx M n hn2 htb hns)
    (hi : canonicalTouchedSourceIdx M n hn2 htb hns S hlen j = some i) :
    i ∈ touchedWindowSupportFibre M n hn2 htb hns S hlen j := by
  classical
  unfold canonicalTouchedSourceIdx at hi
  let F := touchedWindowSupportFibre M n hn2 htb hns S hlen j
  by_cases h : F.Nonempty
  · simp [F, h] at hi
    subst i
    exact Finset.min'_mem F h
  · simp [F, h] at hi

/-- Canonical fibre-backed source record. -/
noncomputable def canonicalTouchedWindowSource
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hlen : S.length = Nat.log 2 n)
    (j : Fin (Nat.log 2 n)) :
    TouchedWindowSource M n hn2 htb hns S hlen j where
  source := canonicalTouchedSourceIdx M n hn2 htb hns S hlen j
  source_mem_fibre := by
    intro i hi
    exact canonicalTouchedSourceIdx_mem_fibre M n hn2 htb hns S hlen j i hi

/-- Canonical-source KR data.

Only `localStateOf` remains as local normal-form data.  The source at every
position is fixed by the actual support fibre. -/
def CookLevinTouchedCanonicalSourceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (interp : touchedKRWords 16 (Nat.log 2 n) →
      MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (localStateOf :
      (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ) →
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)) →
      (hlen : S.length = Nat.log 2 n) →
      (j : Fin (Nat.log 2 n)) → Fin 4),
    ∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (alloc : cookLevinConstraintIdx M n hn2 htb hns →
        List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      (hlen : S.length = Nat.log 2 n) →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (cookLevinTableau M n hn2 htb hns).partition S →
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
      (∀ i, ∀ v ∈ alloc i,
        v ∈ ((cookLevinTableau M n hn2 htb hns).constraints.get i).support) →
      (∀ i, (alloc i).length ≤ 6) →
      (∀ i, i ∉ cookLevinTouchedConstraints M n hn2 htb hns S → alloc i = []) →
      touchedSplitRow M n hn2 htb hns S m alloc =
        interp (fun j => touchedInterfaceStateCode
          (touchedActualInterface
            (canonicalTouchedWindowSource M n hn2 htb hns S hlen j)
            (localStateOf S m alloc hlen j)))

/-- Canonical-source data supplies the actual-type seam by fixing `sourceOf` to
`canonicalTouchedWindowSource`. -/
theorem touchedActualTypeKRData_of_touchedCanonicalSourceKRData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hData : CookLevinTouchedCanonicalSourceKRData M n hn2 htb hns) :
    CookLevinTouchedActualTypeKRData M n hn2 htb hns := by
  rcases hData with ⟨interp, localStateOf, hsound⟩
  refine ⟨interp, ?_, localStateOf, ?_⟩
  · intro S m alloc hlen j
    exact canonicalTouchedWindowSource M n hn2 htb hns S hlen j
  · intro S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout
    exact hsound S m alloc hlen hdeg hmvars hadm hall hcompat hlenAlloc hout

/-- Uniform canonical-source KR data at paper scale. -/
def Step247UniformTouchedCanonicalSourceKRData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinTouchedCanonicalSourceKRData M n hn2 htb hns

/-- Uniform canonical-source data implies the actual-type seam. -/
theorem step247UniformTouchedActualTypeKRData_of_touchedCanonicalSourceKRData
    (hData : Step247UniformTouchedCanonicalSourceKRData) :
    Step247UniformTouchedActualTypeKRData := by
  intro M n hn hn2 htb hns
  exact touchedActualTypeKRData_of_touchedCanonicalSourceKRData
    M n hn2 htb hns (hData M n hn hn2 htb hns)

/-- Uniform canonical-source data closes Route B. -/
theorem noBoundedSATDeciderAtPaperScale_of_touchedCanonicalSourceKRData_TPhi
    (hData : Step247UniformTouchedCanonicalSourceKRData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_touchedActualTypeKRData_TPhi
    (step247UniformTouchedActualTypeKRData_of_touchedCanonicalSourceKRData hData)

/-! ## Axiom audit anchors -/

#print axioms canonicalTouchedSourceIdx
#print axioms canonicalTouchedSourceIdx_mem_fibre
#print axioms canonicalTouchedWindowSource
#print axioms touchedActualTypeKRData_of_touchedCanonicalSourceKRData
#print axioms step247UniformTouchedActualTypeKRData_of_touchedCanonicalSourceKRData
#print axioms noBoundedSATDeciderAtPaperScale_of_touchedCanonicalSourceKRData_TPhi

end PallLean.Paper93.DeepMath.PathB
