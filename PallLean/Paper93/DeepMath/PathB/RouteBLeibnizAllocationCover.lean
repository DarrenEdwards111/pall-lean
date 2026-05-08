import PallLean.Paper93.DeepMath.PathB.RouteBLeibnizTermCover

/-!
# Route B Leibniz allocation cover surface

The previous seam covered arbitrary members of `distribDerivProds`.  This file
opens that definition: a distributed Leibniz term is determined by a derivative
allocation

`h : ι → List (Fin N)`

with every allocated derivative drawn from the row list `S`, and the term is

`∏ i∈s, iterDerivList (h i) (factor i)`.

This is the actual Khatri--Rao counting object in the paper: derivative
allocations across local factors.  The remaining proof after this file is to
construct/count the finite family `G` covering all such allocated products.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- Derivative-allocation cover data for the actual Cook--Levin product.

Compared with `CookLevinLeibnizTermCoverData`, this exposes the witness inside
`LeibnizProduct.distribDerivProds`: every allocation `alloc` whose derivative
variables come from `S` produces a Khatri--Rao term covered by `span G`. -/
def CookLevinLeibnizAllocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (ι : Type) (_ : DecidableEq ι)
    (s : Finset ι)
    (factor : ι → MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
    (G : Finset (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)),
    cookLevinCompiledProduct M n hn2 htb hns = s.prod factor ∧
    G.card ≤ n ^ 200 ∧
    ∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)
      (alloc : ι → List (Fin (cookLevinTableau M n hn2 htb hns).numVars)),
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
      MultilinearSPDP.mlProj
          (m * s.prod (fun i => SPDP.iterDerivList (alloc i) (factor i))) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Allocation-cover data implies Leibniz-term cover data by unpacking
`distribDerivProds`. -/
theorem cookLevinLeibnizTermCoverData_of_allocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hAlloc : CookLevinLeibnizAllocationCoverData M n hn2 htb hns) :
    CookLevinLeibnizTermCoverData M n hn2 htb hns := by
  rcases hAlloc with ⟨ι, instDec, s, factor, G, hprod, hcard, hAllocTerm⟩
  refine ⟨ι, instDec, s, factor, G, hprod, hcard, ?_⟩
  intro S m q hq
  rcases hq with ⟨alloc, hall, rfl⟩
  exact hAllocTerm S m alloc hall

/-- Allocation-cover data implies row-cover data. -/
theorem cookLevinFactorRowCoverData_of_allocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hAlloc : CookLevinLeibnizAllocationCoverData M n hn2 htb hns) :
    CookLevinFactorRowCoverData M n hn2 htb hns :=
  cookLevinFactorRowCoverData_of_leibnizTermCoverData M n hn2 htb hns
    (cookLevinLeibnizTermCoverData_of_allocationCoverData
      M n hn2 htb hns hAlloc)

/-- Allocation-cover data implies factor-local KR data. -/
theorem cookLevinFactorLocalKRData_of_allocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hAlloc : CookLevinLeibnizAllocationCoverData M n hn2 htb hns) :
    CookLevinFactorLocalKRData M n hn2 htb hns :=
  cookLevinFactorLocalKRData_of_leibnizTermCoverData M n hn2 htb hns
    (cookLevinLeibnizTermCoverData_of_allocationCoverData
      M n hn2 htb hns hAlloc)

/-- Allocation-cover data implies the plain `cookLevinQ` P-side bound. -/
theorem plainCookLevinQPSideBound_of_allocationCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hAlloc : CookLevinLeibnizAllocationCoverData M n hn2 htb hns) :
    PlainCookLevinQPSideBound M n hn2 htb hns :=
  plainCookLevinQPSideBound_of_leibnizTermCoverData M n hn2 htb hns
    (cookLevinLeibnizTermCoverData_of_allocationCoverData
      M n hn2 htb hns hAlloc)

/-- Uniform allocation-cover data at paper scale. -/
def Step247UniformLeibnizAllocationCoverData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinLeibnizAllocationCoverData M n hn2 htb hns

/-- Uniform allocation-cover data discharges the Leibniz-term cover seam. -/
theorem step247UniformLeibnizTermCoverData_of_allocationCoverData
    (hAlloc : Step247UniformLeibnizAllocationCoverData) :
    Step247UniformLeibnizTermCoverData := by
  intro M n hn hn2 htb hns
  exact cookLevinLeibnizTermCoverData_of_allocationCoverData
    M n hn2 htb hns (hAlloc M n hn hn2 htb hns)

/-- Uniform allocation-cover data closes the Route B `T_Φ` no-decider surface. -/
theorem noBoundedSATDeciderAtPaperScale_of_allocationCoverData_TPhi
    (hAlloc : Step247UniformLeibnizAllocationCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_leibnizTermCoverData_TPhi
    (step247UniformLeibnizTermCoverData_of_allocationCoverData hAlloc)

/-! ## Axiom audit anchors -/

#print axioms cookLevinLeibnizTermCoverData_of_allocationCoverData
#print axioms cookLevinFactorRowCoverData_of_allocationCoverData
#print axioms cookLevinFactorLocalKRData_of_allocationCoverData
#print axioms plainCookLevinQPSideBound_of_allocationCoverData
#print axioms step247UniformLeibnizTermCoverData_of_allocationCoverData
#print axioms noBoundedSATDeciderAtPaperScale_of_allocationCoverData_TPhi

end PallLean.Paper93.DeepMath.PathB
