import PallLean.Paper93.DeepMath.PathB.RouteBFactorLocalCookLevin

/-!
# Route B factor-local row-cover surface

This file opens the remaining Khatri--Rao seam one level further.  Instead of
assuming the subspace inclusion directly, it states the row-level obligation:
for every admissible derivative list `S` and multiplier `m`, the actual SPDP row

`mlProj (m * iterDerivList S (∏ᵢ (1 - Cᵢ)))`

lies in one finite Khatri--Rao span `G` of size `≤ n^200`.

This is the paper §40.2 proof obligation in its generator-by-generator form.
No profile collapse, no additive sheet, and no total-degree CEW shortcut is
introduced.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- Row-level factor-local KR cover for the actual Cook--Levin product.

A single finite family `G` must cover every strict-κ SPDP generator row at
`κ = ℓ = log₂ n`. This is exactly the generator form of the subspace inclusion
in `CookLevinFactorLocalKRData`. -/
def CookLevinFactorRowCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
    G.card ≤ n ^ 200 ∧
    ∀ (S : List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible (cookLevinTableau M n hn2 htb hns).partition S →
      MultilinearSPDP.mlProj
          (m * SPDP.iterDerivList S
            (cookLevinCompiledProduct M n hn2 htb hns)) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Row-cover data implies the finite KR subspace inclusion data. -/
theorem cookLevinFactorLocalKRData_of_rowCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hRows : CookLevinFactorRowCoverData M n hn2 htb hns) :
    CookLevinFactorLocalKRData M n hn2 htb hns := by
  rcases hRows with ⟨G, hcard, hrow⟩
  refine ⟨G, ?_, hcard⟩
  unfold MultilinearSPDP.mlBlockedSpdpSubspace
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  exact hrow S m hlen hdeg hvars hadm

/-- Row-cover data implies the compiled-product P-side bound. -/
theorem cookLevinCompiledProductPSideBound_of_rowCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hRows : CookLevinFactorRowCoverData M n hn2 htb hns) :
    CookLevinCompiledProductPSideBound M n hn2 htb hns :=
  cookLevinCompiledProductPSideBound_of_factorLocalKRData
    M n hn2 htb hns
    (cookLevinFactorLocalKRData_of_rowCoverData M n hn2 htb hns hRows)

/-- Row-cover data implies the plain `cookLevinQ` P-side bound. -/
theorem plainCookLevinQPSideBound_of_rowCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hRows : CookLevinFactorRowCoverData M n hn2 htb hns) :
    PlainCookLevinQPSideBound M n hn2 htb hns :=
  plainCookLevinQPSideBound_of_factorLocalKRData
    M n hn2 htb hns
    (cookLevinFactorLocalKRData_of_rowCoverData M n hn2 htb hns hRows)

/-- Uniform row-cover data at paper scale. -/
def Step247UniformFactorRowCoverData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinFactorRowCoverData M n hn2 htb hns

/-- Uniform row-cover data discharges the uniform factor-local KR seam. -/
theorem step247UniformFactorLocalKRData_of_rowCoverData
    (hRows : Step247UniformFactorRowCoverData) :
    Step247UniformFactorLocalKRData := by
  intro M n hn hn2 htb hns
  exact cookLevinFactorLocalKRData_of_rowCoverData
    M n hn2 htb hns (hRows M n hn hn2 htb hns)

/-- Uniform row-cover data closes the Route B `T_Φ` no-decider surface. -/
theorem noBoundedSATDeciderAtPaperScale_of_factorRowCoverData_TPhi
    (hRows : Step247UniformFactorRowCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_factorLocalKRData_TPhi
    (step247UniformFactorLocalKRData_of_rowCoverData hRows)

/-! ## Axiom audit anchors -/

#print axioms cookLevinFactorLocalKRData_of_rowCoverData
#print axioms cookLevinCompiledProductPSideBound_of_rowCoverData
#print axioms plainCookLevinQPSideBound_of_rowCoverData
#print axioms step247UniformFactorLocalKRData_of_rowCoverData
#print axioms noBoundedSATDeciderAtPaperScale_of_factorRowCoverData_TPhi

end PallLean.Paper93.DeepMath.PathB
