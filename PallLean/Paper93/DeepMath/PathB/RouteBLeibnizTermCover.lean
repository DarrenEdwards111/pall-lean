import PallLean.Paper93.DeepMath.PathB.RouteBFactorRowCover
import PallLean.LeibnizProduct

/-!
# Route B Leibniz-term cover surface

This file opens the row-cover seam one more faithful step.  The SPDP row
contains `iterDerivList S (∏ᵢ (1-Cᵢ))`; by the already-landed iterated
Leibniz theorem, this derivative lies in the span of distributed derivative
products.  Therefore it is enough to cover every **Leibniz distributed term**
after multiplication by `m` and multilinear projection.

This is still deliberately not a profile/template shortcut: the remaining data
must supply the actual finite Khatri--Rao family and prove each distributed
Leibniz term maps into its span.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler

/-- If `p` lies in the span of a set `A`, and every element of `A` maps into a
submodule `W` under `q ↦ mlProj (m*q)`, then `mlProj (m*p)` lies in `W`.

This is the linearity step that transports the iterated Leibniz span into the
final Khatri--Rao row span. -/
theorem mlProj_mul_mem_of_span_le_cover {N : ℕ}
    (m p : MvPolynomial (Fin N) ℚ)
    (A : Set (MvPolynomial (Fin N) ℚ))
    (W : Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (hp : p ∈ Submodule.span ℚ A)
    (hA : ∀ q ∈ A, MultilinearSPDP.mlProj (m * q) ∈ W) :
    MultilinearSPDP.mlProj (m * p) ∈ W := by
  refine Submodule.span_induction
    (p := fun x _ => MultilinearSPDP.mlProj (m * x) ∈ W)
    hA ?hzero ?hadd ?hsmul hp
  · change MultilinearSPDP.mlProj (m * 0) ∈ W
    rw [mul_zero, MultilinearSPDP.mlProj_zero]
    exact W.zero_mem
  · intro x y _hxmem _hymem hx hy
    change MultilinearSPDP.mlProj (m * (x + y)) ∈ W
    rw [mul_add, MultilinearSPDP.mlProj_add]
    exact W.add_mem hx hy
  · intro a x _hxmem hx
    change MultilinearSPDP.mlProj (m * (a • x)) ∈ W
    rw [mul_smul_comm, MultilinearSPDP.mlProj_smul]
    exact W.smul_mem a hx

/-- Leibniz distributed-term cover data for the actual Cook--Levin product.

The data chooses a concrete finite product presentation of the compiled product
and one row-span family `G`.  The key field is `hTerm`: every distributed
Leibniz product term, after multiplication by the SPDP multiplier `m` and
`mlProj`, lies in `span G`. -/
def CookLevinLeibnizTermCoverData
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
      (q : MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ),
      q ∈ LeibnizProduct.distribDerivProds s factor S →
      MultilinearSPDP.mlProj (m * q) ∈
        Submodule.span ℚ (↑G : Set (MvPolynomial
          (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ))

/-- Leibniz-term cover data implies the row-cover data. -/
theorem cookLevinFactorRowCoverData_of_leibnizTermCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hTerms : CookLevinLeibnizTermCoverData M n hn2 htb hns) :
    CookLevinFactorRowCoverData M n hn2 htb hns := by
  rcases hTerms with ⟨ι, instDec, s, factor, G, hprod, hcard, hTerm⟩
  letI : DecidableEq ι := instDec
  refine ⟨G, hcard, ?_⟩
  intro S m _hlen _hdeg _hvars _hadm
  have hLeib : SPDP.iterDerivList S (cookLevinCompiledProduct M n hn2 htb hns) ∈
      Submodule.span ℚ (LeibnizProduct.distribDerivProds s factor S) := by
    rw [hprod]
    exact LeibnizProduct.iterDerivList_finset_prod_mem_span s factor S
  exact mlProj_mul_mem_of_span_le_cover
    m (SPDP.iterDerivList S (cookLevinCompiledProduct M n hn2 htb hns))
    (LeibnizProduct.distribDerivProds s factor S)
    (Submodule.span ℚ (↑G : Set (MvPolynomial
      (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)))
    hLeib
    (fun q hq => hTerm S m q hq)

/-- Leibniz-term cover data implies the factor-local KR data. -/
theorem cookLevinFactorLocalKRData_of_leibnizTermCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hTerms : CookLevinLeibnizTermCoverData M n hn2 htb hns) :
    CookLevinFactorLocalKRData M n hn2 htb hns :=
  cookLevinFactorLocalKRData_of_rowCoverData M n hn2 htb hns
    (cookLevinFactorRowCoverData_of_leibnizTermCoverData
      M n hn2 htb hns hTerms)

/-- Leibniz-term cover data implies the plain `cookLevinQ` P-side bound. -/
theorem plainCookLevinQPSideBound_of_leibnizTermCoverData
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hTerms : CookLevinLeibnizTermCoverData M n hn2 htb hns) :
    PlainCookLevinQPSideBound M n hn2 htb hns :=
  plainCookLevinQPSideBound_of_rowCoverData M n hn2 htb hns
    (cookLevinFactorRowCoverData_of_leibnizTermCoverData
      M n hn2 htb hns hTerms)

/-- Uniform Leibniz-term cover data at paper scale. -/
def Step247UniformLeibnizTermCoverData : Prop :=
  ∀ (M : DTM) (n : ℕ) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    CookLevinLeibnizTermCoverData M n hn2 htb hns

/-- Uniform Leibniz-term cover data discharges the row-cover seam. -/
theorem step247UniformFactorRowCoverData_of_leibnizTermCoverData
    (hTerms : Step247UniformLeibnizTermCoverData) :
    Step247UniformFactorRowCoverData := by
  intro M n hn hn2 htb hns
  exact cookLevinFactorRowCoverData_of_leibnizTermCoverData
    M n hn2 htb hns (hTerms M n hn hn2 htb hns)

/-- Uniform Leibniz-term cover data closes the Route B `T_Φ` no-decider surface. -/
theorem noBoundedSATDeciderAtPaperScale_of_leibnizTermCoverData_TPhi
    (hTerms : Step247UniformLeibnizTermCoverData) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_factorRowCoverData_TPhi
    (step247UniformFactorRowCoverData_of_leibnizTermCoverData hTerms)

/-! ## Axiom audit anchors -/

#print axioms mlProj_mul_mem_of_span_le_cover
#print axioms cookLevinFactorRowCoverData_of_leibnizTermCoverData
#print axioms cookLevinFactorLocalKRData_of_leibnizTermCoverData
#print axioms plainCookLevinQPSideBound_of_leibnizTermCoverData
#print axioms step247UniformFactorRowCoverData_of_leibnizTermCoverData
#print axioms noBoundedSATDeciderAtPaperScale_of_leibnizTermCoverData_TPhi

end PallLean.Paper93.DeepMath.PathB
