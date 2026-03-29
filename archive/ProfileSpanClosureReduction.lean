import PallLean.ProfileGeneratorReduction
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# ProfileSpanClosureReduction

Final reduction of the profile-side closure target.

A profile slice is a span of explicit allocation-generated polynomials. So to prove the
profile-slice finrank bound, it is enough to exhibit a finite spanning family of those
allocation generators whose cardinality is bounded by the target profile local dimension.
-/

namespace ProfileSpanClosureReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open ProfileGeneratorReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Finite spanning-card theorem for one concrete profile slice. -/
def ProfileSliceHasFiniteSpanningFamily
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin (tseitinNumVars Φ)) F),
    profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
      shift (verifierFactor (F := F) Φ) S hS ρ
      ≤ Submodule.span F (↑G : Set (MvPolynomial (Fin (tseitinNumVars Φ)) F)) ∧
    G.card ≤ profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ) ρ

/-- A finite spanning family of the right cardinality implies the profile-slice closure target. -/
theorem profileSliceSpanClosure_of_finiteSpanningFamily
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (hfin : ProfileSliceHasFiniteSpanningFamily (F := F) Φ κ shift S hS ρ) :
    ProfileSliceSpanClosure (F := F) Φ κ shift S hS ρ := by
  rcases hfin with ⟨G, hspan, hcard⟩
  exact le_trans
    (Submodule.finrank_mono hspan)
    (le_trans
      (Submodule.finrank_span_set_le_card (G.finite_toSet))
      hcard)

end ProfileSpanClosureReduction
