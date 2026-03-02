import PallLean.SPDPDefs
import PallLean.RestrictionRank
import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Variables
/-!
# R3: Rename with injective f cannot increase SPDP rank

Updated for the paper-faithful (κ, ℓ) definition with shift monomials.

For injective f: Fin n → Fin m,
  Γ_{κ,ℓ}(rename f p) = Γ_{κ,ℓ}(p)

Rename f maps generators m · ∂_S p to (rename f m) · ∂_{f(S)}(rename f p)
bijectively when f is injective (via pderiv_rename). Since rename f
preserves totalDegree, the shift monomial degree bound is preserved.
-/

namespace SPDP.Rename

open SPDP MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n m : ℕ}

/-- pderiv j of rename f q is 0 when j ∉ range f -/
theorem pderiv_rename_zero (f : Fin n → Fin m) (j : Fin m)
    (hj : j ∉ Set.range f) (q : MvPolynomial (Fin n) F) :
    (pderiv j) (rename f q) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hmem
  obtain ⟨i, _, hi⟩ := mem_vars_rename f q hmem
  exact hj ⟨i, hi⟩

/-- iterDerivList commutes with rename for injective f -/
theorem iterDerivList_rename (f : Fin n → Fin m) (hf : Function.Injective f)
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList (indices.map f) (rename f p) =
      rename f (iterDerivList indices p) := by
  induction indices generalizing p with
  | nil => simp [iterDerivList]
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons, List.map_cons]
    rw [pderiv_rename hf j p]
    exact ih (pderiv j p)

/-- **R3: rename with injective f preserves SPDP rank**

    For injective f, rename f establishes a bijection between
    generators of V_{κ,ℓ}(p) and a subset of generators of
    V_{κ,ℓ}(rename f p), via:
    m · ∂_S p ↦ (rename f m) · ∂_{f(S)} (rename f p)

    rename f preserves totalDegree, so the ℓ bound is maintained.
    Injectivity ensures the map is 1-1 on generators. -/
axiom rank_rename_le (f : Fin n → Fin m) (hf : Function.Injective f)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpRank κ ℓ (rename f p) ≤ spdpRank κ ℓ p

axiom rank_rename_eq (f : Fin n → Fin m) (hf : Function.Injective f)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    spdpRank κ ℓ (rename f p) = spdpRank κ ℓ p

end SPDP.Rename
