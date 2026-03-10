/-
  ProfileBridge.lean — Bridge between DisjointLeibniz.iterDeriv and SPDP.iterDerivList
  
  Connects the general disjoint Leibniz factorization theorem to the 
  concrete SPDP definitions, enabling elimination of profile_spanning_set_bound.
-/
import PallLean.DisjointLeibniz
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace ProfileBridge

open MvPolynomial SPDP DisjointLeibniz

/-- The two iterDeriv definitions are identical -/
theorem iterDeriv_eq_iterDerivList {n : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    DisjointLeibniz.iterDeriv S p = SPDP.iterDerivList S p := by
  unfold DisjointLeibniz.iterDeriv SPDP.iterDerivList
  rfl

/-- For a product of factors with disjoint block-based variables,
    iterDerivList factors into per-block derivatives.
    
    This is the key bridge: specializes iterDeriv_prod_disjoint 
    to the SPDP setting with Fin n variables and block partition. -/
theorem iterDerivList_prod_disjoint {n : ℕ} {F : Type*} [CommRing F] [DecidableEq F]
    {R : ℕ} (B : BlockPartition n)
    (f : Fin R → MvPolynomial (Fin n) F)
    (block : Fin R → Fin n → Prop) [∀ c, DecidablePred (block c)]
    (hf_vars : ∀ c, ∀ v ∈ (f c).vars, block c v)
    (hdisjoint : ∀ c₁ c₂, c₁ ≠ c₂ → ∀ v, block c₁ v → ¬ block c₂ v)
    (S : List (Fin n)) (hS : ∀ x ∈ S, ∃ c, block c x) :
    iterDerivList S (Finset.univ.prod f) =
      Finset.univ.prod (fun c => iterDerivList (S.filter (block c)) (f c)) := by
  rw [← iterDeriv_eq_iterDerivList]
  have : ∀ c, iterDerivList (S.filter (block c)) (f c) =
      iterDeriv (S.filter (block c)) (f c) := fun c => iterDeriv_eq_iterDerivList _ _
  simp_rw [this]
  exact iterDeriv_prod_disjoint f Finset.univ block
    (fun c _ => hf_vars c)
    (fun c₁ _ c₂ _ hne => hdisjoint c₁ c₂ hne)
    S (fun x hx => let ⟨c, hc⟩ := hS x hx; ⟨c, Finset.mem_univ c, hc⟩)

/-! ## Per-block derivative space bound

    Each clause factor f_c = 1 - z_c · V_c has at most 5 variables 
    (4 clause variables + 1 selector). In the multilinear (Boolean) setting,
    f_c has at most 2^5 = 32 monomials. Taking any number of derivatives
    can only reduce the number of monomials (each pderiv maps a monomial 
    to 0 or 1 monomial). So iterDerivList S f_c always has ≤ 32 monomials,
    hence lies in a space of dimension ≤ 32.
    
    More precisely: the set of all possible iterDerivList S f_c as S varies
    over all sublists is finite (at most 2^5 possible derivative sequences 
    on 5 variables, though many give the same result). -/

-- The span of all iterDerivList outputs is finite-dimensional with bounded dimension.

end ProfileBridge
