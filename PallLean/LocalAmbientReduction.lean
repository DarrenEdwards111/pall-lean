import PallLean.LocalClauseFactorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# LocalAmbientReduction

Paper-faithful reduction of the local clause-factor image theorem to a support-restricted
multilinear ambient theorem.

For a single verifier factor, the remaining irreducible step is:

* show every local image lies in the multilinear ambient on the factor's support;
* bound that ambient by `2^(|support|) ≤ 16`.

This file packages that reduction explicitly.
-/

namespace LocalAmbientReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalClauseFactorSpace
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Support-restricted multilinear ambient space on a finite support set `T`. -/
noncomputable def supportMultilinearAmbient
    {n : ℕ}
    (T : Finset (Fin n)) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | IsMultilinear q ∧ q.vars ⊆ T }

/-- Local support set for a verifier factor. -/
noncomputable def verifierFactorSupport
    (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    Finset (Fin (tseitinNumVars Φ)) :=
  (verifierFactor (F := F) Φ c).vars

/--
The concrete local ambient theorem we still need:
all local clause-factor images lie in the multilinear ambient over the factor support.
-/
def LocalClauseFactorEmbedsInAmbient (Φ : TseitinFormula) : Prop :=
  ∀ (c : Fin Φ.clauses.length) (k : Fin 5),
    localClauseFactorSpace (F := F) Φ c k ≤
      supportMultilinearAmbient (F := F) (verifierFactorSupport (F := F) Φ c)

/--
Finite-dimensional ambient bound on a support-restricted multilinear space.

This is the final constant-dimension endpoint for a single clause factor.
-/
def SupportAmbientFinrankBound {n : ℕ} : Prop :=
  ∀ (T : Finset (Fin n)), T.card ≤ 4 →
    Module.finrank F (supportMultilinearAmbient (F := F) T) ≤ 16

/--
Once local clause-factor images embed in the 4-variable ambient, the local image theorem follows.
-/
theorem localClauseFactorImageBound_of_ambient
    (Φ : TseitinFormula)
    (hembed : LocalClauseFactorEmbedsInAmbient (F := F) Φ)
    (hambient : SupportAmbientFinrankBound (F := F) (n := tseitinNumVars Φ)) :
    LocalClauseFactorImageBound (F := F) Φ := by
  intro c k
  have hsub := hembed c k
  have hcard : (verifierFactorSupport (F := F) Φ c).card ≤ 4 :=
    verifierFactor_vars_card_le_four (F := F) Φ c
  exact le_trans
    (Submodule.finrank_mono hsub)
    (hambient _ hcard)

end LocalAmbientReduction
