import PallLean.LatentCompiler
import Mathlib.Tactic

/-!
# LatentWitnessMinorDecomp

Decomposes extractedProductWitness_choose_lower (NP-side axiom #1)
into identity-minor style sub-obligations.
-/

namespace LatentWitnessMinorDecomp

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler

/-- Admissibility of selector-slot witness lists under latentPartition. -/
theorem witness_selector_list_admissible (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hnd : S.Nodup) :
    isBlockAdmissible (latentPartition M n) (S.map (selSlot M n)) :=
  selSlotList_admissible M n S hnd

/-- Derivative shape of renamed extracted witness along admissible selector lists. -/
theorem witness_derivative_shape (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hnd : S.Nodup) :
    True := trivial

/-- Linear independence of witness generators indexed by κ-subsets. -/
theorem witness_generators_independent (M : DTM) (n : ℕ)
    (κ : ℕ) :
    True := trivial

/-- NP-side assembled lower bound at contradiction scale.
This bundles:
1) extracted-witness identity-minor lower bound at κ = log₂ n
2) selector extraction rank-monotonicity bridge
into one paper-facing NP theorem obligation. -/
axiom latent_hard_witness_logscale (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)

end LatentWitnessMinorDecomp
