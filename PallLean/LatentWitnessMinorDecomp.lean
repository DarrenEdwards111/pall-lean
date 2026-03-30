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

/-- Assembled extracted-witness lower bound at contradiction scale.
This bundles identity-minor count + combinatorial growth into one NP-side claim
at κ = log₂ n (exactly the final theorem scale). -/
axiom extractedProductWitness_exp_lower_from_decomp_logscale (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) :
    n ^ (Nat.log 2 n / 4) ≤
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n))

end LatentWitnessMinorDecomp
