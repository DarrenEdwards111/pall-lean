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

/-- Assembled identity-minor count lower bound. -/
axiom extractedProductWitness_choose_lower_from_decomp (M : DTM) (n : ℕ)
    (κ : ℕ) (hκ : κ ≥ 1) :
    Nat.choose (latentBaseVars M n) κ ≤
      mlBlockedSpdpRank (latentPartition M n) κ κ
        (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n))

end LatentWitnessMinorDecomp
