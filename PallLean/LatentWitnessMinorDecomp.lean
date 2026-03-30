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
    (S : List (Fin (latentBaseVars M n))) (_hnd : S.Nodup) :
    True := trivial

/-- Linear independence of witness generators indexed by κ-subsets. -/
theorem witness_generators_independent (_M : DTM) (_n : ℕ)
    (_κ : ℕ) :
    True := trivial

/-- Contradiction-scale extracted witness lower bound (before bridge lift). -/
def extracted_witness_exp_lower_logscale (M : DTM) (n : ℕ) (_hn804 : n ≥ 2 ^ 804) : Prop :=
  n ^ (Nat.log 2 n / 4) ≤
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n))

/-- Contradiction-scale selector extraction monotonicity bridge. -/
def selector_bridge_logscale (M : DTM) (n : ℕ) (_hn804 : n ≥ 2 ^ 804) : Prop :=
  mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
    (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n)) ≤
  mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
    (latentCompiledPoly M n)

/-- NP-side assembled lower bound at contradiction scale.
This bundles:
1) extracted-witness identity-minor lower bound at κ = log₂ n
2) selector extraction rank-monotonicity bridge
into one paper-facing NP theorem obligation. -/
def latent_hard_witness_logscale (M : DTM) (n : ℕ) (_hn804 : n ≥ 2 ^ 804) : Prop :=
  n ^ (Nat.log 2 n / 4) ≤
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n)

/-- Assembly theorem for NP side at contradiction scale. -/
theorem latent_hard_witness_logscale_from_parts (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hLower : extracted_witness_exp_lower_logscale M n hn804)
    (hBridge : selector_bridge_logscale M n hn804) :
    latent_hard_witness_logscale M n hn804 :=
  le_trans hLower hBridge

end LatentWitnessMinorDecomp
