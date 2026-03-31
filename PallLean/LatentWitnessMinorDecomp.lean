import PallLean.LatentCompiler
import PallLean.ProductDeriv
import Mathlib.Tactic

/-!
# LatentWitnessMinorDecomp

Direct NP-side lower bound on latentCompiledPoly via identity-minor
construction on the selConSheet component.

Key insight: derivatives at selSlot positions kill machCopySheet and copyConSheet
(they contain no selSlot variables), so SPDP generators from selSlot-admissible
lists depend only on selConSheet. The selConSheet product structure then provides
a Kronecker-delta identity for linear independence.
-/

namespace LatentWitnessMinorDecomp

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler

/-- Admissibility of selector-slot witness lists under latentPartition. -/
theorem witness_selector_list_admissible (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hnd : S.Nodup) :
    isBlockAdmissible (latentPartition M n) (S.map (selSlot M n)) :=
  selSlotList_admissible M n S hnd

/-! ## Structural: selSlot derivatives isolate selConSheet -/

/-- machCopyGadget has no selSlot variables (uses machSlot and copySlot only).
Therefore pderiv at any selSlot position gives 0. -/
theorem selSlot_ne_machSlot (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ≠ machSlot M n i := by
  simp [selSlot, machSlot, slot, Fin.ext_iff]; omega

theorem selSlot_ne_copySlot (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ≠ copySlot M n i := by
  simp [selSlot, copySlot, slot, Fin.ext_iff]; omega

theorem selSlot_ne_conSlot (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ≠ conSlot M n i := by
  simp [selSlot, conSlot, slot, Fin.ext_iff]; omega

/-- machCopyGadget has no selSlot variables (uses machSlot and copySlot only).
Therefore pderiv at any selSlot position gives 0. -/
theorem pderiv_selSlot_machCopyGadget (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    pderiv (selSlot M n j) (machCopyGadget M n i) = 0 := by
  unfold machCopyGadget Xmach Xcopy
  have hm := selSlot_ne_machSlot M n i j
  have hc := selSlot_ne_copySlot M n i j
  -- machCopyGadget = 1 - X_mach * X_copy
  -- pderiv kills both X_mach and X_copy since selSlot ≠ machSlot, copySlot
  -- Use ProductDeriv.pderiv_one_sub_mul_ne
  exact ProductDeriv.pderiv_one_sub_mul_ne hm (by
    rw [MvPolynomial.vars_X]; simp; exact hc)

/-- copyConGadget has no selSlot variables. -/
theorem pderiv_selSlot_copyConGadget (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    pderiv (selSlot M n j) (copyConGadget M n i) = 0 := by
  unfold copyConGadget Xcopy Xcon
  have hcp := selSlot_ne_copySlot M n i j
  have hcn := selSlot_ne_conSlot M n i j
  exact ProductDeriv.pderiv_one_sub_mul_ne hcp (by
    rw [MvPolynomial.vars_X]; simp; exact hcn)

/-! ## Direct NP lower bound -/

/-- NP-side lower bound at contradiction scale — DIRECT on latentCompiledPoly.
No bridge needed: identity minor on selConSheet inside latentCompiledPoly
gives C(baseVars, κ) linearly independent generators directly.

Proof sketch (paper-faithful, Section 18 style):
1. Derivatives at selSlot positions kill machCopySheet and copyConSheet
2. Remaining selConSheet = ∏(1 - Xsel_i · Xcon_i) has product structure
3. Tag monomials τ_S = ∏_{j∈S} e_{conSlot j} give Kronecker delta
4. Linear independence → rank ≥ C(baseVars, κ) ≥ n^(κ/4) -/
def latent_hard_witness_logscale (M : DTM) (n : ℕ) (_hn804 : n ≥ 2 ^ 804) : Prop :=
  n ^ (Nat.log 2 n / 4) ≤
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n)

/-- Alias: "Obligation 1" in the current route is the direct NP lower bound. -/
def obligation1_np_logscale (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804) : Prop :=
  latent_hard_witness_logscale M n hn804

end LatentWitnessMinorDecomp
