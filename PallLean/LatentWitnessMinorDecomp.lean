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

private theorem foldl_pderiv_zero_sel {n : ℕ} (l : List (Fin n)) :
    l.foldl (fun q i => pderiv i q) (0 : MvPolynomial (Fin n) ℚ) = 0 := by
  induction l with
  | nil => simp
  | cons a rest ih => simpa [List.foldl] using ih

private theorem pderiv_selSlot_prod_machCopy_zero (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (t : Finset (Fin (latentBaseVars M n))) :
    pderiv (selSlot M n j) (∏ i ∈ t, machCopyGadget M n i) = 0 := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      simp [Finset.prod_insert, ha, MvPolynomial.pderiv_mul,
        pderiv_selSlot_machCopyGadget, ih]

private theorem pderiv_selSlot_prod_copyCon_zero (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n))
    (t : Finset (Fin (latentBaseVars M n))) :
    pderiv (selSlot M n j) (∏ i ∈ t, copyConGadget M n i) = 0 := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      simp [Finset.prod_insert, ha, MvPolynomial.pderiv_mul,
        pderiv_selSlot_copyConGadget, ih]

/-- Any nonempty iterated selSlot-derivative kills machCopySheet. -/
theorem iterDerivList_selSlot_machCopySheet_zero (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hS : S ≠ []) :
    iterDerivList (S.map (selSlot M n)) (machCopySheet M n) = 0 := by
  cases S with
  | nil => contradiction
  | cons a rest =>
      unfold machCopySheet
      simp only [iterDerivList, List.map, List.foldl]
      rw [pderiv_selSlot_prod_machCopy_zero M n a Finset.univ]
      exact foldl_pderiv_zero_sel (rest.map (selSlot M n))

/-- Any nonempty iterated selSlot-derivative kills copyConSheet. -/
theorem iterDerivList_selSlot_copyConSheet_zero (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hS : S ≠ []) :
    iterDerivList (S.map (selSlot M n)) (copyConSheet M n) = 0 := by
  cases S with
  | nil => contradiction
  | cons a rest =>
      unfold copyConSheet
      simp only [iterDerivList, List.map, List.foldl]
      rw [pderiv_selSlot_prod_copyCon_zero M n a Finset.univ]
      exact foldl_pderiv_zero_sel (rest.map (selSlot M n))

/-- For nonempty selector-derivative lists, latentCompiledPoly derivatives reduce to selConSheet. -/
theorem iterDerivList_selSlot_latentCompiled_eq_selCon (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hS : S ≠ []) :
    iterDerivList (S.map (selSlot M n)) (latentCompiledPoly M n) =
      iterDerivList (S.map (selSlot M n)) (selConSheet M n) := by
  unfold latentCompiledPoly
  rw [iterDerivList_add, iterDerivList_add,
    iterDerivList_selSlot_machCopySheet_zero M n S hS,
    iterDerivList_selSlot_copyConSheet_zero M n S hS,
    zero_add, zero_add]

/-! ## selConSheet identity-minor core lemmas -/

private theorem selSlot_not_in_Xcon_vars (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) :
    selSlot M n j ∉ (Xcon M n i).vars := by
  unfold Xcon
  rw [MvPolynomial.vars_X]
  simp [selSlot_ne_conSlot M n i j]

/-- Derivative of selConGadget at its own selector slot. -/
theorem pderiv_selSlot_selConGadget_eq (M : DTM) (n : ℕ)
    (i : Fin (latentBaseVars M n)) :
    pderiv (selSlot M n i) (selConGadget M n i) = -(Xcon M n i) := by
  unfold selConGadget Xsel
  exact ProductDeriv.pderiv_one_sub_mul (selSlot_not_in_Xcon_vars M n i i)

/-- Derivative of selConGadget at a different selector slot is zero. -/
theorem pderiv_selSlot_selConGadget_ne (M : DTM) (n : ℕ)
    (i j : Fin (latentBaseVars M n)) (hij : i ≠ j) :
    pderiv (selSlot M n j) (selConGadget M n i) = 0 := by
  unfold selConGadget Xsel
  have hneq : selSlot M n j ≠ selSlot M n i := by
    intro h
    have hji : j = i := selSlot_injective M n h
    exact hij hji.symm
  exact ProductDeriv.pderiv_one_sub_mul_ne hneq (selSlot_not_in_Xcon_vars M n i j)

/-- Single selector derivative of selConSheet isolates one factor by product rule. -/
theorem pderiv_selSlot_selConSheet (M : DTM) (n : ℕ)
    (j : Fin (latentBaseVars M n)) :
    pderiv (selSlot M n j) (selConSheet M n) =
      (-(Xcon M n j)) * (∏ i ∈ (Finset.univ.erase j), selConGadget M n i) := by
  unfold selConSheet
  rw [ProductDeriv.pderiv_prod_single
      (s := Finset.univ)
      (f := fun i => selConGadget M n i)
      (i := selSlot M n j)
      (k := j)
      (hk := by simp)]
  · simpa [pderiv_selSlot_selConGadget_eq]
  · intro i hi hij
    exact pderiv_selSlot_selConGadget_ne M n i j hij

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
