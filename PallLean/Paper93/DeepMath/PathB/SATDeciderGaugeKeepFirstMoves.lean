import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeCandidate
import PallLean.CompiledBoolFactorBridge
import Mathlib.Tactic

/-!
# Keep-first moves the real Cook-Levin compiled polynomial

This file closes the remaining certificate exposed in
`SATDeciderGaugeCandidate`: the concrete keep-first projection does not fix the
real product-form `compiledPoly (cook_levin_compilation ...)`.

The witness is the coefficient of the second Cook-Levin variable.  The
keep-first projection kills every monomial containing that variable, while in
the real compiled product that coefficient is `-1`: it comes from the
second booleanity factor and the remaining Cook-Levin factors have constant
term `1` and no linear coefficient.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPower

attribute [local instance] Classical.dec

private lemma coeff_single_X_mul_X {N : Nat} (v i j : Fin N) :
    MvPolynomial.coeff (Finsupp.single v 1)
      (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin N) Rat) = 0 := by
  rw [MvPolynomial.coeff_mul_X']
  by_cases hj : j = v
  · subst hj
    simp [MvPolynomial.coeff_X']
  · have hnot : j ∉ (Finsupp.single v 1).support := by
      rw [Finsupp.mem_support_iff]
      simp [hj]
    simp [hnot]

private lemma coeff_single_cadjFactor_zero {N : Nat} (v i j : Fin N) (c : Rat) :
    MvPolynomial.coeff (Finsupp.single v 1)
      ((1 : MvPolynomial (Fin N) Rat) - MvPolynomial.C c *
        (MvPolynomial.X i * MvPolynomial.X j)) = 0 := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, MvPolynomial.coeff_C_mul,
    coeff_single_X_mul_X]
  have hne : (0 : Fin N →₀ Nat) ≠ Finsupp.single v 1 := by
    intro h
    have := DFunLike.congr_fun h v
    simp at this
  simp [hne]

private lemma coeff_single_mul {N : Nat} (v : Fin N)
    (p q : MvPolynomial (Fin N) Rat) :
    MvPolynomial.coeff (Finsupp.single v 1) (p * q) =
      MvPolynomial.coeff (Finsupp.single v 1) p * MvPolynomial.coeff 0 q +
        MvPolynomial.coeff 0 p * MvPolynomial.coeff (Finsupp.single v 1) q := by
  rw [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single]
  have hanti :
      Finset.antidiagonal 1 = ({(0, 1), (1, 0)} : Finset (Nat × Nat)) := by
    decide
  rw [hanti]
  simp [add_comm]

private lemma coeff_single_ne_zero {N : Nat} (v : Fin N) :
    (0 : Fin N →₀ Nat) ≠ Finsupp.single v 1 := by
  intro h
  have := DFunLike.congr_fun h v
  simp at this

private lemma list_prod_coeff_single_eq_zero {N : Nat} (v : Fin N)
    (ps : List (MvPolynomial (Fin N) Rat))
    (hps : ∀ p ∈ ps, MvPolynomial.coeff (Finsupp.single v 1) p = 0) :
    MvPolynomial.coeff (Finsupp.single v 1) ps.prod = 0 := by
  induction ps with
  | nil =>
      simp [MvPolynomial.coeff_one, coeff_single_ne_zero v]
  | cons p ps ih =>
      rw [List.prod_cons, coeff_single_mul]
      rw [hps p (by simp), ih (by intro q hq; exact hps q (by simp [hq]))]
      simp

/-- Every rest factor product has zero linear coefficient in every variable. -/
theorem restFactorProd_coeff_single_eq_zero (M : DTM) (n : Nat) (v : Fin n) :
    MvPolynomial.coeff (Finsupp.single v 1) (restFactorProd' M n) = 0 := by
  unfold restFactorProd'
  apply list_prod_coeff_single_eq_zero
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨lc, hlc, rfl⟩ := hp
  obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc hlc
  rw [hpoly]
  exact coeff_single_cadjFactor_zero v i ⟨i.val + 1, hi⟩ c

/-- The full booleanity product has linear coefficient `-1` at each variable. -/
theorem boolFactorFullProd_coeff_single (n : Nat) (v : Fin n) :
    MvPolynomial.coeff (Finsupp.single v 1) (boolFactorFullProd n) = (-1 : Rat) := by
  have h :=
    coeff_tag_iterDeriv_boolFactor_prod_general
      (N := n) ({v} : Finset (Fin n)) (∅ : Finset (Fin n))
  simpa [boolFactorFullProd] using h

/-- The keep-first projection kills the second-variable linear coefficient. -/
theorem satDeciderGaugeKeepFirstProjection_coeff_secondVar_image
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat) :
    MvPolynomial.coeff (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
      (satDeciderGaugeKeepFirstProjection M n hn2 htb hns p) = 0 := by
  by_contra hcoeff
  have hmem :
      Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1 ∈
        (satDeciderGaugeKeepFirstProjection M n hn2 htb hns p).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hnot_keep :
      ¬ PiStarConcrete.keepFirstK
          (N := (cook_levin_compilation M n hn2 htb hns).numVars) 1
          (satDeciderGaugeSecondVar M n hn2 htb hns) := by
    simp [PiStarConcrete.keepFirstK, satDeciderGaugeSecondVar]
  have hnotvars :
      satDeciderGaugeSecondVar M n hn2 htb hns ∉
        (satDeciderGaugeKeepFirstProjection M n hn2 htb hns p).vars := by
    unfold satDeciderGaugeKeepFirstProjection PiStarConcrete.piZero
    exact PiStarConcrete.notMem_vars_piSubst
      (PiStarConcrete.keepFirstK 1) 0 hnot_keep p
  have hzero := MvPolynomial.mem_support_notMem_vars_zero hmem hnotvars
  simp at hzero

/-- In the real compiled Cook-Levin product, the second-variable linear
coefficient is `-1`. -/
theorem compiledPoly_coeff_secondVar
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MvPolynomial.coeff (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) = (-1 : Rat) := by
  rw [CompiledBoolFactorBridge.compiledPoly_eq_boolFactorFullProd_mul_rest M n hn2 htb hns]
  rw [coeff_single_mul]
  have hbool := boolFactorFullProd_coeff_single n
    (satDeciderGaugeSecondVar M n hn2 htb hns)
  have hrest0 := restFactorProd'_const_one M n
  have hrest1 := restFactorProd_coeff_single_eq_zero M n
    (satDeciderGaugeSecondVar M n hn2 htb hns)
  rw [hbool, hrest0, hrest1]
  ring

/-- Concrete coefficient witness for the keep-first projection. -/
theorem satDeciderGaugeKeepFirstProjection_compiledPoly_coeff_witness
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ α,
      MvPolynomial.coeff α
          (satDeciderGaugeKeepFirstProjection M n hn2 htb hns
            (compiledPoly (cook_levin_compilation M n hn2 htb hns))) ≠
        MvPolynomial.coeff α
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) := by
  refine ⟨Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1, ?_⟩
  rw [satDeciderGaugeKeepFirstProjection_coeff_secondVar_image,
    compiledPoly_coeff_secondVar]
  norm_num

/-- The keep-first projection moves the real product-form `compiledPoly`. -/
theorem satDeciderGaugeKeepFirstProjection_moves_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFirstProjection M n hn2 htb hns
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠
      compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  intro hfix
  have hcoeff := congrArg
    (fun p => MvPolynomial.coeff
      (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1) p) hfix
  dsimp at hcoeff
  rw [satDeciderGaugeKeepFirstProjection_coeff_secondVar_image,
    compiledPoly_coeff_secondVar] at hcoeff
  norm_num at hcoeff

/-- The concrete keep-first projection satisfies the candidate core. -/
theorem satDeciderGaugeKeepFirstProjection_candidateCore
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeCandidateCore M n hn2 htb hns
      (satDeciderGaugeKeepFirstProjection M n hn2 htb hns) := by
  rw [satDeciderGaugeKeepFirstProjection_candidateCore_iff_moves_compiledPoly]
  exact satDeciderGaugeKeepFirstProjection_moves_compiledPoly M n hn2 htb hns

end PallLean.Paper93.DeepMath.PathB
