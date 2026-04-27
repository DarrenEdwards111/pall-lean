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

private lemma coeff_single_two_X_mul_X {N : Nat} (v i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.coeff (Finsupp.single v 2)
      (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin N) Rat) = 0 := by
  rw [MvPolynomial.coeff_mul_X']
  by_cases hj : j = v
  · subst hj
    have hmem : j ∈ (Finsupp.single j 2).support := by
      rw [Finsupp.mem_support_iff]
      simp
    rw [if_pos hmem]
    rw [MvPolynomial.coeff_X', if_neg]
    intro h
    have hval := DFunLike.congr_fun h j
    simp [hij] at hval
  · have hnot : j ∉ (Finsupp.single v 2).support := by
      rw [Finsupp.mem_support_iff]
      simp [hj]
    simp [hnot]

private lemma coeff_single_two_cadjFactor_zero {N : Nat}
    (v i j : Fin N) (hij : i ≠ j) (c : Rat) :
    MvPolynomial.coeff (Finsupp.single v 2)
      ((1 : MvPolynomial (Fin N) Rat) - MvPolynomial.C c *
        (MvPolynomial.X i * MvPolynomial.X j)) = 0 := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one, MvPolynomial.coeff_C_mul,
    coeff_single_two_X_mul_X v i j hij]
  have hne : (0 : Fin N →₀ Nat) ≠ Finsupp.single v 2 := by
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

private lemma coeff_single_two_mul {N : Nat} (v : Fin N)
    (p q : MvPolynomial (Fin N) Rat) :
    MvPolynomial.coeff (Finsupp.single v 2) (p * q) =
      MvPolynomial.coeff (Finsupp.single v 1) p *
          MvPolynomial.coeff (Finsupp.single v 1) q +
        (MvPolynomial.coeff (Finsupp.single v 2) q * MvPolynomial.coeff 0 p +
          MvPolynomial.coeff (Finsupp.single v 2) p * MvPolynomial.coeff 0 q) := by
  rw [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single]
  have hanti :
      Finset.antidiagonal 2 =
        ({(0, 2), (1, 1), (2, 0)} : Finset (Nat × Nat)) := by
    decide
  rw [hanti]
  simp only [Finset.map_insert, Finset.map_singleton]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_singleton]
      simp [Function.Embedding.prodMap]
      ring
    · intro hmem
      unfold Function.Embedding.prodMap at hmem
      simp only [Function.Embedding.coeFn_mk, Prod.map_apply] at hmem
      simp at hmem
  · intro hmem
    unfold Function.Embedding.prodMap at hmem
    simp only [Function.Embedding.coeFn_mk, Prod.map_apply] at hmem
    simp at hmem
    rcases hmem with ⟨hzero, _⟩
    have hval := congrArg (fun a : Fin N →₀ Nat => a v) hzero
    simp at hval

private lemma coeff_single_ne_zero {N : Nat} (v : Fin N) :
    (0 : Fin N →₀ Nat) ≠ Finsupp.single v 1 := by
  intro h
  have := DFunLike.congr_fun h v
  simp at this

private lemma coeff_single_two_ne_zero {N : Nat} (v : Fin N) :
    (0 : Fin N →₀ Nat) ≠ Finsupp.single v 2 := by
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

private lemma list_prod_coeff_single_two_eq_zero {N : Nat} (v : Fin N)
    (ps : List (MvPolynomial (Fin N) Rat))
    (hps1 : ∀ p ∈ ps, MvPolynomial.coeff (Finsupp.single v 1) p = 0)
    (hps2 : ∀ p ∈ ps, MvPolynomial.coeff (Finsupp.single v 2) p = 0) :
    MvPolynomial.coeff (Finsupp.single v 2) ps.prod = 0 := by
  induction ps with
  | nil =>
      simp [MvPolynomial.coeff_one, coeff_single_two_ne_zero v]
  | cons p ps ih =>
      rw [List.prod_cons, coeff_single_two_mul]
      rw [hps2 p (by simp),
        list_prod_coeff_single_eq_zero v ps
          (by intro q hq; exact hps1 q (by simp [hq])),
        hps1 p (by simp),
        ih
          (by intro q hq; exact hps1 q (by simp [hq]))
          (by intro q hq; exact hps2 q (by simp [hq]))]
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

/-- Every rest factor product has zero pure-square coefficient in every
variable.  Each nonconstant rest factor contributes a mixed edge monomial, so
no exact `X_v^2` monomial can be formed without extra variables. -/
theorem restFactorProd_coeff_single_two_eq_zero (M : DTM) (n : Nat) (v : Fin n) :
    MvPolynomial.coeff (Finsupp.single v 2) (restFactorProd' M n) = 0 := by
  unfold restFactorProd'
  apply list_prod_coeff_single_two_eq_zero
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨lc, hlc, rfl⟩ := hp
    obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc hlc
    rw [hpoly]
    exact coeff_single_cadjFactor_zero v i ⟨i.val + 1, hi⟩ c
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨lc, hlc, rfl⟩ := hp
    obtain ⟨c, i, hi, hpoly⟩ := rest_constraint_cadj_form M n lc hlc
    rw [hpoly]
    have hij : i ≠ ⟨i.val + 1, hi⟩ := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    exact coeff_single_two_cadjFactor_zero v i ⟨i.val + 1, hi⟩ hij c

/-- The full booleanity product has linear coefficient `-1` at each variable. -/
theorem boolFactorFullProd_coeff_single (n : Nat) (v : Fin n) :
    MvPolynomial.coeff (Finsupp.single v 1) (boolFactorFullProd n) = (-1 : Rat) := by
  have h :=
    coeff_tag_iterDeriv_boolFactor_prod_general
      (N := n) ({v} : Finset (Fin n)) (∅ : Finset (Fin n))
  simpa [boolFactorFullProd] using h

private theorem coeff_single_two_boolFactor {N : Nat} (v : Fin N) :
    MvPolynomial.coeff (Finsupp.single v 2)
      (boolFactor N v : MvPolynomial (Fin N) Rat) = 1 := by
  unfold boolFactor
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
  have hzero : MvPolynomial.coeff (Finsupp.single v 2)
      (MvPolynomial.X v * (1 - MvPolynomial.X v) : MvPolynomial (Fin N) Rat) = -1 := by
    rw [mul_sub, mul_one, MvPolynomial.coeff_sub]
    have hlinear : MvPolynomial.coeff (Finsupp.single v 2)
        (MvPolynomial.X v : MvPolynomial (Fin N) Rat) = 0 := by
      rw [MvPolynomial.coeff_X', if_neg]
      intro h
      have hv := DFunLike.congr_fun h v
      simp at hv
    have hsq : MvPolynomial.coeff (Finsupp.single v 2)
        (MvPolynomial.X v * MvPolynomial.X v : MvPolynomial (Fin N) Rat) = 1 := by
      have hmono : (MvPolynomial.X v * MvPolynomial.X v : MvPolynomial (Fin N) Rat) =
          MvPolynomial.monomial (Finsupp.single v 2) 1 := by
        show (MvPolynomial.monomial (Finsupp.single v 1) 1 *
          MvPolynomial.monomial (Finsupp.single v 1) 1 :
          MvPolynomial (Fin N) Rat) = _
        rw [MvPolynomial.monomial_mul, mul_one]
        have hpow :
            Finsupp.single v 1 + Finsupp.single v 1 =
              (Finsupp.single v 2 : Fin N →₀ Nat) := by
          ext i
          by_cases hi : i = v
          · subst hi
            simp
          · simp [hi]
        rw [hpow]
      rw [hmono, MvPolynomial.coeff_monomial, if_pos rfl]
    rw [hlinear, hsq]
    ring
  have hne : (0 : Fin N →₀ Nat) ≠ Finsupp.single v 2 := coeff_single_two_ne_zero v
  rw [if_neg hne, hzero]
  ring

private theorem monomSupportedIn_single_two {N : Nat} (v : Fin N) :
    CoeffDisjoint.monomSupportedIn (Finsupp.single v 2) ({v} : Set (Fin N)) := by
  intro x hx
  rw [Finsupp.mem_support_iff] at hx
  simp only [Finsupp.single_apply] at hx
  split_ifs at hx with h
  · exact Set.mem_singleton_iff.mpr h.symm
  · exact absurd rfl hx

/-- The full booleanity product has pure-square coefficient `1` at each
variable. -/
theorem boolFactorFullProd_coeff_single_two (n : Nat) (v : Fin n) :
    MvPolynomial.coeff (Finsupp.single v 2) (boolFactorFullProd n) = (1 : Rat) := by
  unfold boolFactorFullProd
  let m : Fin n -> Fin n →₀ Nat := fun i =>
    if i = v then Finsupp.single v 2 else 0
  have hsum : (∑ i ∈ Finset.univ, m i) = Finsupp.single v 2 := by
    ext x
    rw [CoeffDisjoint.finset_sum_apply]
    by_cases hx : x = v
    ·
      rw [Finset.sum_eq_single v]
      · simp [m, hx]
      · intro b _ hb
        simp [m, hb]
      · intro hv
        simp at hv
    · have hzero : ∀ i : Fin n, (m i) x = 0 := by
        intro i
        by_cases hi : i = v
        · simp [m, hi, hx]
        · simp [m, hi]
      rw [Finset.sum_eq_zero]
      · simp [hx]
      · intro i _
        exact hzero i
  rw [← hsum]
  rw [CoeffDisjoint.coeff_finset_prod_disjoint
    (s := Finset.univ)
    (f := fun i => boolFactor n i)
    (S := fun i => ({i} : Set (Fin n)))
    (m := m)
    (hf := fun i _ => usesOnly_boolFactor i)
    (hdisj := singleton_pairwiseDisjoint Finset.univ)
    (hm := fun i _ => by
      by_cases hi : i = v
      · simpa [m, hi] using monomSupportedIn_single_two v
      · simpa [m, hi] using monomSupportedIn_zero ({i} : Set (Fin n)))]
  apply Finset.prod_eq_one
  intro i _
  by_cases hi : i = v
  · simpa [m, hi] using coeff_single_two_boolFactor v
  · simp [m, hi, coeff_zero_boolFactor]

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

/-- In the real compiled Cook-Levin product, the second-variable pure-square
coefficient is `1`.  This non-multilinear coefficient separates the concrete
NP head row from any multilinear monomial tail. -/
theorem compiledPoly_coeff_secondVar_square
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    MvPolynomial.coeff (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 2)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) = (1 : Rat) := by
  rw [CompiledBoolFactorBridge.compiledPoly_eq_boolFactorFullProd_mul_rest M n hn2 htb hns]
  rw [coeff_single_two_mul]
  have hbool2 := boolFactorFullProd_coeff_single_two n
    (satDeciderGaugeSecondVar M n hn2 htb hns)
  have hbool1 := boolFactorFullProd_coeff_single n
    (satDeciderGaugeSecondVar M n hn2 htb hns)
  have hrest0 := restFactorProd'_const_one M n
  have hrest1 := restFactorProd_coeff_single_eq_zero M n
    (satDeciderGaugeSecondVar M n hn2 htb hns)
  have hrest2 := restFactorProd_coeff_single_two_eq_zero M n
    (satDeciderGaugeSecondVar M n hn2 htb hns)
  rw [hbool2, hbool1, hrest0, hrest1, hrest2]
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
