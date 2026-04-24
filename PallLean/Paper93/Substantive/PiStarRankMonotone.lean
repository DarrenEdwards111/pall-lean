/-
  PallLean/Paper93/Substantive/PiStarRankMonotone.lean

  W7 — Rank-monotonicity of the W4 concrete Π⋆ projection on the
  multilinear blocked SPDP structure.

  ## Scope

  This file proves the substantive inequality

      mlBlockedSpdpRank B κ ℓ (piStarConcrete N p)
        ≤ mlBlockedSpdpRank B κ ℓ p

  for every `p : MvPolynomial (Fin N) ℚ` and every SPDP blocking
  `(B, κ, ℓ)`. The proof is a single application of
  `Submodule.finrank_map_le` (via `Submodule.finrank_mono`) to the
  derivative-SPDP subspace, once we establish the subspace inclusion

      mlBlockedSpdpSubspace B κ ℓ (piStarConcrete N p)
        ≤ Submodule.map (piStarConcrete N) (mlBlockedSpdpSubspace B κ ℓ p).

  The inclusion is proved by case analysis on the underlying derivation
  list `S`:

    * **S nonempty** (`κ ≥ 1`): every generator of the LHS vanishes
      because `iterDerivList S 1 = 0` (derivative of the constant `1`
      annihilates on any nonempty list of pderivs), so the generator is
      `0`, which is the image of `0 ∈ SPDP(p)` under `piStarConcrete N`.

    * **S empty** (`κ = 0`): the constraint `m.vars ⊆ [].toFinset = ∅`
      forces `m = C (constantCoeff m)`. The generator then becomes
      `constantCoeff p • mlProj m = (constantCoeff m * constantCoeff p) • 1`,
      and the preimage `y := mlProj (m * iterDerivList [] p) ∈ SPDP(p)`
      satisfies `piStarConcrete N y = (constantCoeff m * constantCoeff p) • 1`,
      matching the generator.

  We then compose with the Cook--Levin step to deliver the corollary

      mlBlockedSpdpRank B κ ℓ (piStarConcrete n (cookLevinQ M n hn htb hns))
        ≤ mlBlockedSpdpRank B κ ℓ (cookLevinQ M n hn htb hns)

  as a direct specialisation. This is the paper-faithful Route C ⇒
  Route A monotonicity at the rank level: the universal constant-projection
  gauge never increases the SPDP rank of any input polynomial.

  ## Paper citations

    * §7.1 pp. 25–26 — universal gauge `Π⋆` and rank-minimising property.
    * §28.3 pp. 137–138 — rank-collapse term in the N-Frame Lagrangian.
    * Lemma 40(c), Definition 12 — multilinear SPDP rank.
    * §40.2 Theorem 216 p. 203 — P-side Width⇒Rank envelope at the
      paper-faithful compilation output.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms piStar_rank_monotone`:
      [propext, Classical.choice, Quot.sound]
-/

import PallLean.Paper93.Substantive.ConcretePiStar
import PallLean.Paper93.Substantive.RankUnderPiStar
import PallLean.PaperFaithfulCompilation
import PallLean.MultilinearSPDP
import PallLean.GodMoveReal
import PallLean.PACLeibniz
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic

namespace PallLean.Paper93.Substantive

open MvPolynomial

set_option maxHeartbeats 800000

/-! ## Auxiliary lemmas: derivative and projection of the constant `1` -/

/-- `iterDerivList S 1 = 0` on any nonempty derivation list. -/
private theorem iterDerivList_one_of_ne_nil {N : ℕ}
    (S : List (Fin N)) (hS : S ≠ []) :
    SPDP.iterDerivList S (1 : MvPolynomial (Fin N) ℚ) = 0 := by
  cases S with
  | nil => exact absurd rfl hS
  | cons i rest =>
    unfold SPDP.iterDerivList
    simp only [List.foldl_cons]
    have h1 : MvPolynomial.pderiv i (1 : MvPolynomial (Fin N) ℚ) = 0 := by simp
    rw [h1]
    -- foldl from 0 = 0; delegate to the standard helper.
    show rest.foldl (fun r i => MvPolynomial.pderiv i r) 0 = 0
    exact SPDP.foldl_pderiv_zero rest

/-- `mlProj (C c) = C c`: the projection to multilinear monomials fixes
constants, because the zero multidegree is multilinear. -/
private theorem mlProj_C {N : ℕ} (c : ℚ) :
    MultilinearSPDP.mlProj (MvPolynomial.C c : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.C c := by
  have hmon : (MvPolynomial.C c : MvPolynomial (Fin N) ℚ) =
      MvPolynomial.monomial 0 c := by
    rw [MvPolynomial.monomial_zero']
  rw [hmon, MultilinearSPDP.mlProj_monomial]
  have h0 : MultilinearSPDP.Finsupp.IsMultilinear (0 : Fin N →₀ ℕ) := by
    intro i; simp
  simp [h0]

/-- **Constant coefficient of `mlProj q` equals constant coefficient of `q`**.

The zero multidegree is trivially multilinear, so `mlProj` (which filters
Finsupp support to multilinear multidegrees) keeps the constant term
unchanged. -/
private theorem constantCoeff_mlProj {N : ℕ}
    (q : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.constantCoeff (MultilinearSPDP.mlProj q) =
      MvPolynomial.constantCoeff q := by
  classical
  -- Reduce to monomial case via polynomial additive induction.
  induction q using MvPolynomial.induction_on' with
  | monomial α a =>
    -- mlProj of a monomial: keep if multilinear α, else 0.
    rw [MultilinearSPDP.mlProj_monomial]
    split_ifs with hα
    · rfl
    · -- mlProj(monomial α a) = 0. constantCoeff 0 = 0.
      -- Also, constantCoeff(monomial α a) = if α = 0 then a else 0.
      rw [map_zero]
      -- Need to show 0 = constantCoeff(monomial α a).
      -- If α = 0 is multilinear (always true), contradicting ¬hα. So α ≠ 0.
      by_cases hα0 : α = 0
      · subst hα0
        exfalso; apply hα; intro i; simp
      · rw [MvPolynomial.constantCoeff_monomial]
        rw [if_neg hα0]
  | add q r hq hr =>
    rw [map_add, MultilinearSPDP.mlProj_add, map_add, hq, hr]

/-! ## Main inclusion: SPDP(piStar p) ≤ map piStar (SPDP p) -/

/-- **Subspace inclusion**: the multilinear blocked SPDP subspace of
`piStarConcrete N p` is contained in the image under `piStarConcrete N`
of the multilinear blocked SPDP subspace of `p`.

This is the core lemma whose `finrank`-application yields the W7
rank-monotonicity statement. -/
theorem mlBlockedSpdpSubspace_piStarConcrete_le_map
    {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ (piStarConcrete N p) ≤
      Submodule.map (piStarConcrete N)
        (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ p) := by
  -- Unfold the LHS to a span of explicit generators.
  unfold MultilinearSPDP.mlBlockedSpdpSubspace
  rw [Submodule.span_le]
  rintro r ⟨S, m, hSlen, hmdeg, hmvar, hadm, hr⟩
  -- Case split on whether `S` is empty.
  by_cases hS : S = []
  · -- **Case S = []**: the preimage is `y = mlProj(m * iterDerivList [] p)`.
    subst hS
    -- `m.vars ⊆ [].toFinset = ∅`, so m is a constant: m = C (constantCoeff m).
    have hm_vars_empty : m.vars = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hi' : i ∈ ([] : List (Fin N)).toFinset := hmvar hi
      simp at hi'
    -- `m.vars = ∅` implies `m = C (constantCoeff m)`: any nonzero-exponent
    -- monomial would contribute a variable to `m.vars`.
    have hm_const : m = MvPolynomial.C (MvPolynomial.constantCoeff m) := by
      rw [MvPolynomial.constantCoeff_eq]
      apply MvPolynomial.ext
      intro d
      rw [MvPolynomial.coeff_C]
      split_ifs with hd
      · subst hd; rfl
      · by_contra hc
        have hd_support : d ∈ m.support := Finsupp.mem_support_iff.mpr hc
        have hex : ∃ i, d i ≠ 0 := by
          by_contra h'
          push_neg at h'
          apply hd
          ext i
          simp [h' i]
        obtain ⟨i, hdi⟩ := hex
        have hi_vars : i ∈ m.vars :=
          (MvPolynomial.mem_vars i).mpr
            ⟨d, hd_support, Finsupp.mem_support_iff.mpr hdi⟩
        rw [hm_vars_empty] at hi_vars
        exact (Finset.notMem_empty _) hi_vars
    -- Set c' := constantCoeff m, so m = C c'.
    set c' : ℚ := MvPolynomial.constantCoeff m with hc'_def
    -- Preimage y := mlProj(m * p) = mlProj(m * iterDerivList [] p) ∈ SPDP(p).
    refine ⟨MultilinearSPDP.mlProj
              (m * SPDP.iterDerivList ([] : List (Fin N)) p), ?_, ?_⟩
    · -- y is a generator of the SPDP subspace of `p` with S = [], same m.
      apply Submodule.subset_span
      exact ⟨[], m, hSlen, hmdeg, hmvar, hadm, rfl⟩
    · -- Show: piStarConcrete N y = r.
      -- Both sides evaluate to (constantCoeff m * constantCoeff p) • 1.
      have h_iter_empty_p : SPDP.iterDerivList ([] : List (Fin N)) p = p := by
        simp [SPDP.iterDerivList]
      have h_iter_empty : SPDP.iterDerivList ([] : List (Fin N))
          (piStarConcrete N p) = piStarConcrete N p := by
        simp [SPDP.iterDerivList]
      -- Step 1: compute LHS := piStarConcrete N (mlProj(m * iterDerivList [] p))
      -- Unfold iterDerivList [] and piStarConcrete.
      rw [h_iter_empty_p]
      have h_piStar_y : piStarConcrete N
          (MultilinearSPDP.mlProj (m * p)) =
          (MvPolynomial.constantCoeff
            (MultilinearSPDP.mlProj (m * p))) •
              (1 : MvPolynomial (Fin N) ℚ) := rfl
      rw [h_piStar_y]
      -- constantCoeff(mlProj(m * p)) = constantCoeff(m * p) = constantCoeff m * constantCoeff p.
      rw [constantCoeff_mlProj]
      rw [map_mul MvPolynomial.constantCoeff m p]
      -- LHS is now: (constantCoeff m * constantCoeff p) • 1.
      -- Step 2: compute RHS := mlProj(m * iterDerivList [] (piStarConcrete N p)).
      rw [hr, h_iter_empty]
      have hpiStar_eq : piStarConcrete N p =
          (MvPolynomial.constantCoeff p) •
            (1 : MvPolynomial (Fin N) ℚ) := rfl
      rw [hpiStar_eq]
      -- m * (constantCoeff p • 1) = constantCoeff p • m, via mul_smul_comm + mul_one.
      have hmul_smul : m * ((MvPolynomial.constantCoeff p) •
          (1 : MvPolynomial (Fin N) ℚ)) =
          (MvPolynomial.constantCoeff p) • m := by
        rw [mul_smul_comm, mul_one]
      rw [hmul_smul]
      -- mlProj (constantCoeff p • m) = constantCoeff p • mlProj m.
      rw [MultilinearSPDP.mlProj_smul]
      -- RHS is now: constantCoeff p • mlProj m.
      -- Substitute m = C c' (using c' = constantCoeff m). After substitution:
      -- RHS = constantCoeff p • mlProj(C c') = constantCoeff p • C c'.
      rw [hm_const, mlProj_C c']
      -- Finally rewrite C c' as c' • 1 on the RHS and compare.
      rw [MvPolynomial.C_eq_smul_one]
      -- RHS = constantCoeff p • (c' • 1) = (constantCoeff p * c') • 1.
      rw [smul_smul]
      -- Both sides are smul on 1; match scalars. The remaining LHS scalar
      -- `constantCoeff (c' • 1)` evaluates to `c'` because the constant
      -- term of `c' • 1 = C c'` is `c'`.
      have hcc : MvPolynomial.constantCoeff
          ((c' : ℚ) • (1 : MvPolynomial (Fin N) ℚ)) = c' := by
        rw [← MvPolynomial.C_eq_smul_one]
        exact MvPolynomial.constantCoeff_C _ _
      rw [hcc]
      congr 1
      ring
  · -- **Case S ≠ []**: r = 0, and 0 ∈ Submodule.map.
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [map_zero]
    -- Show r = 0 via iterDerivList S (piStarConcrete N p) = 0.
    rw [hr]
    have hpiStar_eq : piStarConcrete N p =
        (MvPolynomial.constantCoeff p) •
          (1 : MvPolynomial (Fin N) ℚ) := rfl
    rw [hpiStar_eq]
    -- iterDerivList S (c • 1) = c • iterDerivList S 1 = c • 0 = 0.
    rw [PACLeibniz.iterDerivList_smul]
    rw [iterDerivList_one_of_ne_nil S hS]
    simp

/-! ## Main theorem: Π⋆ is rank-monotone -/

/-- **Π⋆ is rank-decreasing**: `rank(Π⋆(p)) ≤ rank(p)`.

Core W7 substantive result: the W4 concrete `piStarConcrete`, defined as
the ℚ-linear projection `p ↦ constantCoeff p • 1`, never increases the
multilinear blocked SPDP rank. The proof is an immediate consequence of
the subspace inclusion `mlBlockedSpdpSubspace_piStarConcrete_le_map` via
`Submodule.finrank_mono` and `Submodule.finrank_map_le`. -/
theorem piStar_rank_monotone {N B κ ℓ} (p : MvPolynomial (Fin N) ℚ) :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piStarConcrete N p) ≤
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ p := by
  -- Submodule.finrank_map_le applied to the derivative-SPDP subspace.
  unfold MultilinearSPDP.mlBlockedSpdpRank
  calc Module.finrank ℚ
        (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ (piStarConcrete N p))
      ≤ Module.finrank ℚ
          (Submodule.map (piStarConcrete N)
            (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ p)) :=
        Submodule.finrank_mono
          (mlBlockedSpdpSubspace_piStarConcrete_le_map B κ ℓ p)
    _ ≤ Module.finrank ℚ
          (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ p) :=
        Submodule.finrank_map_le _ _

/-- **Cook--Levin specialisation**: rank of `Π⋆(cookLevinQ M n hn htb hns)`
is at most the rank of `cookLevinQ M n hn htb hns`.

Direct consequence of `piStar_rank_monotone` applied to the paper-faithful
Cook--Levin compiled polynomial from `PaperFaithfulCompilation.cookLevinQ`.
This is the W7 Cook--Levin SPDP structure rank-monotonicity statement. -/
theorem piStar_cookLevinQ_rank_at_most_original
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {B κ ℓ} :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (piStarConcrete n (PaperFaithfulCompilation.cookLevinQ M n hn htb hns)) ≤
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (PaperFaithfulCompilation.cookLevinQ M n hn htb hns) :=
  piStar_rank_monotone _

/-! ## Kernel-only axiom trace -/

#print axioms piStar_rank_monotone
#print axioms piStar_cookLevinQ_rank_at_most_original

end PallLean.Paper93.Substantive
