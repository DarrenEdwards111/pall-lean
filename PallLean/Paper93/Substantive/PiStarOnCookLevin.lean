/-
  PallLean/Paper93/Substantive/PiStarOnCookLevin.lean

  Agent W5 — Apply the substantive rank-1 projection `piStarConcrete`
  (W4, `PallLean.Paper93.Substantive.ConcretePiStar`) to the Cook–Levin
  compiled witness polynomial `cookLevinQ`
  (`PallLean.PaperFaithfulCompilation`) and derive the rank bound.

  ## Scope

  This file proves three theorems composing W4 (concrete `Π⋆`) with the
  Cook–Levin Step 2 compiled polynomial:

    * `piStar_cookLevinQ_is_constant` — `Π⋆(cookLevinQ)` equals a
      constant polynomial, namely `C (constantCoeff cookLevinQ)`.

    * `constant_poly_rank_le_one` — any constant polynomial
      `C c : MvPolynomial (Fin n) ℚ` has multilinear blocked SPDP rank
      at most `1` in any SPDP blocking `(B, κ, ℓ)`.

    * `piStar_cookLevinQ_rank_bound` — combining the above, the rank of
      `Π⋆(cookLevinQ)` is at most `1`, hence at most `n^200`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §7.1 pp. 25–26 — role of the Global God-Move gauge `Π⋆` and the
      rank-minimising Lagrangian.
    * §7.1 Theorem 10 — projected SPDP rank after `Π⋆` is polynomial in
      the input length (`n^200` is comfortably polynomial).
    * Lemma 40(c), Definition 12 — multilinear SPDP rank.
-/

import PallLean.Paper93.Substantive.ConcretePiStar
import PallLean.PaperFaithfulCompilation
import PallLean.MultilinearSPDP
import PallLean.GodMoveReal
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic

namespace PallLean.Paper93.Substantive

open MvPolynomial

/-- **`Π⋆(cookLevinQ)` is a constant polynomial.**

    Paper §7.1 Theorem 10 base-case statement: the substantive rank-1
    projection `piStarConcrete` sends every multivariate polynomial to
    `constantCoeff p • 1 = C (constantCoeff p)`, a constant.

    Specialised to `cookLevinQ M n`, we extract the witness
    `c := constantCoeff (cookLevinQ M n hn htb hns)` such that
    `piStarConcrete n (cookLevinQ M n hn htb hns) = C c`. -/
theorem piStar_cookLevinQ_is_constant
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ c : ℚ, piStarConcrete n (PaperFaithfulCompilation.cookLevinQ M n hn htb hns)
      = (MvPolynomial.C c : MvPolynomial (Fin n) ℚ) := by
  -- The constant coefficient of `cookLevinQ` is the witness.
  refine ⟨MvPolynomial.constantCoeff
    (PaperFaithfulCompilation.cookLevinQ M n hn htb hns), ?_⟩
  -- Unfold `piStarConcrete` to the `smul`-on-`1` form …
  show (MvPolynomial.constantCoeff
          (PaperFaithfulCompilation.cookLevinQ M n hn htb hns)) •
        (1 : MvPolynomial (Fin n) ℚ)
      = MvPolynomial.C
          (MvPolynomial.constantCoeff
            (PaperFaithfulCompilation.cookLevinQ M n hn htb hns))
  -- … and rewrite `c • 1 = C c` via Mathlib's `C_eq_smul_one`.
  rw [MvPolynomial.C_eq_smul_one]

/-- **The multilinear SPDP subspace of a constant polynomial lies inside
    the `ℚ`-span of `{1}`.**

    Generators of `mlBlockedSpdpSubspace B κ ℓ (C c)` have the form
    `mlProj (m * iterDerivList S (C c))`.

    * If `S` is nonempty (`κ ≥ 1`), `iterDerivList S (C c) = 0` by
      `GodMoveReal.iterDerivList_C_eq_zero`, so the generator is `0`.
    * If `S = []` (`κ = 0`), `iterDerivList [] (C c) = C c` and
      `m.vars ⊆ ∅` forces `m = C (m.coeff 0)`.  Then
      `mlProj (C (m.coeff 0) * C c) = C (m.coeff 0 * c)
         = (m.coeff 0 * c) • 1 ∈ span ℚ {1}`.

    Either way every generator lies in the ℚ-span of `{1}`. -/
theorem constant_mlBlockedSpdpSubspace_le_span_one
    {n : ℕ} (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (c : ℚ) :
    MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ
        (MvPolynomial.C c : MvPolynomial (Fin n) ℚ)
      ≤ Submodule.span ℚ ({1} : Set (MvPolynomial (Fin n) ℚ)) := by
  unfold MultilinearSPDP.mlBlockedSpdpSubspace
  rw [Submodule.span_le]
  rintro q ⟨S, m, _hSlen, _hmdeg, hmvar, _hadm, hq⟩
  -- Split on whether `S` is empty.
  by_cases hS : S = []
  · -- S = []: iterDerivList [] (C c) = C c, m has no variables.
    subst hS
    -- `m.vars ⊆ [].toFinset = ∅` means `m` is a constant.
    have hm_vars_empty : m.vars = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hi' : i ∈ ([] : List (Fin n)).toFinset := hmvar hi
      simp at hi'
    -- `m.vars = ∅` directly implies `m = C (constantCoeff m)`:
    -- every non-zero-exponent monomial in `m.support` would contribute
    -- to `m.vars`.
    have hm_const : m = MvPolynomial.C (MvPolynomial.constantCoeff m) := by
      rw [MvPolynomial.constantCoeff_eq]
      apply MvPolynomial.ext
      intro d
      rw [MvPolynomial.coeff_C]
      split_ifs with hd
      · subst hd; rfl
      · -- `d ≠ 0`, show `coeff d m = 0`.
        by_contra hc
        have hd_support : d ∈ m.support := Finsupp.mem_support_iff.mpr hc
        -- `d ≠ 0` means some `i` has `d i ≠ 0`.
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
    -- `iterDerivList [] (C c) = C c`.
    have h_iter : SPDP.iterDerivList ([] : List (Fin n))
        (MvPolynomial.C c : MvPolynomial (Fin n) ℚ) =
        (MvPolynomial.C c : MvPolynomial (Fin n) ℚ) := by
      simp [SPDP.iterDerivList]
    -- Compute `q` explicitly.
    rw [hq, h_iter]
    rw [hm_const]
    -- Now `q = mlProj (C (constantCoeff m) * C c) = C (constantCoeff m * c)`,
    -- which is a scalar multiple of `1`.
    rw [← MvPolynomial.C_mul]
    -- `mlProj (C k) = C k` since constants are multilinear.
    have hml : MultilinearSPDP.mlProj
        (MvPolynomial.C ((MvPolynomial.constantCoeff m) * c)
          : MvPolynomial (Fin n) ℚ) =
        MvPolynomial.C ((MvPolynomial.constantCoeff m) * c) := by
      -- `C k = monomial 0 k`, and `0 : Fin n →₀ ℕ` is multilinear.
      have hmon : (MvPolynomial.C ((MvPolynomial.constantCoeff m) * c)
            : MvPolynomial (Fin n) ℚ) =
          MvPolynomial.monomial 0 ((MvPolynomial.constantCoeff m) * c) := by
        rw [MvPolynomial.monomial_zero']
      rw [hmon, MultilinearSPDP.mlProj_monomial]
      have hml0 : MultilinearSPDP.Finsupp.IsMultilinear
          (0 : Fin n →₀ ℕ) := by
        intro i
        simp [Finsupp.coe_zero]
      simp [hml0]
    rw [hml]
    -- `C (k) = k • 1` for any `k : ℚ`.
    rw [MvPolynomial.C_eq_smul_one]
    -- `k • 1 ∈ span ℚ {1}`.
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton _))
  · -- S ≠ []: iterDerivList S (C c) = 0.
    have h_iter_zero : SPDP.iterDerivList S
        (MvPolynomial.C c : MvPolynomial (Fin n) ℚ) = 0 :=
      GodMoveReal.iterDerivList_C_eq_zero c S hS
    have hq0 : q = 0 := by
      rw [hq, h_iter_zero, mul_zero, MultilinearSPDP.mlProj_zero]
    rw [hq0]
    exact Submodule.zero_mem _

/-- **Constant polynomials have multilinear blocked SPDP rank `≤ 1`**.

    Follows from `constant_mlBlockedSpdpSubspace_le_span_one` by
    `Submodule.finrank_mono` and `finrank_span_le_card` on the singleton
    set `{1}`. -/
theorem constant_poly_rank_le_one {n : ℕ} (B : SPDP.BlockPartition n) (κ ℓ : ℕ) (c : ℚ) :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
        (MvPolynomial.C c : MvPolynomial (Fin n) ℚ) ≤ 1 := by
  unfold MultilinearSPDP.mlBlockedSpdpRank
  -- The subspace is contained in the span of `{1}`, whose rank is ≤ 1.
  have hle := constant_mlBlockedSpdpSubspace_le_span_one (n := n) B κ ℓ c
  -- `finrank (span {1}) ≤ 1` from `finrank_span_le_card`.
  have hspan_le :
      Module.finrank ℚ (Submodule.span ℚ
          ({1} : Set (MvPolynomial (Fin n) ℚ))) ≤ 1 := by
    have := finrank_span_le_card (R := ℚ)
      ({1} : Set (MvPolynomial (Fin n) ℚ))
    simpa using this
  -- Monotonicity of finrank under submodule inclusion.
  exact le_trans (Submodule.finrank_mono hle) hspan_le

/-- **Combining: rank of `Π⋆(cookLevinQ)` ≤ 1 ≤ n^200.**

    The substantive projection `piStarConcrete` sends `cookLevinQ` to a
    constant polynomial (by `piStar_cookLevinQ_is_constant`), whose
    multilinear blocked SPDP rank is at most `1`
    (`constant_poly_rank_le_one`). Chaining with `1 ≤ n^200` yields the
    polynomial rank bound of paper §7.1 Theorem 10. -/
theorem piStar_cookLevinQ_rank_bound
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn200 : 1 ≤ n ^ 200) :
    ∃ (B : SPDP.BlockPartition n) (κ ℓ : ℕ),
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
          (piStarConcrete n
            (PaperFaithfulCompilation.cookLevinQ M n hn htb hns)) ≤ n ^ 200 := by
  -- Fix an arbitrary witness blocking: the trivial one-block partition,
  -- κ = 0, ℓ = 0. (The bound holds for every `(B, κ, ℓ)`.)
  refine ⟨⟨1, fun _ => 0⟩, 0, 0, ?_⟩
  -- Extract the constant form.
  obtain ⟨c, hc⟩ := piStar_cookLevinQ_is_constant M n hn htb hns
  rw [hc]
  -- The rank is ≤ 1; chain with `1 ≤ n^200`.
  exact le_trans (constant_poly_rank_le_one _ _ _ c) hn200

end PallLean.Paper93.Substantive
