/-
  PiStarConcrete.lean — concrete variable-substitution gauge
  ============================================================

  ## Goal

  Construct a concrete ℚ-linear endomorphism `piSubst` on
  `MvPolynomial (Fin N) ℚ` and verify it satisfies structural
  properties (idempotency, ℚ-linearity). This is the simplest nontrivial
  candidate for Π⋆ from paper Definition 6:

    > "ΠΦ ... (i) restricting administrative/tableau blocks v to fixed
    >  constants, (ii) projecting to the clause-sheet blocks u, (iii)
    >  applying a fixed block-local relabeling/basis normalization."

  We implement (i) — variable substitution — via MvPolynomial.aeval.

  ## Structure

  Given:
  - A predicate `keep : Fin N → Prop` identifying which variables to keep
  - A substitution value `val : Fin N → ℚ` for variables not kept

  The gauge `piSubst keep val` evaluates each X_i to:
  - X_i if `keep i` holds
  - C (val i) if `keep i` fails

  This is a ℚ-algebra homomorphism; its underlying ℚ-linear map is our
  candidate gauge endomorphism.

  ## Status: ON-CHAIN, axiom-free, no sorry.
-/

import PallLean.MultilinearSPDP
import PallLean.GaugeMonotonicity
import PallLean.IterDerivHelpers
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

namespace PiStarConcrete

open MvPolynomial

variable {N : ℕ}

/-! ## Section 1: The substitution algebra homomorphism -/

/-- **Substitution map**: `i ↦ X i` if `keep i` else `C (val i)`. -/
noncomputable def substFn (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) (i : Fin N) :
    MvPolynomial (Fin N) ℚ :=
  if keep i then X i else C (val i)

/-- **Substitution gauge** (algebra homomorphism form): replace each
non-kept variable by a constant. -/
noncomputable def substAlgHom (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ :=
  aeval (substFn keep val)

/-- **Substitution gauge** (ℚ-linear map form): the underlying ℚ-linear
endomorphism of `substAlgHom`. -/
noncomputable def piSubst (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  (substAlgHom keep val).toLinearMap

/-! ## Section 2: Basic properties -/

/-- `piSubst` evaluates `X i` to either `X i` or `C (val i)`. -/
theorem piSubst_X (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) (i : Fin N) :
    piSubst keep val (X i) = if keep i then X i else C (val i) := by
  unfold piSubst substAlgHom substFn
  rw [AlgHom.toLinearMap_apply, aeval_X]

/-- `piSubst keep val (C c) = C c` (constants are fixed). -/
theorem piSubst_C (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) (c : ℚ) :
    piSubst keep val (C c) = C c := by
  unfold piSubst substAlgHom
  rw [AlgHom.toLinearMap_apply, aeval_C]
  rfl

/-- **`piSubst keep val = id` when all variables are kept.** -/
theorem piSubst_all_kept (keep : Fin N → Prop) [DecidablePred keep] (hall : ∀ i, keep i) (val : Fin N → ℚ) :
    piSubst keep val = LinearMap.id := by
  unfold piSubst substAlgHom substFn
  have : (fun i : Fin N => if keep i then (X i : MvPolynomial (Fin N) ℚ) else C (val i)) =
      X := by
    funext i
    simp [hall i]
  rw [this]
  rw [show (aeval X : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ) =
        AlgHom.id ℚ _ from aeval_X_left]
  rfl

/-- **`substAlgHom` is idempotent as an algebra homomorphism.** -/
theorem substAlgHom_idempotent (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    (substAlgHom keep val).comp (substAlgHom keep val) = substAlgHom keep val := by
  apply MvPolynomial.algHom_ext
  intro i
  -- Both sides applied to X i.
  unfold substAlgHom
  simp only [AlgHom.comp_apply, aeval_X]
  -- Goal: aeval (substFn keep val) (substFn keep val i) = substFn keep val i
  unfold substFn
  by_cases hi : keep i
  · simp [hi]
  · simp [hi]

/-- **`piSubst keep val` is idempotent** (a projection gauge).
Substituting twice is the same as substituting once, because after the
first substitution, each non-kept variable is replaced by a constant,
and constants are fixed by subsequent substitutions. -/
theorem piSubst_idempotent (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    (piSubst keep val) ∘ₗ (piSubst keep val) = piSubst keep val := by
  apply LinearMap.ext
  intro p
  -- Goal: (piSubst keep val) ((piSubst keep val) p) = piSubst keep val p
  show (substAlgHom keep val).toLinearMap ((substAlgHom keep val).toLinearMap p)
        = (substAlgHom keep val).toLinearMap p
  have h := substAlgHom_idempotent keep val
  have : (substAlgHom keep val) ((substAlgHom keep val) p) = substAlgHom keep val p :=
    congrArg (fun f : _ →ₐ[ℚ] _ => f p) h
  simpa [AlgHom.toLinearMap_apply] using this

/-- **`piSubst keep val` is a projection gauge.** -/
theorem piSubst_isProjectionGauge (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ) :
    GaugeMonotonicity.IsProjectionGauge (piSubst keep val) :=
  ⟨piSubst_idempotent keep val⟩

/-! ## Section 3: Rank monotonicity (all-kept trivial case)

When `keep i` holds for every `i`, `piSubst keep val = id` and rank
monotonicity is trivial. This is a sanity check and a concrete instance
of `IsRankMonotoneGauge`. The nontrivial case (some variables not kept)
requires showing that substitution does not increase the SPDP rank —
deeper content developed separately. -/

/-- **All-kept case**: `piSubst` with every variable kept is rank-monotone
(in fact, it's the identity). -/
theorem piSubst_isRankMonotoneGauge_all_kept
    {N : ℕ} (B : SPDP.BlockPartition N)
    (keep : Fin N → Prop) [DecidablePred keep]
    (hall : ∀ i, keep i) (val : Fin N → ℚ) :
    GaugeMonotonicity.IsRankMonotoneGauge B (piSubst keep val) := by
  rw [piSubst_all_kept keep hall val]
  exact GaugeMonotonicity.IsRankMonotoneGauge.id B

/-! ## Section 4: Partial derivative through substitution

For a variable `i` that is **not kept**, the partial derivative of
`piSubst keep val p` with respect to `i` is zero: since `piSubst`
replaces `X_i` by a constant, the result has no `X_i` to differentiate.

This is the key algebraic identity underlying the "rank-reducing"
behavior of the substitution gauge. -/

/-- **Non-kept variables don't appear in `substAlgHom p`**. -/
theorem notMem_vars_substAlgHom
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    {i : Fin N} (hi : ¬ keep i) (p : MvPolynomial (Fin N) ℚ) :
    i ∉ (substAlgHom keep val p).vars := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    show i ∉ (substAlgHom keep val (C c)).vars
    rw [show substAlgHom keep val (C c) = C c from by
      unfold substAlgHom; rw [aeval_C]; rfl]
    simp [MvPolynomial.vars_C]
  | add p q hp hq =>
    show i ∉ (substAlgHom keep val (p + q)).vars
    rw [map_add]
    intro h
    have := MvPolynomial.vars_add_subset _ _ h
    rcases Finset.mem_union.mp this with hp' | hq'
    · exact hp hp'
    · exact hq hq'
  | mul_X p j hp =>
    show i ∉ (substAlgHom keep val (p * X j)).vars
    rw [map_mul]
    intro h
    have := MvPolynomial.vars_mul _ _ h
    rcases Finset.mem_union.mp this with hp' | hj'
    · exact hp hp'
    · -- i ∈ (substAlgHom (X j)).vars. substAlgHom (X j) = substFn keep val j.
      have : substAlgHom keep val (X j) = substFn keep val j := by
        unfold substAlgHom; rw [aeval_X]
      rw [this] at hj'
      unfold substFn at hj'
      by_cases hj : keep j
      · simp [hj, MvPolynomial.vars_X] at hj'
        exact hi (hj' ▸ hj)
      · simp [hj, MvPolynomial.vars_C] at hj'

/-- **Non-kept variables don't appear in `piSubst p`**: for any `p`,
if `i` is not kept, then `i ∉ (piSubst keep val p).vars`. -/
theorem notMem_vars_piSubst
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    {i : Fin N} (hi : ¬ keep i) (p : MvPolynomial (Fin N) ℚ) :
    i ∉ (piSubst keep val p).vars := by
  show i ∉ ((substAlgHom keep val).toLinearMap p).vars
  rw [AlgHom.toLinearMap_apply]
  exact notMem_vars_substAlgHom keep val hi p

/-- **Partial derivative vanishes on non-kept variables**: for any `p`,
if `i` is not kept, then `pderiv i (piSubst keep val p) = 0`. -/
theorem pderiv_piSubst_notKept
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    {i : Fin N} (hi : ¬ keep i) (p : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.pderiv i (piSubst keep val p) = 0 :=
  MvPolynomial.pderiv_eq_zero_of_notMem_vars (notMem_vars_piSubst keep val hi p)

/-- **Iterated derivative along a list with a non-kept element vanishes**. -/
theorem iterDerivList_piSubst_notKept
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (S : List (Fin N)) (hS : ∃ i ∈ S, ¬ keep i)
    (p : MvPolynomial (Fin N) ℚ) :
    SPDP.iterDerivList S (piSubst keep val p) = 0 := by
  obtain ⟨i, hi_mem, hi_keep⟩ := hS
  exact IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars
    S i (piSubst keep val p) hi_mem
    (notMem_vars_piSubst keep val hi_keep p)

/-! ## Section 4.5: Commutation of pderiv with piSubst for kept variables

For a kept variable `i`, the partial derivative commutes with `piSubst`:
  `pderiv i (piSubst p) = piSubst (pderiv i p)`.

This is the other side of the rank-preservation coin: on kept variables,
substitution is "transparent" to differentiation. The proof is by
induction on `p` with a case split on whether the multiplicand `X j` has
`keep j` or not. -/

/-- **Commutation for kept variables** (algebra-hom version). -/
theorem pderiv_substAlgHom_kept
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    {i : Fin N} (hi : keep i) (p : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.pderiv i (substAlgHom keep val p) =
      substAlgHom keep val (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    show MvPolynomial.pderiv i (substAlgHom keep val (C c)) =
      substAlgHom keep val (MvPolynomial.pderiv i (C c))
    rw [show substAlgHom keep val (C c) = C c from by
      unfold substAlgHom; rw [aeval_C]; rfl]
    simp
  | add p q hp hq =>
    show MvPolynomial.pderiv i (substAlgHom keep val (p + q)) =
      substAlgHom keep val (MvPolynomial.pderiv i (p + q))
    rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
    show MvPolynomial.pderiv i (substAlgHom keep val (p * X j)) =
      substAlgHom keep val (MvPolynomial.pderiv i (p * X j))
    -- Use ring-hom for substAlgHom (mul preservation)
    rw [map_mul (substAlgHom keep val) p (X j)]
    -- Leibniz on pderiv for LHS: pderiv i (a * b) = pderiv i a * b + a * pderiv i b
    rw [Derivation.leibniz (MvPolynomial.pderiv i)]
    rw [hp]
    -- substAlgHom (X j) = substFn keep val j
    have hXj : substAlgHom keep val (X j) = substFn keep val j := by
      unfold substAlgHom; rw [aeval_X]
    rw [hXj]
    -- Leibniz on pderiv for RHS argument
    rw [Derivation.leibniz (MvPolynomial.pderiv i) p (X j)]
    rw [map_add]
    simp only [smul_eq_mul, map_mul]
    rw [hXj]
    -- Helper: pderiv i (substFn keep val j) = substAlgHom (pderiv i (X j))
    have hstep : MvPolynomial.pderiv i (substFn keep val j) =
                 substAlgHom keep val (MvPolynomial.pderiv i (X j)) := by
      unfold substFn
      by_cases hj : keep j
      · -- substFn = X j. Both sides: pderiv i (X j) = substAlgHom (pderiv i (X j)).
        -- If keep j, then pderiv i (X j) is either 1 or 0 — a constant — and substAlgHom fixes constants.
        simp only [hj, if_true]
        by_cases hij : i = j
        · subst hij
          rw [MvPolynomial.pderiv_X_self]
          rw [show (substAlgHom keep val) (1 : MvPolynomial (Fin N) ℚ) = 1 from map_one _]
        · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
          rw [show (substAlgHom keep val) (0 : MvPolynomial (Fin N) ℚ) = 0 from map_zero _]
      · -- substFn = C (val j). LHS: pderiv i (C (val j)) = 0.
        simp only [hj, if_false]
        have : MvPolynomial.pderiv i (C (val j) : MvPolynomial (Fin N) ℚ) = 0 :=
          Derivation.map_algebraMap (MvPolynomial.pderiv i) (val j)
        rw [this]
        -- RHS: i ≠ j since ¬keep j but keep i
        have hij : i ≠ j := fun heq => hj (heq ▸ hi)
        rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
        rw [show (substAlgHom keep val) (0 : MvPolynomial (Fin N) ℚ) = 0 from map_zero _]
    rw [hstep]

/-- **Commutation for kept variables** (linear-map version). -/
theorem pderiv_piSubst_kept
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    {i : Fin N} (hi : keep i) (p : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.pderiv i (piSubst keep val p) =
      piSubst keep val (MvPolynomial.pderiv i p) := by
  show MvPolynomial.pderiv i ((substAlgHom keep val).toLinearMap p) =
    (substAlgHom keep val).toLinearMap (MvPolynomial.pderiv i p)
  simp only [AlgHom.toLinearMap_apply]
  exact pderiv_substAlgHom_kept keep val hi p

/-- **Iterated-derivative commutation for all-kept S**:
  `iterDerivList S (piSubst p) = piSubst (iterDerivList S p)` when every
element of S is kept. -/
theorem iterDerivList_piSubst_allKept
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (S : List (Fin N)) (hS : ∀ i ∈ S, keep i) (p : MvPolynomial (Fin N) ℚ) :
    SPDP.iterDerivList S (piSubst keep val p) =
      piSubst keep val (SPDP.iterDerivList S p) := by
  induction S generalizing p with
  | nil => rfl
  | cons i rest ih =>
    have hi : keep i := hS i (by exact List.mem_cons_self)
    have hrest : ∀ j ∈ rest, keep j :=
      fun j hj => hS j (List.mem_cons_of_mem i hj)
    simp only [SPDP.iterDerivList, List.foldl_cons]
    rw [show List.foldl (fun r j => MvPolynomial.pderiv j r)
            (MvPolynomial.pderiv i (piSubst keep val p)) rest =
          SPDP.iterDerivList rest (MvPolynomial.pderiv i (piSubst keep val p)) from rfl]
    rw [show List.foldl (fun r j => MvPolynomial.pderiv j r)
            (MvPolynomial.pderiv i p) rest =
          SPDP.iterDerivList rest (MvPolynomial.pderiv i p) from rfl]
    rw [pderiv_piSubst_kept keep val hi p]
    exact ih hrest (MvPolynomial.pderiv i p)

/-! ## Section 5: SPDP rank bound via all-kept restriction

The SPDP subspace of `piSubst p` is spanned only by generators with
S all-kept. For S not all-kept, the generator is 0. This gives a
characterization of the SPDP subspace after substitution. -/

/-- The SPDP subspace of `piSubst p` is contained in the span of
generators with all-kept S. -/
theorem mlBlockedSpdpSubspace_piSubst_allKept
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (B : SPDP.BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ (piSubst keep val p) ≤
      Submodule.span ℚ
        { q : MvPolynomial (Fin N) ℚ |
          ∃ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
            S.length = κ ∧ m.totalDegree ≤ ℓ ∧
            m.vars ⊆ S.toFinset ∧
            SPDP.isBlockAdmissible B S ∧
            (∀ i ∈ S, keep i) ∧
            q = MultilinearSPDP.mlProj
                  (m * SPDP.iterDerivList S (piSubst keep val p)) } := by
  unfold MultilinearSPDP.mlBlockedSpdpSubspace
  rw [Submodule.span_le]
  rintro q ⟨S, m, hSlen, hmdeg, hmvar, hadm, hq⟩
  -- Case analysis: S is all-kept or not.
  by_cases hallkept : ∀ i ∈ S, keep i
  · -- All-kept: q is in the restricted span directly.
    exact Submodule.subset_span ⟨S, m, hSlen, hmdeg, hmvar, hadm, hallkept, hq⟩
  · -- Some i ∈ S is not kept: iterDerivList S (piSubst p) = 0, so q = 0.
    push_neg at hallkept
    obtain ⟨i, hi_mem, hi_keep⟩ := hallkept
    have h0 : SPDP.iterDerivList S (piSubst keep val p) = 0 :=
      iterDerivList_piSubst_notKept keep val S ⟨i, hi_mem, hi_keep⟩ p
    rw [h0, mul_zero] at hq
    rw [show MultilinearSPDP.mlProj (0 : MvPolynomial (Fin N) ℚ) = 0 from
        MultilinearSPDP.mlProj_zero] at hq
    rw [hq]
    exact Submodule.zero_mem _

end PiStarConcrete
