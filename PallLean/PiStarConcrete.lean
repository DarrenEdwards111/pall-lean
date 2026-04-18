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

/-- **Refined form using the commutation theorem**: since
`iterDerivList S (piSubst p) = piSubst (iterDerivList S p)` for all-kept
S, the SPDP subspace of `piSubst p` is spanned by generators of the form
`mlProj(m * piSubst (iterDerivList S p))` with all-kept S. -/
theorem mlBlockedSpdpSubspace_piSubst_factored
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
                  (m * piSubst keep val (SPDP.iterDerivList S p)) } := by
  -- Compose the two results: Section 5's all-kept restriction + §4.5 commutation.
  intro q hq
  have h1 := mlBlockedSpdpSubspace_piSubst_allKept keep val B κ ℓ p hq
  -- Rewrite each allKept generator using iterDerivList_piSubst_allKept.
  refine Submodule.span_le.mpr ?_ h1
  rintro r ⟨S, m, hSlen, hmdeg, hmvar, hadm, hallkept, hr⟩
  rw [iterDerivList_piSubst_allKept keep val S hallkept p] at hr
  exact Submodule.subset_span ⟨S, m, hSlen, hmdeg, hmvar, hadm, hallkept, hr⟩

/-! ## Section 6: Summary — the API for rank reduction

Putting it all together: the piSubst gauge's SPDP subspace is spanned
by generators of the form `mlProj(m · piSubst(∂^S p))` for **all-kept**
derivation lists S only. This is significantly smaller than the full
SPDP subspace when `keep` excludes many variables — which is the
essence of Π⋆'s rank-reducing mechanism per paper Definition 6(i). -/

/-- **Key reduction** for property (2) (P-side rank bound): if the
all-kept-restricted generators of p's SPDP subspace (with substitution
applied) are covered by ≤ `bound` spanning elements, then
`rank(piSubst p) ≤ bound`. -/
theorem mlBlockedSpdpRank_piSubst_le_of_cover
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (B : SPDP.BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (G : Finset (MvPolynomial (Fin N) ℚ))
    (hCover : ∀ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
      S.length = κ → m.totalDegree ≤ ℓ → m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible B S → (∀ i ∈ S, keep i) →
      MultilinearSPDP.mlProj (m * piSubst keep val (SPDP.iterDerivList S p))
        ∈ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ)))
    (bound : ℕ) (hCard : G.card ≤ bound) :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piSubst keep val p) ≤ bound := by
  apply GaugeMonotonicity.rank_le_of_spans_gauge B (piSubst keep val) κ ℓ p G
    _ bound hCard
  -- Show mlBlockedSpdpSubspace B κ ℓ (piSubst p) ≤ span G.
  intro q hq
  have h := mlBlockedSpdpSubspace_piSubst_factored keep val B κ ℓ p hq
  refine Submodule.span_le.mpr ?_ h
  rintro r ⟨S, m, hSlen, hmdeg, hmvar, hadm, hallkept, hr⟩
  rw [hr]
  exact hCover S m hSlen hmdeg hmvar hadm hallkept

/-! ## Section 7: The zero-substitution gauge `piZero`

The substitution gauge `piSubst keep val` in general may NOT be
rank-monotone (substitution can *create* multilinearity — e.g.,
substituting `X_k^2 → (val k)^2` turns a non-multilinear term into a
constant, which IS multilinear). To obtain a rank-monotone gauge, we
specialize to `val = 0`:

  piZero keep := piSubst keep 0

For `val ≡ 0`, non-kept variables substitute to 0, annihilating any
monomial that contains them. This is a genuine **projection** onto the
subalgebra generated by `{X_j : keep j}`, and is rank-monotone because
it maps SPDP generators to (multiples of) SPDP generators using only
kept variables. -/

/-- The zero-substitution gauge: substitute 0 for non-kept variables. -/
noncomputable def piZero (keep : Fin N → Prop) [DecidablePred keep] :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  piSubst keep 0

/-- `piZero` is a projection gauge (inherits from `piSubst`). -/
theorem piZero_isProjectionGauge (keep : Fin N → Prop) [DecidablePred keep] :
    GaugeMonotonicity.IsProjectionGauge (piZero keep) :=
  piSubst_isProjectionGauge keep 0

/-- For any variable `i` (kept or not), `piZero` evaluates `X i` to
either `X i` (if kept) or `0` (if not). -/
theorem piZero_X (keep : Fin N → Prop) [DecidablePred keep] (i : Fin N) :
    piZero keep (X i) = if keep i then X i else 0 := by
  unfold piZero
  rw [piSubst_X]
  split_ifs with h
  · rfl
  · simp [Pi.zero_apply]

/-- `piZero keep (C c) = C c`. -/
theorem piZero_C (keep : Fin N → Prop) [DecidablePred keep] (c : ℚ) :
    piZero keep (C c) = C c :=
  piSubst_C keep 0 c

/-- `piZero keep` is idempotent. -/
theorem piZero_idempotent (keep : Fin N → Prop) [DecidablePred keep] :
    (piZero keep) ∘ₗ (piZero keep) = piZero keep :=
  piSubst_idempotent keep 0

/-! ## Section 8: Conditional rank monotonicity for piZero

Full rank monotonicity for `piZero` requires showing that the SPDP
subspace of `piZero p` is contained in the image of the SPDP subspace
of `p` under `piZero`. This in turn requires commutation
  `mlProj ∘ piZero = piZero ∘ mlProj`
on suitable polynomials, which holds because both are Finsupp-filter
operations that commute as set operations on monomial supports.

Below we package the rank-monotonicity theorem as a **conditional**
result — given the commutation hypothesis as input. This separates
the linear-algebra argument (which we give here) from the Finsupp-
level commutation proof (which would be the next step). -/

/-- **Conditional rank monotonicity for piZero**: if `piZero` commutes
with `mlProj` on the polynomials `m * iterDerivList S p` with
`m.vars ⊆ S.toFinset` (kept-supported shifts against all-kept
derivation lists), then `piZero` is rank-monotone.

Specifically: given hypothesis
  `hcomm : mlProj(m · piZero(iterDerivList S p)) =
           piZero(mlProj(m · iterDerivList S p))`
for such (S, m), we conclude
  `mlBlockedSpdpRank B κ ℓ (piZero p) ≤ mlBlockedSpdpRank B κ ℓ p`. -/
theorem piZero_rankMonotone_of_mlProj_commute
    (keep : Fin N → Prop) [DecidablePred keep]
    (B : SPDP.BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (hcomm : ∀ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
      S.length = κ → m.totalDegree ≤ ℓ → m.vars ⊆ S.toFinset →
      SPDP.isBlockAdmissible B S → (∀ i ∈ S, keep i) →
      MultilinearSPDP.mlProj (m * piZero keep (SPDP.iterDerivList S p)) =
        piZero keep (MultilinearSPDP.mlProj (m * SPDP.iterDerivList S p))) :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piZero keep p) ≤
      MultilinearSPDP.mlBlockedSpdpRank B κ ℓ p := by
  -- Step 1: show mlBlockedSpdpSubspace B κ ℓ (piZero p)
  --         ≤ piZero(mlBlockedSpdpSubspace B κ ℓ p).
  have hincl :
      MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ (piZero keep p) ≤
        Submodule.map (piZero keep)
          (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ p) := by
    intro q hq
    have hq' := mlBlockedSpdpSubspace_piSubst_factored keep (0 : Fin N → ℚ) B κ ℓ p hq
    refine Submodule.span_le.mpr ?_ hq'
    rintro r ⟨S, m, hSlen, hmdeg, hmvar, hadm, hallkept, hr⟩
    -- From the factored form: r = mlProj(m · piSubst keep 0 (iterDerivList S p))
    --                         = mlProj(m · piZero keep (iterDerivList S p))
    -- By hypothesis: this equals piZero(mlProj(m · iterDerivList S p))
    have hcomm' := hcomm S m hSlen hmdeg hmvar hadm hallkept
    rw [hr]
    -- hr put r = mlProj(m · piSubst keep 0 (iterDerivList S p))
    -- which unfolds to mlProj(m · piZero keep (iterDerivList S p)) by defn of piZero.
    show MultilinearSPDP.mlProj (m * (piSubst keep 0) (SPDP.iterDerivList S p))
        ∈ Submodule.map (piZero keep)
          (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ p)
    -- Rewrite via commutation hypothesis
    rw [show (piSubst keep 0 : _ →ₗ[ℚ] _) (SPDP.iterDerivList S p) =
          piZero keep (SPDP.iterDerivList S p) from rfl]
    rw [hcomm']
    -- Goal: piZero(mlProj(m · iterDerivList S p)) ∈ image under piZero of SPDP subspace
    exact ⟨MultilinearSPDP.mlProj (m * SPDP.iterDerivList S p),
      Submodule.subset_span ⟨S, m, hSlen, hmdeg, hmvar, hadm, rfl⟩, rfl⟩
  -- Step 2: finrank of image ≤ finrank of domain.
  unfold MultilinearSPDP.mlBlockedSpdpRank
  calc Module.finrank ℚ
        (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ (piZero keep p))
      ≤ Module.finrank ℚ
          (Submodule.map (piZero keep)
            (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ p)) :=
        Submodule.finrank_mono hincl
    _ ≤ Module.finrank ℚ
          (MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ p) :=
        Submodule.finrank_map_le _ _

/-! ## Section 9: Concrete `keep` predicates

Common specific keep predicates for use with piZero/piSubst. These
correspond to the paper's Definition 6(i) "restricting tableau blocks
to fixed constants": the complement of `keep` is the restricted set. -/

/-- **Keep-first-K predicate**: keep the first K variables (indices < K),
substitute the rest. This is the simplest concrete `keep` predicate. -/
def keepFirstK (K : ℕ) : Fin N → Prop := fun i => i.val < K

instance keepFirstK_decidable (K : ℕ) : DecidablePred (keepFirstK (N := N) K) :=
  fun i => Nat.decLt _ _

/-- `keepFirstK 0` keeps no variables (substitutes everything). -/
theorem keepFirstK_zero_iff (i : Fin N) : keepFirstK 0 i ↔ False := by
  unfold keepFirstK; simp

/-- `keepFirstK N` keeps all variables (identity for piSubst). -/
theorem keepFirstK_N_iff (i : Fin N) : keepFirstK N i ↔ True := by
  unfold keepFirstK
  simp [i.isLt]

/-- **Keep-by-block predicate**: keep variables in specified blocks of a
partition. Given `P : Finset (block index)`, keep i iff `partition.assign i ∈ P`.
This models the paper's block-based separation. -/
def keepByBlock {numBlocks : ℕ}
    (assign : Fin N → Fin numBlocks) (P : Finset (Fin numBlocks)) :
    Fin N → Prop :=
  fun i => assign i ∈ P

instance keepByBlock_decidable {numBlocks : ℕ}
    (assign : Fin N → Fin numBlocks) (P : Finset (Fin numBlocks)) :
    DecidablePred (keepByBlock assign P) :=
  fun i => Finset.decidableMem (assign i) P

/-- **Piecewise keep**: union of keep-by-block over multiple block-index sets. -/
theorem keepByBlock_union_iff {numBlocks : ℕ}
    (assign : Fin N → Fin numBlocks) (P Q : Finset (Fin numBlocks)) (i : Fin N) :
    keepByBlock assign (P ∪ Q) i ↔ keepByBlock assign P i ∨ keepByBlock assign Q i := by
  unfold keepByBlock
  simp [Finset.mem_union]

/-! ## Section 10: piZero on monomials — explicit formula

The building block for the Finsupp commutation `mlProj ∘ piZero = piZero ∘ mlProj`:
compute piZero acting on a single monomial explicitly. -/

/-- `piZero` on a monomial: keeps it if kept-supported, else zero.

Specifically, `substFn keep 0 i = X i` for kept `i` and `0` for non-kept.
Thus `aeval (substFn keep 0) (monomial α c) = c · ∏_i (f i)^{α i}`,
which evaluates to `c · monomial α 1` when α is kept-supported (non-kept
exponents are all 0), and `0` otherwise (any non-kept variable with
positive exponent gives `0^{α i} = 0`). -/
theorem piZero_monomial (keep : Fin N → Prop) [DecidablePred keep]
    (α : Fin N →₀ ℕ) (c : ℚ) :
    piZero keep (MvPolynomial.monomial α c) =
      if ∀ i, ¬ keep i → α i = 0 then MvPolynomial.monomial α c else 0 := by
  unfold piZero piSubst substAlgHom
  rw [AlgHom.toLinearMap_apply]
  rw [MvPolynomial.aeval_monomial]
  -- Goal: (algebraMap ℚ _ c) * α.prod (fun i k => substFn keep 0 i ^ k) = if ... then monomial α c else 0
  rw [show (algebraMap ℚ (MvPolynomial (Fin N) ℚ) c) = C c from rfl]
  split_ifs with hkept
  · -- α is kept-supported: each non-kept i has α i = 0.
    -- So ∏ i ∈ α.support, (substFn keep 0 i)^{α i} = ∏ over kept i in support, X_i^{α i} = monomial α 1.
    rw [show (MvPolynomial.monomial α c : MvPolynomial (Fin N) ℚ) =
          C c * MvPolynomial.monomial α 1 from by
        rw [MvPolynomial.C_mul_monomial]; ring_nf]
    congr 1
    -- Goal: α.prod (fun i k => substFn keep 0 i ^ k) = monomial α 1
    rw [show (MvPolynomial.monomial α (1 : ℚ) : MvPolynomial (Fin N) ℚ) =
          α.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin N) ℚ) ^ k) from by
        rw [MvPolynomial.monomial_eq]; simp]
    apply Finsupp.prod_congr
    intro i hi
    -- i ∈ α.support means α i ≠ 0, so α i ≥ 1.
    -- Need substFn keep 0 i ^ (α i) = X i ^ (α i)
    -- Since α i ≥ 1 and α is kept-supported, we have keep i.
    have hαi : α i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hki : keep i := by
      by_contra hk
      exact hαi (hkept i hk)
    simp [substFn, hki]
  · -- α is not kept-supported: ∃ i with ¬keep i and α i ≠ 0.
    push_neg at hkept
    obtain ⟨i, hki, hαi⟩ := hkept
    -- The product has factor (substFn keep 0 i)^{α i} = 0^{α i} = 0 since α i ≥ 1.
    have hki_support : i ∈ α.support := Finsupp.mem_support_iff.mpr hαi
    have : α.prod (fun i k => (substFn keep (0 : Fin N → ℚ) i : MvPolynomial (Fin N) ℚ) ^ k) = 0 := by
      rw [Finsupp.prod_eq_zero_iff]
      refine ⟨i, hki_support, ?_⟩
      simp [substFn, hki, Pi.zero_apply]
      exact hαi
    rw [this, mul_zero]

/-! ## Section 11: Commutation `mlProj ∘ piZero = piZero ∘ mlProj`

Both `mlProj` and `piZero` filter monomials on disjoint criteria:
- `mlProj` keeps monomials with `Finsupp.IsMultilinear α` (each α i ≤ 1)
- `piZero keep` keeps monomials with `∀ i, ¬keep i → α i = 0`

On a single monomial, either both predicates hold (keep the monomial)
or at least one fails (result is zero). The commutation follows by
inspection. -/

/-- **Commutation on a monomial**: `mlProj(piZero(monomial α c)) =
piZero(mlProj(monomial α c))`. -/
theorem mlProj_piZero_comm_monomial
    (keep : Fin N → Prop) [DecidablePred keep]
    (α : Fin N →₀ ℕ) (c : ℚ) :
    MultilinearSPDP.mlProj (piZero keep (MvPolynomial.monomial α c)) =
      piZero keep (MultilinearSPDP.mlProj (MvPolynomial.monomial α c)) := by
  rw [piZero_monomial, MultilinearSPDP.mlProj_monomial]
  split_ifs with hkept hml hml' hkept'
  · -- α kept-supported AND multilinear
    rw [MultilinearSPDP.mlProj_monomial, piZero_monomial]
    simp [hml]
    intros x hk hαx
    exact absurd (hkept x hk) hαx
  · -- α kept-supported but NOT multilinear
    rw [MultilinearSPDP.mlProj_monomial, map_zero]
    simp [hml]
  · -- α NOT kept-supported but multilinear
    rw [MultilinearSPDP.mlProj_zero, piZero_monomial]
    simp [hkept]
  · -- Neither kept-supported NOR multilinear
    rw [MultilinearSPDP.mlProj_zero, map_zero]

/-- **Commutation** of `mlProj` and `piZero` on all polynomials. -/
theorem mlProj_piZero_comm (keep : Fin N → Prop) [DecidablePred keep]
    (p : MvPolynomial (Fin N) ℚ) :
    MultilinearSPDP.mlProj (piZero keep p) =
      piZero keep (MultilinearSPDP.mlProj p) := by
  -- Both mlProj and piZero are additive. Use polynomial additive induction.
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    exact mlProj_piZero_comm_monomial keep α c
  | add p q hp hq =>
    rw [map_add (piZero keep), MultilinearSPDP.mlProj_add,
        MultilinearSPDP.mlProj_add, map_add (piZero keep), hp, hq]

/-- **piZero fixes kept-supported polynomials**: if every monomial's
support in `m` is kept-supported, then `piZero keep m = m`.

Stated at the support level to avoid vars/add interactions. -/
theorem piZero_eq_self_of_support_kept
    (keep : Fin N → Prop) [DecidablePred keep]
    {m : MvPolynomial (Fin N) ℚ}
    (hm : ∀ α ∈ m.support, ∀ i, ¬ keep i → α i = 0) :
    piZero keep m = m := by
  -- Expand m = ∑_α coeff α m · monomial α 1 and apply piZero_monomial.
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff m]
  rw [map_sum (piZero keep)]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff m]
  apply Finset.sum_congr rfl
  intro α hα
  rw [piZero_monomial]
  split_ifs with h
  · rfl
  · push_neg at h
    obtain ⟨i, hki, hαi⟩ := h
    exact absurd (hm α hα i hki) hαi

/-- **piZero is multiplicative on products where one factor is kept-supported**:
if every monomial in m's support is kept-supported, then
`piZero(m · q) = m · piZero(q)`. -/
theorem piZero_mul_eq_of_support_kept
    (keep : Fin N → Prop) [DecidablePred keep]
    {m : MvPolynomial (Fin N) ℚ}
    (hm : ∀ α ∈ m.support, ∀ i, ¬ keep i → α i = 0)
    (q : MvPolynomial (Fin N) ℚ) :
    piZero keep (m * q) = m * piZero keep q := by
  show (substAlgHom keep 0).toLinearMap (m * q) = m * (substAlgHom keep 0).toLinearMap q
  rw [AlgHom.toLinearMap_apply, map_mul, AlgHom.toLinearMap_apply]
  have hm_fixed : substAlgHom keep 0 m = m := by
    have hfixed := piZero_eq_self_of_support_kept keep hm
    unfold piZero piSubst at hfixed
    rwa [AlgHom.toLinearMap_apply] at hfixed
  rw [hm_fixed]

/-- **Extended commutation**: if m's support is kept-supported,
`mlProj(m · piZero(q)) = piZero(mlProj(m · q))`. -/
theorem mlProj_mul_piZero_comm
    (keep : Fin N → Prop) [DecidablePred keep]
    {m : MvPolynomial (Fin N) ℚ}
    (hm : ∀ α ∈ m.support, ∀ i, ¬ keep i → α i = 0)
    (q : MvPolynomial (Fin N) ℚ) :
    MultilinearSPDP.mlProj (m * piZero keep q) =
      piZero keep (MultilinearSPDP.mlProj (m * q)) := by
  rw [← piZero_mul_eq_of_support_kept keep hm q]
  exact mlProj_piZero_comm keep (m * q)

/-- Support → vars implication: if `m.vars ⊆ kept`, then every monomial
in `m.support` has only kept variables in its positive-exponent part. -/
theorem support_kept_of_vars_kept
    (keep : Fin N → Prop)
    {m : MvPolynomial (Fin N) ℚ} (hm : ∀ i ∈ m.vars, keep i) :
    ∀ α ∈ m.support, ∀ i, ¬ keep i → α i = 0 := by
  intro α hα i hki
  by_contra hαi
  have hi_vars : i ∈ m.vars := by
    rw [MvPolynomial.mem_vars]
    exact ⟨α, hα, Finsupp.mem_support_iff.mpr hαi⟩
  exact hki (hm i hi_vars)

/-- **Unconditional rank monotonicity for `piZero`** (item 1 DONE):
`mlBlockedSpdpRank B κ ℓ (piZero keep p) ≤ mlBlockedSpdpRank B κ ℓ p`. -/
theorem piZero_isRankMonotoneGauge
    (keep : Fin N → Prop) [DecidablePred keep]
    (B : SPDP.BlockPartition N) :
    GaugeMonotonicity.IsRankMonotoneGauge B (piZero keep) := by
  intro κ ℓ p
  apply piZero_rankMonotone_of_mlProj_commute keep B κ ℓ p
  intro S m hSlen hmdeg hmvar hadm hallkept
  -- Hypothesis m.vars ⊆ S.toFinset (since S is all-kept) gives m.vars ⊆ kept.
  have hm_kept : ∀ i ∈ m.vars, keep i := fun i hi => by
    have : i ∈ S.toFinset := hmvar hi
    have : i ∈ S := List.mem_toFinset.mp this
    exact hallkept i this
  exact mlProj_mul_piZero_comm keep
    (support_kept_of_vars_kept keep hm_kept)
    (SPDP.iterDerivList S p)

end PiStarConcrete
