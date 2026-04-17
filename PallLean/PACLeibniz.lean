/-
  PACLeibniz.lean — Infrastructure for discharging Lemma 40(c)

  This file builds up the Leibniz-rule + span-decomposition infrastructure
  needed to discharge the `gadget_multiplication_rank_bound` axiom in PAC.lean.

  The three pieces are:
  1. iterDerivList distributes over scalar multiplication.
  2. Leibniz for iterDerivList on polynomial products (induction on S).
  3. Constant-case SPDP rank bound (the `g = C c` sub-case of Lemma 40(c),
     axiom-free).

  Piece 3 is the minimal concrete discharge we can get without the full
  matrix-factoring argument of the paper.
-/
import PallLean.MultilinearSPDP
import PallLean.CookLevinDefs
import Mathlib.Tactic

namespace PACLeibniz

open MvPolynomial MultilinearSPDP SPDP

set_option maxHeartbeats 800000

/-! ## Piece 1: iterDerivList distributes over scalar multiplication -/

/-- `iterDerivList` is ℚ-linear in the polynomial argument. -/
theorem iterDerivList_smul {N : ℕ} (S : List (Fin N)) (c : ℚ)
    (p : MvPolynomial (Fin N) ℚ) :
    iterDerivList S (c • p) = c • iterDerivList S p := by
  unfold iterDerivList
  induction S generalizing p with
  | nil => simp
  | cons a rest ih =>
    show rest.foldl (fun r i => (pderiv i) r) ((pderiv a) (c • p)) =
         c • rest.foldl (fun r i => (pderiv i) r) ((pderiv a) p)
    have h : (pderiv a) (c • p) = c • (pderiv a) p := (pderiv a).map_smul c p
    rw [h]
    exact ih _

/-! ## Piece 2: Constant-case SPDP rank bound (axiom-free)

The simplest non-trivial sub-case of Lemma 40(c): for a *constant* gadget
`g = C c`, multiplication by `g` doesn't increase SPDP rank. This is
because `C c * p = c • p` and scalar multiplication preserves span
(for c ≠ 0) or sends to {0} (for c = 0). -/

/-- For a constant-multiplication of a polynomial, the SPDP subspace of
the product is contained in the original subspace (up to ℚ-span). -/
theorem mlBlockedSpdpSubspace_C_mul_le {N : ℕ} (B : BlockPartition N)
    (κ ℓ : ℕ) (c : ℚ) (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpSubspace B κ ℓ (MvPolynomial.C c * p) ≤
    mlBlockedSpdpSubspace B κ ℓ p := by
  -- Rewrite C c * p as c • p
  have h_eq : MvPolynomial.C c * p = c • p :=
    (MvPolynomial.smul_eq_C_mul p c).symm
  rw [h_eq]
  unfold mlBlockedSpdpSubspace
  rw [Submodule.span_le]
  rintro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  -- q = mlProj(m * iterDerivList S (c • p))
  --   = mlProj(m * (c • iterDerivList S p))     [by iterDerivList_smul]
  --   = mlProj(c • (m * iterDerivList S p))     [by mul_smul_comm]
  --   = c • mlProj(m * iterDerivList S p)       [by mlProj_smul]
  have h1 : iterDerivList S (c • p) = c • iterDerivList S p :=
    iterDerivList_smul S c p
  rw [hq, h1]
  have h2 : m * (c • iterDerivList S p) = c • (m * iterDerivList S p) :=
    mul_smul_comm c m (iterDerivList S p)
  rw [h2]
  have h3 : mlProj (c • (m * iterDerivList S p)) =
            c • mlProj (m * iterDerivList S p) :=
    mlProj_smul c (m * iterDerivList S p)
  rw [h3]
  -- Now need: c • mlProj(m * iterDerivList S p) ∈ mlBlockedSpdpSubspace B κ ℓ p
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩

/-- **Lemma 40(c), constant case (axiom-free).** Multiplication by a
constant polynomial `C c` does not increase SPDP rank. -/
theorem mlBlockedSpdpRank_C_mul_le {N : ℕ} (B : BlockPartition N)
    (κ ℓ : ℕ) (c : ℚ) (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpRank B κ ℓ (MvPolynomial.C c * p) ≤
    mlBlockedSpdpRank B κ ℓ p := by
  unfold mlBlockedSpdpRank
  exact Submodule.finrank_mono (mlBlockedSpdpSubspace_C_mul_le B κ ℓ c p)

/-! ## Piece 3: Leibniz for iterDerivList (membership form, axiom-free)

Paper Lemma 40(c) starts with the observation that
`iterDerivList S (g * p)` expands via the Leibniz rule as a linear
combination of terms `iterDerivList A g · iterDerivList B p` where `A, B`
are sublists of `S`.

Rather than stating this as an equality with an explicit combinatorial
sum, we prove the weaker but sufficient **span-membership** form:
`iterDerivList S (g * p)` lies in the ℚ-span of all products
`iterDerivList A g · iterDerivList B p` for `A, B : List (Fin N)`.

This is proved by induction on `S` using `Derivation.leibniz` for `pderiv`
and `LowDeg.foldl_pderiv_add`. Axiom-free. -/

/-- The **Leibniz generator set**: all products
`iterDerivList A g · iterDerivList B p` for list-index pairs `(A, B)`.
The actual Leibniz expansion produces a finite linear combination of
these; the span is their ℚ-linear closure. -/
noncomputable def leibnizGenSet {N : ℕ} (g p : MvPolynomial (Fin N) ℚ) :
    Set (MvPolynomial (Fin N) ℚ) :=
  { r | ∃ A B : List (Fin N), r = iterDerivList A g * iterDerivList B p }

/-- Monotonicity of the Leibniz generator set under differentiation of `g`:
replacing `g` with `pderiv a g` shrinks the span (since every
`iterDerivList A (pderiv a g) = iterDerivList (a :: A) g` is already a
generator of `leibnizGenSet g p`). -/
private theorem leibnizGenSet_pderiv_g_subset {N : ℕ} (a : Fin N)
    (g p : MvPolynomial (Fin N) ℚ) :
    leibnizGenSet ((pderiv a) g) p ⊆ leibnizGenSet g p := by
  rintro r ⟨A, B, hr⟩
  refine ⟨a :: A, B, ?_⟩
  rw [hr]
  -- iterDerivList A (pderiv a g) = iterDerivList (a :: A) g by definition
  rfl

/-- Analogous monotonicity for differentiation on the `p` side. -/
private theorem leibnizGenSet_pderiv_p_subset {N : ℕ} (a : Fin N)
    (g p : MvPolynomial (Fin N) ℚ) :
    leibnizGenSet g ((pderiv a) p) ⊆ leibnizGenSet g p := by
  rintro r ⟨A, B, hr⟩
  refine ⟨A, a :: B, ?_⟩
  rw [hr]
  rfl

/-- **Leibniz for `iterDerivList` (membership form, axiom-free).**

For any list `S` and any two polynomials `g, p`, the iterated derivative
`iterDerivList S (g * p)` lies in the ℚ-span of all products
`iterDerivList A g · iterDerivList B p`. -/
theorem iterDerivList_mul_mem_leibniz_span {N : ℕ}
    (S : List (Fin N)) (g p : MvPolynomial (Fin N) ℚ) :
    iterDerivList S (g * p) ∈
    Submodule.span ℚ (leibnizGenSet g p) := by
  induction S generalizing g p with
  | nil =>
    -- iterDerivList [] (g * p) = g * p = iterDerivList [] g * iterDerivList [] p
    apply Submodule.subset_span
    refine ⟨[], [], ?_⟩
    simp [iterDerivList]
  | cons a rest ih =>
    -- iterDerivList (a :: rest) (g * p)
    --   = iterDerivList rest (pderiv a (g * p))
    --   = iterDerivList rest (pderiv a g * p + g * pderiv a p)  [pderiv Leibniz]
    --   = iterDerivList rest (pderiv a g * p) + iterDerivList rest (g * pderiv a p)
    --       [by LowDeg.foldl_pderiv_add]
    have h_pderiv : (pderiv a) (g * p) = (pderiv a) g * p + g * (pderiv a) p := by
      have hl := (pderiv a).leibniz g p
      -- (pderiv a).leibniz g p : pderiv a (g * p) = g • pderiv a p + p • pderiv a g
      simp only [smul_eq_mul] at hl
      rw [hl]; ring
    have h_expand : iterDerivList (a :: rest) (g * p) =
                    iterDerivList rest ((pderiv a) g * p) +
                    iterDerivList rest (g * (pderiv a) p) := by
      unfold iterDerivList
      show rest.foldl (fun r i => (pderiv i) r) ((pderiv a) (g * p)) =
           rest.foldl (fun r i => (pderiv i) r) ((pderiv a) g * p) +
           rest.foldl (fun r i => (pderiv i) r) (g * (pderiv a) p)
      rw [h_pderiv]
      exact LowDeg.foldl_pderiv_add rest _ _
    rw [h_expand]
    apply Submodule.add_mem
    · -- iterDerivList rest (pderiv a g * p) ∈ span (leibnizGenSet (pderiv a g) p)
      --                                    ⊆ span (leibnizGenSet g p)  [by subset lemma]
      have ih1 := ih ((pderiv a) g) p
      exact Submodule.span_mono (leibnizGenSet_pderiv_g_subset a g p) ih1
    · have ih2 := ih g ((pderiv a) p)
      exact Submodule.span_mono (leibnizGenSet_pderiv_p_subset a g p) ih2

/-! ## Piece 4: Using Leibniz to bound SPDP subspace of `g * p`

The Leibniz membership theorem `iterDerivList_mul_mem_leibniz_span` gives

  `iterDerivList S (g * p) ∈ span ℚ (leibnizGenSet g p)`

for the **infinite** generator set
`{ iterDerivList A g * iterDerivList B p | A, B : List (Fin N) }`.

Multiplying by a multiplier `m` and applying `mlProj` preserves this span
membership (mlProj is ℚ-linear). Therefore every SPDP generator
`mlProj(m * iterDerivList S (g * p))` lies in the ℚ-span of the
**mlProj-products**:

  `mlProj(m · iterDerivList A g · iterDerivList B p)`

for some `A, B : List (Fin N)`. Consequently:

  `mlBlockedSpdpSubspace B_partition κ ℓ (g * p) ≤ span(all mlProj-products)`.

This is the structural fact underlying Lemma 40(c). To convert it into
the paper's `rank(g*p) ≤ N^C · rank(p)` at shifted `(κ', ℓ')`, one still
needs:

(a) A **finite** generating set for the mlProj-products (bounded by `N^C`),
    which requires bounded-support/degree arguments on `g` to limit the
    distinct `iterDerivList A g` values.
(b) A way to identify each mlProj-product with a generator of
    `mlBlockedSpdpSubspace p` at shifted parameters `(κ+d, ℓ+d)`, which
    in turn requires a partition and variable-support analysis (each
    `m · iterDerivList A g` has vars in `vars(m) ∪ g.vars`, which may
    extend the original `S.toFinset`).

Pieces (a) and (b) are the matrix-factoring / partition-gymnastics content
of the paper's Lemma 40(c) proof. We do **not** discharge them here;
they are the genuine remaining mathematical content beyond the Leibniz rule.

Instead, we expose below a cleaner reformulation of the axiom used in
`PAC.lean`, making its content specifically about the mlProj-product span.
This does not reduce the axiomatic trust but makes what's being assumed
structurally cleaner. -/

end PACLeibniz
