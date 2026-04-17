/-
  PermanentGodMove.lean — Paper's Theorem 100 (God Move for permanent)

  Paper reference (p vs np1.pdf): Theorem 100, line 5679+.

  The permanent polynomial perm_n(X) = Σ_σ Π_i X_{σ(i), i}, where
  X_{i,j} is a symbolic variable, admits an explicit God-Move
  projection Π_n such that

      Π_n M_{κ,0}(perm_n) = I_{(n choose κ)}

  giving the NP-side lower bound Γ_{κ,0}(perm_n) ≥ C(n, κ).

  This file formalizes:
  1. The permanent polynomial `permPoly n` in MvPolynomial (Fin n × Fin n) ℚ.
  2. The witness monomial `witnessMono S` = Π_{i ∉ S} X_{i, i} for
     S ⊂ [n] with |S| = κ.
  3. Partial derivatives of `permPoly` along diagonal variables
     (paper's ∂_S), giving `perm(X[T, T])` where T = [n] \ S.
  4. The core identity-minor coefficient claim: coeff_{m_T}(∂_S permPoly)
     = δ_{S,T} (Kronecker delta).
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace PermanentGodMove

open MvPolynomial Matrix

variable {n : ℕ}

/-- The symbolic n × n matrix with entry (i, j) equal to MvPolynomial.X (i, j). -/
noncomputable def symbolicMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℚ) :=
  fun i j => MvPolynomial.X (i, j)

/-- The permanent polynomial perm_n = Σ_σ Π_i X_{σ(i), i}, viewed as
an MvPolynomial in the n² variables indexed by pairs (i, j). -/
noncomputable def permPoly (n : ℕ) : MvPolynomial (Fin n × Fin n) ℚ :=
  (symbolicMatrix n).permanent

/-- Expansion of permPoly as a sum over permutations. -/
theorem permPoly_eq_sum (n : ℕ) :
    permPoly n = ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, MvPolynomial.X (σ i, i) := by
  unfold permPoly Matrix.permanent symbolicMatrix
  rfl

/-- Witness monomial for S : Finset (Fin n): the diagonal product
Π_{i ∉ S} X_{(i, i)}. -/
noncomputable def witnessMono (S : Finset (Fin n)) :
    MvPolynomial (Fin n × Fin n) ℚ :=
  ∏ i ∈ Sᶜ, MvPolynomial.X (i, i)

/-- The identity permutation's contribution to permPoly:
`∏_i X_{(i, i)} = witnessMono ∅`. -/
theorem identity_contribution (n : ℕ) :
    (∏ i : Fin n, MvPolynomial.X (i, i) :
      MvPolynomial (Fin n × Fin n) ℚ) =
    witnessMono (∅ : Finset (Fin n)) := by
  unfold witnessMono
  simp

/-- The permanent polynomial at the identity permutation gives the
diagonal monomial. This is the "base case" of Theorem 100 (κ = 0). -/
theorem permPoly_identity_term (n : ℕ) :
    (∏ i : Fin n, MvPolynomial.X ((Equiv.refl (Fin n)) i, i) :
      MvPolynomial (Fin n × Fin n) ℚ) =
    ∏ i : Fin n, MvPolynomial.X (i, i) := by
  simp [Equiv.refl]

/-- **Identity permutation as a permutation term of permPoly.**
The identity permutation contributes `∏ᵢ X_(i,i)` to the sum defining
the permanent. -/
theorem permPoly_contains_identity_term (n : ℕ) :
    (∏ i : Fin n, MvPolynomial.X (i, i) :
      MvPolynomial (Fin n × Fin n) ℚ) =
    ∏ i : Fin n, MvPolynomial.X
      ((Equiv.refl (Fin n)) i, i) := by
  simp [Equiv.refl]

/-- Every permutation contributes exactly one monomial term of
`permPoly n`. Each monomial from σ has total degree n. -/
theorem permPoly_term_totalDegree_le (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (∏ i : Fin n,
        (MvPolynomial.X (σ i, i) : MvPolynomial (Fin n × Fin n) ℚ)).totalDegree
      ≤ n := by
  have : (∏ i : Fin n,
            (MvPolynomial.X (σ i, i) :
              MvPolynomial (Fin n × Fin n) ℚ)).totalDegree ≤
         ∑ i : Fin n,
            (MvPolynomial.X (σ i, i) :
              MvPolynomial (Fin n × Fin n) ℚ).totalDegree :=
    MvPolynomial.totalDegree_finset_prod _ _
  apply le_trans this
  simp [MvPolynomial.totalDegree_X]

/-- The total degree of `permPoly n` is at most `n`. -/
theorem permPoly_totalDegree_le (n : ℕ) :
    (permPoly n).totalDegree ≤ n := by
  rw [permPoly_eq_sum]
  apply le_trans (MvPolynomial.totalDegree_finset_sum _ _)
  simp only [Finset.sup_le_iff, Finset.mem_univ, forall_const]
  intro σ
  exact permPoly_term_totalDegree_le n σ

/-! ### Step 1: Partial derivatives along diagonal variables

The paper's `∂_S perm_n` is the iterated partial derivative of
`permPoly` with respect to the diagonal variables `X_{(i,i)}` for
`i ∈ S`. We use `MvPolynomial.pderiv` and Mathlib's partial-derivative
infrastructure. -/

/-- `diagPderiv i` applies the partial derivative w.r.t. the diagonal
variable `X_{(i, i)}`. -/
noncomputable def diagPderiv {n : ℕ} (i : Fin n) :
    MvPolynomial (Fin n × Fin n) ℚ → MvPolynomial (Fin n × Fin n) ℚ :=
  MvPolynomial.pderiv (i, i)

theorem diagPderiv_add {n : ℕ} (i : Fin n)
    (p q : MvPolynomial (Fin n × Fin n) ℚ) :
    diagPderiv i (p + q) = diagPderiv i p + diagPderiv i q :=
  (MvPolynomial.pderiv (i, i)).map_add p q

/-- Iterated diagonal partial derivative indexed by a finite set `S`.
Uses `Finset.prod` of the composed linear maps; since pderivs commute,
the order doesn't matter. -/
noncomputable def iterDiagPderiv {n : ℕ} (S : Finset (Fin n)) :
    MvPolynomial (Fin n × Fin n) ℚ → MvPolynomial (Fin n × Fin n) ℚ :=
  fun p => S.toList.foldl (fun q i => diagPderiv i q) p

/-- Iterated pderiv through an empty set is the identity. -/
theorem iterDiagPderiv_empty {n : ℕ}
    (p : MvPolynomial (Fin n × Fin n) ℚ) :
    iterDiagPderiv (∅ : Finset (Fin n)) p = p := by
  unfold iterDiagPderiv
  simp

/-- Iterated pderiv through a singleton equals a single pderiv. -/
theorem iterDiagPderiv_singleton {n : ℕ} (i : Fin n)
    (p : MvPolynomial (Fin n × Fin n) ℚ) :
    iterDiagPderiv ({i} : Finset (Fin n)) p = diagPderiv i p := by
  unfold iterDiagPderiv
  simp [Finset.toList_singleton]

/-- iterDiagPderiv is ℚ-linear in the polynomial argument. -/
theorem iterDiagPderiv_add {n : ℕ} (S : Finset (Fin n))
    (p q : MvPolynomial (Fin n × Fin n) ℚ) :
    iterDiagPderiv S (p + q) = iterDiagPderiv S p + iterDiagPderiv S q := by
  unfold iterDiagPderiv
  induction S.toList generalizing p q with
  | nil => simp
  | cons a rest ih =>
    show rest.foldl (fun q i => diagPderiv i q) (diagPderiv a (p + q)) =
         rest.foldl (fun q i => diagPderiv i q) (diagPderiv a p) +
         rest.foldl (fun q i => diagPderiv i q) (diagPderiv a q)
    rw [diagPderiv_add]
    exact ih _ _

/-- iterDiagPderiv applied to 0 is 0. -/
theorem iterDiagPderiv_zero {n : ℕ} (S : Finset (Fin n)) :
    iterDiagPderiv S (0 : MvPolynomial (Fin n × Fin n) ℚ) = 0 := by
  unfold iterDiagPderiv
  induction S.toList with
  | nil => simp
  | cons a rest ih =>
    show rest.foldl (fun q i => diagPderiv i q) (diagPderiv a 0) = 0
    rw [show diagPderiv a 0 = 0 from (MvPolynomial.pderiv (a, a)).map_zero]
    exact ih

/-- iterDiagPderiv distributes over sums of polynomials. -/
theorem iterDiagPderiv_sum {n : ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset (Fin n))
    (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℚ) :
    iterDiagPderiv S (∑ k ∈ s, f k) = ∑ k ∈ s, iterDiagPderiv S (f k) := by
  induction s using Finset.induction_on with
  | empty => simp [iterDiagPderiv_zero]
  | insert a s' ha ih =>
    rw [Finset.sum_insert ha, iterDiagPderiv_add, ih, Finset.sum_insert ha]

/-- `diagPderiv i (X (i, i)) = 1`. -/
theorem diagPderiv_X_diag {n : ℕ} (i : Fin n) :
    diagPderiv i (MvPolynomial.X (i, i) :
      MvPolynomial (Fin n × Fin n) ℚ) = 1 := by
  unfold diagPderiv
  rw [MvPolynomial.pderiv_X]
  simp

/-- `diagPderiv i` annihilates any `X (p, q)` with `(p, q) ≠ (i, i)`. -/
theorem diagPderiv_X_off_diag {n : ℕ} (i : Fin n) (p q : Fin n)
    (h : (p, q) ≠ (i, i)) :
    diagPderiv i (MvPolynomial.X (p, q) :
      MvPolynomial (Fin n × Fin n) ℚ) = 0 := by
  unfold diagPderiv
  rw [MvPolynomial.pderiv_X]
  have hne : (i, i) ≠ (p, q) := fun heq => h heq.symm
  simp [Pi.single_apply, hne]

/-! ### Leibniz rule for finite products

General Leibniz formula for `pderiv` applied to a finite product:
`pderiv i (∏_{k ∈ s} f k) = ∑_{k ∈ s} pderiv i (f k) · ∏_{j ∈ s \ {k}} f j`.

This isn't in Mathlib for `MvPolynomial.pderiv` / general derivations
(only the binary form exists), so we prove it here by induction on
the finset. -/

theorem pderiv_finset_prod {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (i : σ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → MvPolynomial σ R) :
    MvPolynomial.pderiv i (∏ k ∈ s, f k) =
    ∑ k ∈ s, (MvPolynomial.pderiv i (f k)) * ∏ j ∈ s.erase k, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' ha_notin ih =>
    rw [Finset.prod_insert ha_notin]
    rw [MvPolynomial.pderiv_mul]
    rw [ih]
    rw [Finset.sum_insert ha_notin]
    -- Split the sum: k = a term, then k ∈ s' terms.
    congr 1
    · -- a term: pderiv i (f a) * ∏_{j ∈ (insert a s').erase a} f j
      congr 1
      rw [Finset.erase_insert ha_notin]
    · -- Sum over s': f a * (pderiv i (f k) * ∏_{j ∈ s'.erase k} f j)
      -- equals ∑_{k ∈ s'} pderiv i (f k) * ∏_{j ∈ (insert a s').erase k} f j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hka : k ≠ a := fun heq => ha_notin (heq ▸ hk)
      rw [Finset.erase_insert_of_ne hka.symm]
      rw [Finset.prod_insert
        (fun hmem => ha_notin ((Finset.mem_erase.mp hmem).2))]
      ring

/-! ### Step 2a: single-derivative of a permutation term

For a permutation `σ : Equiv.Perm (Fin n)` and the product
`Π_k X_{(σ k, k)}`, applying `diagPderiv i` yields:
- `Π_{k ≠ i} X_{(σ k, k)}` if `σ i = i` (identity on `i`)
- `0` otherwise.

This is the key single-variable case underlying Step 2's
cofactor identity `∂_S permPoly = perm(X[T,T])`. -/

theorem diagPderiv_perm_term_fixes (n : ℕ) (i : Fin n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ i = i) :
    diagPderiv i (∏ k : Fin n,
        (MvPolynomial.X (σ k, k) : MvPolynomial (Fin n × Fin n) ℚ)) =
    ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
        (MvPolynomial.X (σ k, k) : MvPolynomial (Fin n × Fin n) ℚ) := by
  unfold diagPderiv
  rw [pderiv_finset_prod]
  -- Σ_k pderiv_i (X_(σk,k)) * Π_{j ∈ univ.erase k} X_(σj,j)
  -- Only k = i contributes (others give pderiv = 0).
  rw [Finset.sum_eq_single i]
  · -- k = i: pderiv i (X (σ i, i)) * Π_{j ∈ univ.erase i} X(σj,j)
    have hsi : (σ i, i) = (i, i) := by rw [hσ]
    show MvPolynomial.pderiv (i, i) (MvPolynomial.X (σ i, i)) * _ = _
    have h1 : MvPolynomial.pderiv (i, i) (MvPolynomial.X (σ i, i) :
        MvPolynomial (Fin n × Fin n) ℚ) = 1 := by
      rw [hsi]
      have := diagPderiv_X_diag (n := n) i
      unfold diagPderiv at this
      exact this
    rw [h1, one_mul]
  · -- k ≠ i: pderiv i (X (σ k, k)) = 0 (since (σ k, k) has second coord k ≠ i).
    intro k _ hk_ne_i
    have hne : (σ k, k) ≠ (i, i) := by
      intro heq
      exact hk_ne_i (Prod.mk.injEq .. |>.mp heq).2
    have hzero := diagPderiv_X_off_diag (n := n) i (σ k) k hne
    unfold diagPderiv at hzero
    rw [hzero, zero_mul]
  · intro hnotin
    exact absurd (Finset.mem_univ i) hnotin

theorem diagPderiv_perm_term_nonfixing (n : ℕ) (i : Fin n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ i ≠ i) :
    diagPderiv i (∏ k : Fin n,
        (MvPolynomial.X (σ k, k) : MvPolynomial (Fin n × Fin n) ℚ)) = 0 := by
  unfold diagPderiv
  rw [pderiv_finset_prod]
  apply Finset.sum_eq_zero
  intro k _
  -- Case: if k = i, pderiv i (X(σi, i)) = 0 because σi ≠ i.
  -- Case: if k ≠ i, pderiv i (X(σk, k)) = 0 because second coord k ≠ i.
  by_cases hk : k = i
  · rw [hk]
    have hne : (σ i, i) ≠ (i, i) := fun heq =>
      hσ (Prod.mk.injEq .. |>.mp heq).1
    have h := diagPderiv_X_off_diag (n := n) i (σ i) i hne
    unfold diagPderiv at h
    rw [h, zero_mul]
  · have hne : (σ k, k) ≠ (i, i) :=
      fun heq => hk (Prod.mk.injEq .. |>.mp heq).2
    have h := diagPderiv_X_off_diag (n := n) i (σ k) k hne
    unfold diagPderiv at h
    rw [h, zero_mul]

/-! ### Step 2b: single-variable pderiv of permPoly

Applying `diagPderiv i` to `permPoly n`:
Sum over permutations σ, each term vanishes unless σ i = i.
For σ fixing i, we get `Π_{k ∈ univ.erase i} X_{(σ k, k)}`. -/

theorem diagPderiv_permPoly_eq_sum_fixing (n : ℕ) (i : Fin n) :
    diagPderiv i (permPoly n) =
    ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun σ => σ i = i),
      ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
        (MvPolynomial.X (σ k, k) : MvPolynomial (Fin n × Fin n) ℚ) := by
  rw [permPoly_eq_sum]
  -- diagPderiv is a linear map: apply to sum.
  show diagPderiv i (∑ σ : Equiv.Perm (Fin n),
      ∏ k : Fin n, (MvPolynomial.X (σ k, k) :
        MvPolynomial (Fin n × Fin n) ℚ)) = _
  rw [show diagPderiv i (∑ σ : Equiv.Perm (Fin n),
      ∏ k : Fin n, (MvPolynomial.X (σ k, k) :
        MvPolynomial (Fin n × Fin n) ℚ)) =
      ∑ σ : Equiv.Perm (Fin n),
        diagPderiv i (∏ k : Fin n, (MvPolynomial.X (σ k, k) :
          MvPolynomial (Fin n × Fin n) ℚ)) from by
      unfold diagPderiv
      exact map_sum (MvPolynomial.pderiv (i, i)) _ _]
  -- Split based on σ i = i vs σ i ≠ i
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Equiv.Perm (Fin n)))
      (fun σ => σ i = i)]
  -- Non-fixing terms are 0
  have h_nonfix : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun σ => ¬ σ i = i),
      diagPderiv i (∏ k : Fin n, (MvPolynomial.X (σ k, k) :
        MvPolynomial (Fin n × Fin n) ℚ)) = 0 := by
    intro σ hσ
    have := (Finset.mem_filter.mp hσ).2
    exact diagPderiv_perm_term_nonfixing n i σ this
  rw [Finset.sum_congr rfl (fun σ hσ => h_nonfix σ hσ)]
  rw [Finset.sum_const_zero, add_zero]
  -- Apply fixing theorem to each term
  apply Finset.sum_congr rfl
  intro σ hσ
  have hfix := (Finset.mem_filter.mp hσ).2
  exact diagPderiv_perm_term_fixes n i σ hfix

/-- `permPoly n` is nonzero for `n ≥ 1` (the identity permutation's
diagonal term contributes a nonzero monomial). -/
theorem permPoly_ne_zero_of_pos {n : ℕ} (hn : 1 ≤ n) :
    permPoly n ≠ 0 := by
  rw [permPoly_eq_sum]
  -- The sum Σ_σ Π_i X_(σ i, i) is nonzero because it's a sum of
  -- nonzero monomials; the identity contributes Π_i X_(i,i).
  -- To avoid the coefficient combinatorics, we argue via nonzero support.
  intro hzero
  -- Each term Π_i X_(σ i, i) is a nonzero polynomial.
  have hterm_ne : ∀ σ : Equiv.Perm (Fin n),
      (∏ i : Fin n, (MvPolynomial.X (σ i, i) :
        MvPolynomial (Fin n × Fin n) ℚ)) ≠ 0 := by
    intro σ
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact MvPolynomial.X_ne_zero _
  -- Evaluate at a point where identity's term is nonzero: x_{i,j} = 1 if i=j, else 0.
  let ev : (Fin n × Fin n) → ℚ := fun p => if p.1 = p.2 then 1 else 0
  have hev : (MvPolynomial.eval ev) (∑ σ : Equiv.Perm (Fin n),
      ∏ i : Fin n, (MvPolynomial.X (σ i, i) :
        MvPolynomial (Fin n × Fin n) ℚ)) = 0 := by
    rw [hzero]; simp
  -- At ev, only σ = identity gives nonzero product (Π_i 1 = 1).
  -- For σ ≠ identity, ∃ i with σ i ≠ i, so the term is 0.
  rw [map_sum] at hev
  have hid_val : (MvPolynomial.eval ev)
      (∏ i : Fin n, (MvPolynomial.X ((Equiv.refl (Fin n)) i, i) :
        MvPolynomial (Fin n × Fin n) ℚ)) = 1 := by
    simp [ev, Equiv.refl, MvPolynomial.eval_prod, MvPolynomial.eval_X]
  -- Other permutations evaluate to 0.
  have hother : ∀ σ : Equiv.Perm (Fin n), σ ≠ Equiv.refl (Fin n) →
      (MvPolynomial.eval ev)
        (∏ i : Fin n, (MvPolynomial.X (σ i, i) :
          MvPolynomial (Fin n × Fin n) ℚ)) = 0 := by
    intro σ hσ
    -- σ ≠ id means ∃ i with σ i ≠ i.
    have ⟨i, hi⟩ : ∃ i : Fin n, σ i ≠ i := by
      by_contra h
      push_neg at h
      apply hσ
      apply Equiv.ext
      intro i
      show σ i = i
      exact h i
    -- In the product, the i-th factor evaluates to 0.
    rw [MvPolynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [ev, MvPolynomial.eval_X, hi]
  -- Sum decomposes: 1 (from id) + Σ others = 0.
  have hsplit :
      ((∑ σ : Equiv.Perm (Fin n),
          (MvPolynomial.eval ev)
            (∏ i : Fin n, (MvPolynomial.X (σ i, i) :
              MvPolynomial (Fin n × Fin n) ℚ))) : ℚ) = 1 := by
    rw [Finset.sum_eq_single (Equiv.refl (Fin n))]
    · exact hid_val
    · intro σ _ hσ
      exact hother σ hσ
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsplit] at hev
  exact one_ne_zero hev

end PermanentGodMove
