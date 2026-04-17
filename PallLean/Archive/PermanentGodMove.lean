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

/-- Two `pderiv`s on MvPolynomial commute. Direct proof via monomial
induction (adapted from `IterDerivHelpers.pderiv_comm`). -/
theorem pderiv_comm_general {σ : Type*} [DecidableEq σ]
    (a b : σ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.pderiv a (MvPolynomial.pderiv b p) =
    MvPolynomial.pderiv b (MvPolynomial.pderiv a p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    simp only [MvPolynomial.pderiv_monomial]
    change MvPolynomial.monomial _ _ = MvPolynomial.monomial _ _
    have key : ∀ (x y : σ),
        (s - Finsupp.single x 1 - Finsupp.single y 1 : σ →₀ ℕ)
        = (s - Finsupp.single y 1 - Finsupp.single x 1 : σ →₀ ℕ) := by
      intro x y
      ext k
      simp only [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h1 h2
      · subst h1; subst h2; omega
      · omega
      · omega
      · rfl
    rw [key b a]
    congr 1
    simp only [Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hba : b = a
    · subst hba; ring
    · have hab' : ¬(a = b) := Ne.symm hba
      simp only [hba, hab', ↓reduceIte, Nat.sub_zero]
      ring
  | add p q hp hq =>
    simp only [map_add, hp, hq]

/-- Two `diagPderiv`s commute. -/
theorem diagPderiv_commute {n : ℕ} (i j : Fin n)
    (p : MvPolynomial (Fin n × Fin n) ℚ) :
    diagPderiv i (diagPderiv j p) = diagPderiv j (diagPderiv i p) := by
  unfold diagPderiv
  exact pderiv_comm_general (i, i) (j, j) p

/-- Foldl of commuting operations over a List.Perm gives the same result. -/
private theorem foldl_diagPderiv_perm {n : ℕ} {l l' : List (Fin n)}
    (h : l.Perm l') (p : MvPolynomial (Fin n × Fin n) ℚ) :
    l.foldl (fun q i => diagPderiv i q) p =
    l'.foldl (fun q i => diagPderiv i q) p := by
  induction h generalizing p with
  | nil => rfl
  | cons a _ ih =>
    show (_ : List _).foldl _ _ = _
    dsimp only [List.foldl]
    exact ih _
  | swap a b rest =>
    dsimp only [List.foldl]
    rw [diagPderiv_commute a b p]
  | trans _ _ ih1 ih2 => exact (ih1 p).trans (ih2 p)

/-- diagPderiv i commutes with foldl of diagPderivs over a list. -/
private theorem diagPderiv_foldl_commute {n : ℕ} (i : Fin n)
    (l : List (Fin n)) (p : MvPolynomial (Fin n × Fin n) ℚ) :
    diagPderiv i (l.foldl (fun q j => diagPderiv j q) p) =
    l.foldl (fun q j => diagPderiv j q) (diagPderiv i p) := by
  induction l generalizing p with
  | nil => rfl
  | cons a rest ih =>
    show diagPderiv i (rest.foldl (fun q j => diagPderiv j q) (diagPderiv a p)) =
         rest.foldl (fun q j => diagPderiv j q) (diagPderiv a (diagPderiv i p))
    rw [ih]
    congr 1
    exact diagPderiv_commute i a p

/-- Unfolding: `iterDiagPderiv (insert i S) p = diagPderiv i (iterDiagPderiv S p)`
when `i ∉ S`. Uses `List.Perm` for `(insert i S).toList`. -/
theorem iterDiagPderiv_insert {n : ℕ} {i : Fin n} {S : Finset (Fin n)}
    (hi : i ∉ S) (p : MvPolynomial (Fin n × Fin n) ℚ) :
    iterDiagPderiv (insert i S) p = diagPderiv i (iterDiagPderiv S p) := by
  unfold iterDiagPderiv
  have hperm : (insert i S).toList.Perm (i :: S.toList) :=
    Finset.toList_insert hi
  rw [foldl_diagPderiv_perm hperm]
  -- Goal: List.foldl (...) p (i :: S.toList) = diagPderiv i (S.toList.foldl (...) p)
  show List.foldl (fun q j => diagPderiv j q) (diagPderiv i p) S.toList =
       diagPderiv i (S.toList.foldl (fun q j => diagPderiv j q) p)
  exact (diagPderiv_foldl_commute i S.toList p).symm

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

/-! ### Step 2c: general cofactor term and its derivative

For a permutation σ and finset S, define `permCofactor σ S` as the
product `∏_{k ∉ S} X_{(σ k, k)}` — this is the "remaining product"
after differentiating w.r.t. variables indexed by S. -/

/-- The cofactor product: `∏ k ∈ Sᶜ, X_{(σ k, k)}`. -/
noncomputable def permCofactor {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : MvPolynomial (Fin n × Fin n) ℚ :=
  ∏ k ∈ Sᶜ, MvPolynomial.X (σ k, k)

/-- Base case: `permCofactor σ ∅ = ∏_k X_{(σk, k)}` (full product). -/
theorem permCofactor_empty {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permCofactor σ ∅ =
    ∏ k : Fin n, (MvPolynomial.X (σ k, k) :
      MvPolynomial (Fin n × Fin n) ℚ) := by
  unfold permCofactor
  rw [Finset.compl_empty]

/-- Inductive step (fixing case): differentiating `permCofactor σ S` at
`i ∉ S` with `σ i = i` yields `permCofactor σ (insert i S)`. -/
theorem diagPderiv_permCofactor_fixes {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) (hσ : σ i = i) :
    diagPderiv i (permCofactor σ S) = permCofactor σ (insert i S) := by
  unfold permCofactor diagPderiv
  rw [pderiv_finset_prod]
  -- Σ_{k ∈ Sᶜ} pderiv (i,i) (X (σk, k)) * ∏_{j ∈ Sᶜ.erase k} X (σj, j)
  -- Only k = i contributes (since σi = i, X(σi, i) = X(i,i)).
  rw [Finset.sum_eq_single i]
  · -- k = i branch
    have hsi : (σ i, i) = (i, i) := by rw [hσ]
    show MvPolynomial.pderiv (i, i) (MvPolynomial.X (σ i, i)) * _ = _
    have h1 : MvPolynomial.pderiv (i, i) (MvPolynomial.X (σ i, i) :
        MvPolynomial (Fin n × Fin n) ℚ) = 1 := by
      rw [hsi]
      have := diagPderiv_X_diag (n := n) i
      unfold diagPderiv at this
      exact this
    rw [h1, one_mul]
    -- Sᶜ.erase i = (insert i S)ᶜ
    congr 1
    ext j
    simp only [Finset.mem_erase, Finset.mem_compl, Finset.mem_insert]
    constructor
    · rintro ⟨hji, hjS⟩
      rintro (heq | hjS')
      · exact hji heq
      · exact hjS hjS'
    · intro h
      refine ⟨fun heq => h (Or.inl heq), fun hjS => h (Or.inr hjS)⟩
  · intro k hk_mem hk_ne_i
    have hne : (σ k, k) ≠ (i, i) := by
      intro heq
      exact hk_ne_i (Prod.mk.injEq .. |>.mp heq).2
    have h := diagPderiv_X_off_diag (n := n) i (σ k) k hne
    unfold diagPderiv at h
    rw [h, zero_mul]
  · intro hnotin
    exact absurd (Finset.mem_compl.mpr hi) hnotin

/-- Inductive step (non-fixing case): differentiating `permCofactor σ S`
at `i ∉ S` with `σ i ≠ i` yields `0`. -/
theorem diagPderiv_permCofactor_nonfixing {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) (hσ : σ i ≠ i) :
    diagPderiv i (permCofactor σ S) = 0 := by
  unfold permCofactor diagPderiv
  rw [pderiv_finset_prod]
  apply Finset.sum_eq_zero
  intro k _
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

/-! ### Step 2d: the iterated cofactor formula

The main theorem of Step 2: applying `iterDiagPderiv S` to `permPoly`
yields a sum over permutations fixing `S` pointwise, each contributing
the cofactor product `permCofactor σ S`. -/

/-! ### Step 3a: permCofactor as a monomial

Each `permCofactor σ S` is a product of distinct variables (since σ
is a permutation), hence equals a single monomial with coefficient 1. -/

/-- The exponent finsupp of `permCofactor σ S`: maps `(p, q)` to 1
iff `q ∈ Sᶜ` and `σ q = p`, else 0. -/
noncomputable def permCofactorExp {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : (Fin n × Fin n) →₀ ℕ :=
  ∑ k ∈ Sᶜ, Finsupp.single (σ k, k) 1

/-- `permCofactor σ S = monomial (permCofactorExp σ S) 1`. -/
theorem permCofactor_eq_monomial {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    permCofactor σ S = MvPolynomial.monomial (permCofactorExp σ S) 1 := by
  unfold permCofactor permCofactorExp
  rw [MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro k _
  rw [MvPolynomial.X]

/-! ### Step 3b: witnessMono as a monomial -/

/-- The exponent finsupp of `witnessMono T`: maps `(p, q)` to 1 iff
`p = q` and `p ∈ Tᶜ`, else 0. -/
noncomputable def witnessMonoExp {n : ℕ} (T : Finset (Fin n)) :
    (Fin n × Fin n) →₀ ℕ :=
  ∑ i ∈ Tᶜ, Finsupp.single (i, i) 1

/-- `witnessMono T = monomial (witnessMonoExp T) 1`. -/
theorem witnessMono_eq_monomial {n : ℕ} (T : Finset (Fin n)) :
    witnessMono T = MvPolynomial.monomial (witnessMonoExp T) 1 := by
  unfold witnessMono witnessMonoExp
  rw [MvPolynomial.monomial_sum_one]
  apply Finset.prod_congr rfl
  intro i _
  rw [MvPolynomial.X]

/-! ### Step 3c: exponent equality characterization

Characterize when `permCofactorExp σ S = witnessMonoExp T`:
- The LHS has support `{(σ k, k) : k ∈ Sᶜ}`.
- The RHS has support `{(i, i) : i ∈ Tᶜ}`.
- Equal iff σ is identity on Sᶜ AND S = T. -/

/-- If `σ` is the identity and `S = T`, then the exponents match. -/
theorem permCofactorExp_eq_witnessMonoExp_of_id {n : ℕ}
    (S : Finset (Fin n)) :
    permCofactorExp (Equiv.refl (Fin n)) S = witnessMonoExp S := by
  unfold permCofactorExp witnessMonoExp
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- Identity permutation's cofactor at S equals the witnessMono at S. -/
theorem permCofactor_id {n : ℕ} (S : Finset (Fin n)) :
    permCofactor (Equiv.refl (Fin n)) S = witnessMono S := by
  rw [permCofactor_eq_monomial, witnessMono_eq_monomial,
      permCofactorExp_eq_witnessMonoExp_of_id]

/-- Coefficient of `witnessMono S` in `permCofactor id S` is 1. -/
theorem coeff_witnessMono_permCofactor_id {n : ℕ} (S : Finset (Fin n)) :
    MvPolynomial.coeff (witnessMonoExp S)
      (permCofactor (Equiv.refl (Fin n)) S) = 1 := by
  rw [permCofactor_id, witnessMono_eq_monomial, MvPolynomial.coeff_monomial]
  simp

/-! ### Step 3c: single-point evaluation of permCofactorExp

Using `Finsupp.coe_finset_sum` + `Finsupp.single_apply` for direct
pointwise evaluation. -/

/-- Finsupp-singles applied pointwise: `Finsupp.single a 1 b = if a = b then 1 else 0`. -/
theorem finsupp_single_one_apply {α : Type*} [DecidableEq α]
    (a b : α) : (Finsupp.single a 1 : α →₀ ℕ) b = if a = b then 1 else 0 := by
  rw [Finsupp.single_apply]

/-- Evaluation of `permCofactorExp` at a diagonal point `(v, v)`. -/
theorem permCofactorExp_apply_diag {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (v : Fin n) :
    permCofactorExp σ S (v, v) =
    if v ∈ Sᶜ ∧ σ v = v then 1 else 0 := by
  classical
  unfold permCofactorExp
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  by_cases hv : v ∈ Sᶜ
  · by_cases hσ : σ v = v
    · rw [if_pos ⟨hv, hσ⟩]
      rw [Finset.sum_eq_single v]
      · rw [finsupp_single_one_apply]
        rw [if_pos]
        simp [hσ]
      · intro k _ hk_ne_v
        rw [finsupp_single_one_apply]
        apply if_neg
        intro heq
        exact hk_ne_v (Prod.mk.inj heq).2
      · intro hnotin; exact absurd hv hnotin
    · rw [if_neg (fun h => hσ h.2)]
      apply Finset.sum_eq_zero
      intro k _
      rw [finsupp_single_one_apply]
      apply if_neg
      intro heq
      have h1 := (Prod.mk.inj heq).1
      have h2 := (Prod.mk.inj heq).2
      rw [h2] at h1
      exact hσ h1
  · rw [if_neg (fun h => hv h.1)]
    apply Finset.sum_eq_zero
    intro k hk
    rw [finsupp_single_one_apply]
    apply if_neg
    intro heq
    have h2 := (Prod.mk.inj heq).2
    rw [← h2] at hv
    exact hv hk

/-- Evaluation of `witnessMonoExp` at a diagonal point `(v, v)`. -/
theorem witnessMonoExp_apply_diag {n : ℕ} (T : Finset (Fin n)) (v : Fin n) :
    witnessMonoExp T (v, v) = if v ∈ Tᶜ then 1 else 0 := by
  classical
  unfold witnessMonoExp
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  by_cases hv : v ∈ Tᶜ
  · rw [if_pos hv]
    rw [Finset.sum_eq_single v]
    · rw [finsupp_single_one_apply, if_pos rfl]
    · intro i _ hi_ne_v
      rw [finsupp_single_one_apply]
      apply if_neg
      intro heq
      exact hi_ne_v (Prod.mk.inj heq).1
    · intro hnotin; exact absurd hv hnotin
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro i hi
    rw [finsupp_single_one_apply]
    apply if_neg
    intro heq
    have : i = v := (Prod.mk.inj heq).1
    exact hv (this ▸ hi)

/-- Evaluation of `permCofactorExp` at an off-diagonal point `(v, w)`
with `v ≠ w`. -/
theorem permCofactorExp_apply_off_diag {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (v w : Fin n) (hvw : v ≠ w) :
    permCofactorExp σ S (v, w) =
    if w ∈ Sᶜ ∧ σ w = v then 1 else 0 := by
  classical
  unfold permCofactorExp
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  by_cases hw : w ∈ Sᶜ
  · by_cases hσ : σ w = v
    · rw [if_pos ⟨hw, hσ⟩]
      rw [Finset.sum_eq_single w]
      · rw [finsupp_single_one_apply]
        rw [if_pos]
        simp [hσ]
      · intro k _ hk_ne_w
        rw [finsupp_single_one_apply]
        apply if_neg
        intro heq
        exact hk_ne_w (Prod.mk.inj heq).2
      · intro hnotin; exact absurd hw hnotin
    · rw [if_neg (fun h => hσ h.2)]
      apply Finset.sum_eq_zero
      intro k _
      rw [finsupp_single_one_apply]
      apply if_neg
      intro heq
      have h1 := (Prod.mk.inj heq).1
      have h2 := (Prod.mk.inj heq).2
      rw [h2] at h1
      exact hσ h1
  · rw [if_neg (fun h => hw h.1)]
    apply Finset.sum_eq_zero
    intro k hk
    rw [finsupp_single_one_apply]
    apply if_neg
    intro heq
    have h2 := (Prod.mk.inj heq).2
    rw [← h2] at hw
    exact hw hk

/-- `witnessMonoExp T` is zero on off-diagonal. -/
theorem witnessMonoExp_apply_off_diag {n : ℕ} (T : Finset (Fin n))
    (v w : Fin n) (hvw : v ≠ w) :
    witnessMonoExp T (v, w) = 0 := by
  classical
  unfold witnessMonoExp
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [finsupp_single_one_apply]
  apply if_neg
  intro heq
  have h1 : i = v := (Prod.mk.inj heq).1
  have h2 : i = w := (Prod.mk.inj heq).2
  exact hvw (h1 ▸ h2)

/-! ### Step 3d: exponent equality → σ = id ∧ S = T

The core combinatorial lemma: given σ fixes S and exponents match,
derive σ = identity AND S = T via pointwise evaluation. -/

/-- If exponents match, then σ fixes Sᶜ pointwise. Together with
σ fixing S (hypothesis), σ is the identity. -/
theorem perm_fixes_compl_of_expEq {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {S T : Finset (Fin n)}
    (h : permCofactorExp σ S = witnessMonoExp T) :
    ∀ w ∈ Sᶜ, σ w = w := by
  intro w hw
  by_contra hσ
  -- σ w ≠ w. Apply exponent equality at (σ w, w).
  set v := σ w with hv_def
  have hvw : v ≠ w := hσ
  have hLHS : permCofactorExp σ S (v, w) = 1 := by
    rw [permCofactorExp_apply_off_diag σ S v w hvw]
    rw [if_pos ⟨hw, rfl⟩]
  have hRHS : witnessMonoExp T (v, w) = 0 :=
    witnessMonoExp_apply_off_diag T v w hvw
  have : (1 : ℕ) = 0 := by
    rw [← hLHS, ← hRHS]
    exact DFunLike.congr_fun h (v, w)
  exact absurd this one_ne_zero

/-- If exponents match AND σ fixes S, then σ is the identity. -/
theorem perm_eq_refl_of_expEq {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {S T : Finset (Fin n)} (hσS : ∀ i ∈ S, σ i = i)
    (h : permCofactorExp σ S = witnessMonoExp T) :
    σ = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro i
  by_cases hiS : i ∈ S
  · exact hσS i hiS
  · exact perm_fixes_compl_of_expEq h i (Finset.mem_compl.mpr hiS)

/-- If exponents match AND σ fixes S, then S = T. -/
theorem S_eq_T_of_expEq {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {S T : Finset (Fin n)} (hσS : ∀ i ∈ S, σ i = i)
    (h : permCofactorExp σ S = witnessMonoExp T) :
    S = T := by
  -- σ = id (from above), so permCofactorExp id S = witnessMonoExp T
  -- ⇒ witnessMonoExp S = witnessMonoExp T (by permCofactorExp_eq_witnessMonoExp_of_id)
  -- ⇒ supports equal ⇒ Sᶜ = Tᶜ ⇒ S = T.
  have hσ_id : σ = Equiv.refl (Fin n) := perm_eq_refl_of_expEq hσS h
  rw [hσ_id] at h
  rw [permCofactorExp_eq_witnessMonoExp_of_id] at h
  -- h : witnessMonoExp S = witnessMonoExp T
  -- Apply at (v, v) for each v: witnessMonoExp S (v, v) = witnessMonoExp T (v, v).
  -- LHS: if v ∈ Sᶜ then 1 else 0. RHS: if v ∈ Tᶜ then 1 else 0.
  -- So v ∈ Sᶜ ↔ v ∈ Tᶜ, hence Sᶜ = Tᶜ ⇒ S = T.
  apply Finset.ext
  intro v
  -- Complementary biconditional from exponent equality at (v, v)
  have hSc_Tc_diff : v ∈ Sᶜ ↔ v ∈ Tᶜ := by
    constructor
    · intro hvSc
      have h1 : witnessMonoExp S (v, v) = 1 := by
        rw [witnessMonoExp_apply_diag]
        rw [if_pos hvSc]
      have h2 := DFunLike.congr_fun h (v, v)
      rw [h1] at h2
      rw [witnessMonoExp_apply_diag] at h2
      by_cases hvTc : v ∈ Tᶜ
      · exact hvTc
      · rw [if_neg hvTc] at h2
        exact absurd h2 one_ne_zero
    · intro hvTc
      have h1 : witnessMonoExp T (v, v) = 1 := by
        rw [witnessMonoExp_apply_diag]
        rw [if_pos hvTc]
      have h2 := DFunLike.congr_fun h.symm (v, v)
      rw [h1] at h2
      rw [witnessMonoExp_apply_diag] at h2
      by_cases hvSc : v ∈ Sᶜ
      · exact hvSc
      · rw [if_neg hvSc] at h2
        exact absurd h2 one_ne_zero
  -- Sᶜ = Tᶜ ↔ S = T on element v
  simp only [Finset.mem_compl] at hSc_Tc_diff
  exact not_iff_not.mp hSc_Tc_diff

/-- Helper: coefficient of `permCofactor σ S` at `witnessMonoExp T`
is 1 iff σ = id and S = T (when σ fixes S). -/
theorem coeff_permCofactor_eq {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S T : Finset (Fin n)) (hσS : ∀ i ∈ S, σ i = i) :
    MvPolynomial.coeff (witnessMonoExp T) (permCofactor σ S) =
    if σ = Equiv.refl (Fin n) ∧ S = T then 1 else 0 := by
  rw [permCofactor_eq_monomial, MvPolynomial.coeff_monomial]
  by_cases hST : σ = Equiv.refl (Fin n) ∧ S = T
  · rw [if_pos hST]
    rw [if_pos]
    rw [hST.1, hST.2]
    exact (permCofactorExp_eq_witnessMonoExp_of_id T).symm
  · rw [if_neg hST]
    rw [if_neg]
    intro hexp_eq
    -- hexp_eq is equality of exponents, possibly in either direction
    apply hST
    have hexp_eq' : permCofactorExp σ S = witnessMonoExp T := by
      first
      | exact hexp_eq
      | exact hexp_eq.symm
    constructor
    · exact perm_eq_refl_of_expEq hσS hexp_eq'
    · exact S_eq_T_of_expEq hσS hexp_eq'

/-- **Iterated cofactor formula** (Step 2 of Theorem 100):
`iterDiagPderiv S permPoly = Σ_{σ ∈ Perm : σ fixes S pointwise} permCofactor σ S`.

This is the paper's `∂_S perm_n = perm(X[T, T])` where `T = [n] \ S`,
expressed via the permCofactor term. -/
theorem iterDiagPderiv_permPoly_eq_sum_cofactor {n : ℕ}
    (S : Finset (Fin n)) :
    iterDiagPderiv S (permPoly n) =
    ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun σ => ∀ i ∈ S, σ i = i),
      permCofactor σ S := by
  induction S using Finset.induction_on with
  | empty =>
    rw [iterDiagPderiv_empty]
    rw [permPoly_eq_sum]
    -- RHS: sum over all σ (filter with ∀ i ∈ ∅ is trivially true) of
    -- permCofactor σ ∅ = ∏_k X_(σk, k)
    have hfilter : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun σ => ∀ i ∈ (∅ : Finset (Fin n)), σ i = i) =
        (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
      apply Finset.filter_true_of_mem
      intros σ _ i hi
      exact absurd hi (by simp)
    rw [hfilter]
    apply Finset.sum_congr rfl
    intro σ _
    exact (permCofactor_empty σ).symm
  | insert a S' ha_notin ih =>
    rw [iterDiagPderiv_insert ha_notin]
    rw [ih]
    -- diagPderiv a (Σ_{σ fixes S'} permCofactor σ S') = Σ ... using linearity
    have h_linear : diagPderiv a
        (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun σ => ∀ i ∈ S', σ i = i),
          permCofactor σ S') =
        ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun σ => ∀ i ∈ S', σ i = i),
          diagPderiv a (permCofactor σ S') := by
      unfold diagPderiv
      exact map_sum (MvPolynomial.pderiv (a, a)) _ _
    rw [h_linear]
    -- Split sum based on σ a = a; rewrite target as sum-with-if
    have hfilter : (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun σ => ∀ i ∈ insert a S', σ i = i) =
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun σ => ∀ i ∈ S', σ i = i)).filter (fun σ => σ a = a) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hfix
        refine ⟨fun i hi => hfix i (Or.inr hi), hfix a (Or.inl rfl)⟩
      · rintro ⟨hfixS', ha⟩ i (hi | hi)
        · rw [hi]; exact ha
        · exact hfixS' i hi
    rw [hfilter]
    -- Goal now: ∑ σ ∈ filter S', diagPderiv a (permCofactor σ S') =
    --          ∑ σ ∈ (filter S').filter (· a = a), permCofactor σ (insert a S')
    -- Convert RHS to sum-with-if over filter S':
    rw [Finset.sum_filter
      (s := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun σ => ∀ i ∈ S', σ i = i))
      (p := fun σ => σ a = a)
      (f := fun σ => permCofactor σ (insert a S'))]
    -- Now both sides are sums over filter S', term-by-term matching.
    apply Finset.sum_congr rfl
    intro σ hσ
    have hfixS' := (Finset.mem_filter.mp hσ).2
    by_cases hσa : σ a = a
    · rw [if_pos hσa]
      exact diagPderiv_permCofactor_fixes σ S' a ha_notin hσa
    · rw [if_neg hσa]
      exact diagPderiv_permCofactor_nonfixing σ S' a ha_notin hσa

/-! ### Step 3 main theorem: coefficient identity

`coeff (witnessMonoExp T) (∂_S permPoly) = δ_{S, T}`.

The paper's Theorem 100 core identity-minor claim. -/

/-- **Theorem 100 core identity-minor claim (Step 3 main)**:
`coeff (witnessMonoExp T) (∂_S permPoly) = δ_{S, T}`.

The SPDP matrix of `permPoly` has an identity submatrix indexed by
subsets of size κ = |S| (with rows = derivatives, columns = witness
monomials): on the diagonal the coefficient is 1, off-diagonal it's 0. -/
theorem coeff_witnessMono_iterDiagPderiv {n : ℕ} (S T : Finset (Fin n)) :
    MvPolynomial.coeff (witnessMonoExp T) (iterDiagPderiv S (permPoly n)) =
    if S = T then 1 else 0 := by
  rw [iterDiagPderiv_permPoly_eq_sum_cofactor]
  rw [MvPolynomial.coeff_sum]
  -- Σ_{σ fixes S} coeff (witnessMonoExp T) (permCofactor σ S)
  -- Each term: 1 if σ = id AND S = T, else 0. So sum = 1 if S = T (only σ=id), else 0.
  by_cases hST : S = T
  · rw [if_pos hST]
    rw [Finset.sum_eq_single (Equiv.refl (Fin n))]
    · rw [coeff_permCofactor_eq _ S T (fun i _ => rfl)]
      rw [if_pos ⟨rfl, hST⟩]
    · intro σ hσ hσ_ne_id
      have hσS := (Finset.mem_filter.mp hσ).2
      rw [coeff_permCofactor_eq σ S T hσS]
      rw [if_neg]
      intro ⟨hσ_id, _⟩
      exact hσ_ne_id hσ_id
    · intro hnotin
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => rfl⟩) hnotin
  · rw [if_neg hST]
    apply Finset.sum_eq_zero
    intro σ hσ
    have hσS := (Finset.mem_filter.mp hσ).2
    rw [coeff_permCofactor_eq σ S T hσS]
    rw [if_neg]
    intro ⟨_, hSTeq⟩
    exact hST hSTeq

/-! ### Step 4: identity minor → linear independence → rank bound

Using the identity submatrix from Step 3, show that the family of
`iterDiagPderiv S permPoly` (indexed by subsets S) is linearly
independent over ℚ. This gives a rank lower bound: the SPDP subspace
of permPoly contains C(n, k) linearly independent elements for each k. -/

/-- **Linear independence of the cofactor family**: the function
`S ↦ iterDiagPderiv S permPoly` from `Finset (Fin n)` to MvPoly is
linearly independent over ℚ.

Proof: if Σ_S c_S · (iterDiagPderiv S permPoly) = 0, take the
coefficient at `witnessMonoExp T` to get c_T = 0 (via Step 3). -/
theorem linearIndependent_iterDiagPderiv_permPoly {n : ℕ} :
    LinearIndependent ℚ
      (fun S : Finset (Fin n) => iterDiagPderiv S (permPoly n)) := by
  rw [linearIndependent_iff]
  intro l hl
  -- l : Finset (Fin n) →₀ ℚ (linear combination)
  -- hl : Finsupp.linearCombination ℚ (...) l = 0
  -- i.e., Σ_S l S · iterDiagPderiv S permPoly = 0 in MvPoly.
  ext T
  -- Show l T = 0 for each T.
  have htake_coeff : MvPolynomial.coeff (witnessMonoExp T)
      (Finsupp.linearCombination ℚ
        (fun S : Finset (Fin n) => iterDiagPderiv S (permPoly n)) l) = 0 := by
    rw [hl]
    exact MvPolynomial.coeff_zero _
  -- Expand the coefficient through the linear combination.
  rw [Finsupp.linearCombination_apply] at htake_coeff
  rw [Finsupp.sum] at htake_coeff
  rw [MvPolynomial.coeff_sum] at htake_coeff
  -- htake_coeff : Σ_{S ∈ l.support} coeff (witnessMonoExp T) (l S • iterDiagPderiv S permPoly) = 0
  -- = Σ_{S ∈ l.support} l S * coeff (witnessMonoExp T) (iterDiagPderiv S permPoly)
  -- = Σ_{S ∈ l.support} l S * (if S = T then 1 else 0)
  -- = if T ∈ l.support then l T else 0
  have hsimp : ∀ S ∈ l.support,
      MvPolynomial.coeff (witnessMonoExp T) (l S • iterDiagPderiv S (permPoly n)) =
      l S * (if S = T then 1 else 0) := by
    intro S _
    rw [MvPolynomial.coeff_smul]
    rw [coeff_witnessMono_iterDiagPderiv]
    simp [smul_eq_mul]
  rw [Finset.sum_congr rfl hsimp] at htake_coeff
  -- Now: Σ_{S ∈ l.support} l S * (if S = T then 1 else 0) = 0
  -- The sum simplifies to l T (or 0 if T ∉ support).
  by_cases hT : T ∈ l.support
  · rw [Finset.sum_eq_single T] at htake_coeff
    · rw [if_pos rfl, mul_one] at htake_coeff
      -- l T = 0 iff (Finsupp.linearCombination ...) = 0
      show l T = (0 : Finset (Fin n) →₀ ℚ) T
      rw [Finsupp.coe_zero, Pi.zero_apply]
      exact htake_coeff
    · intro S _ hS_ne_T
      rw [if_neg hS_ne_T, mul_zero]
    · intro hnotin
      exact absurd hT hnotin
  · show l T = (0 : Finset (Fin n) →₀ ℚ) T
    rw [Finsupp.coe_zero, Pi.zero_apply]
    exact Finsupp.notMem_support_iff.mp hT

/-! ### Step 5: rank bound from linear independence

The linearly independent family of `iterDiagPderiv S permPoly` terms
gives a lower bound on the dimension of the span subspace. -/

/-- The span of the cofactor family has finrank equal to `2^n`
(cardinality of `Finset (Fin n)`). -/
theorem finrank_span_cofactor_family_eq {n : ℕ} :
    Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range (fun S : Finset (Fin n) =>
          iterDiagPderiv S (permPoly n)))) = 2 ^ n := by
  have hli := linearIndependent_iterDiagPderiv_permPoly (n := n)
  rw [finrank_span_eq_card hli]
  rw [Fintype.card_finset]
  simp

/-- The span of the cofactor family has finrank at least `2^n`. -/
theorem finrank_span_cofactor_family_ge {n : ℕ} :
    2 ^ n ≤ Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range (fun S : Finset (Fin n) =>
          iterDiagPderiv S (permPoly n)))) :=
  finrank_span_cofactor_family_eq.ge

/-! ### Step 5b: κ-restricted rank bound (paper's form)

The paper's Theorem 100 uses Γ_{κ,0}(perm_n) ≥ C(n, κ). Restricting
to subsets of size κ gives C(n, κ) linearly independent elements. -/

/-- Linear independence of the cofactor family restricted to subsets
of size exactly κ. -/
theorem linearIndependent_iterDiagPderiv_permPoly_of_card {n : ℕ} (κ : ℕ) :
    LinearIndependent ℚ
      (fun S : { S : Finset (Fin n) // S.card = κ } =>
        iterDiagPderiv S.val (permPoly n)) := by
  apply LinearIndependent.comp linearIndependent_iterDiagPderiv_permPoly
  intro x y hxy
  exact Subtype.ext hxy

/-- Cardinality of size-κ subsets of `Fin n` is `Nat.choose n κ`. -/
private theorem card_subtype_size_eq_choose (n κ : ℕ) :
    Fintype.card { S : Finset (Fin n) // S.card = κ } =
    Nat.choose n κ := by
  rw [Fintype.card_finset_len]
  simp

/-- **Paper's rank bound (Theorem 100)**: `finrank` of the span of
size-κ cofactors is `Nat.choose n κ`. -/
theorem finrank_span_cofactor_family_card_eq {n : ℕ} (κ : ℕ) :
    Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range (fun S : { S : Finset (Fin n) // S.card = κ } =>
          iterDiagPderiv S.val (permPoly n)))) = Nat.choose n κ := by
  have hli := linearIndependent_iterDiagPderiv_permPoly_of_card (n := n) κ
  rw [finrank_span_eq_card hli]
  exact card_subtype_size_eq_choose n κ

/-- **Paper's rank lower bound (Theorem 100 corollary)**. -/
theorem finrank_span_cofactor_family_card_ge {n : ℕ} (κ : ℕ) :
    Nat.choose n κ ≤ Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range (fun S : { S : Finset (Fin n) // S.card = κ } =>
          iterDiagPderiv S.val (permPoly n)))) :=
  (finrank_span_cofactor_family_card_eq κ).ge

/-! ### Step 5c: paper-faithful rank bound at κ = n/2

The paper's concrete Theorem 100 statement: at κ = ⌊n/2⌋, the SPDP
rank of `perm_n` is at least `C(n, ⌊n/2⌋) = 2^Ω(n)`. -/

/-- At κ = n/2, the rank lower bound becomes the central binomial
coefficient `C(n, n/2)`, which is ≥ `2^n / (n+1)`. -/
theorem finrank_span_cofactor_family_half {n : ℕ} :
    Nat.choose n (n / 2) ≤ Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range (fun S : { S : Finset (Fin n) // S.card = n / 2 } =>
          iterDiagPderiv S.val (permPoly n)))) :=
  finrank_span_cofactor_family_card_ge (n / 2)

/-! ### Summary of Theorem 100 formalization

This file completes paper's Theorem 100 (God-Move identity minor for
the permanent) AXIOM-FREE:

Steps 1-5 all proved axiom-free:
- Step 1: partial derivative infrastructure
- Step 2: cofactor identity ∂_S perm_n = perm(X[T,T])
  (iterDiagPderiv_permPoly_eq_sum_cofactor)
- Step 3: coefficient identity coeff(m_T)(∂_S perm_n) = δ_{S,T}
  (coeff_witnessMono_iterDiagPderiv)
- Step 4: linear independence of the cofactor family
  (linearIndependent_iterDiagPderiv_permPoly)
- Step 5: rank bound
  (finrank_span_cofactor_family_card_eq = C(n, κ))

All theorems depend only on propext, Classical.choice, Quot.sound.

This provides an AXIOM-FREE formalization of the paper's NP-side
identity-minor construction for the permanent polynomial — the
"God Move" of Theorem 98/100.

What this does NOT yet include:
- Connection to `paperSpdpMatrix` via reindexing `Fin n × Fin n ≃ Fin (n²)`
- Connection to `mlBlockedSpdpSubspaceInc` generators
- P-side bound (Theorem 10 via amplituhedron) — genuinely paper-deep
- Valiant's permanent-hardness connecting to 3-SAT deciders

These remain as future work on the path to full P ≠ NP discharge. -/

/-! ## Reindexing to `Fin (n * n)` for SPDP-matrix connection

The paper-matrix setup uses `MvPolynomial (Fin N) ℚ` with flat
variable indexing. For the permanent, this requires the equivalence
`Fin n × Fin n ≃ Fin (n * n)` to embed `permPoly` into that form. -/

/-- The flat equivalence `Fin n × Fin n ≃ Fin (n * n)` from Mathlib. -/
noncomputable abbrev flatEquiv (n : ℕ) : Fin n × Fin n ≃ Fin (n * n) :=
  finProdFinEquiv

/-- The permanent polynomial reindexed to `Fin (n * n)`. -/
noncomputable def permPolyFlat (n : ℕ) : MvPolynomial (Fin (n * n)) ℚ :=
  (MvPolynomial.renameEquiv ℚ (flatEquiv n)) (permPoly n)

/-- The renamed permanent polynomial's cofactor family is linearly
independent (since renameEquiv is an injective linear map). -/
theorem linearIndependent_renamed_cofactors {n : ℕ} :
    LinearIndependent ℚ
      (fun S : Finset (Fin n) =>
        (MvPolynomial.renameEquiv ℚ (flatEquiv n))
          (iterDiagPderiv S (permPoly n))) := by
  have hli := linearIndependent_iterDiagPderiv_permPoly (n := n)
  have halg_inj : Function.Injective
      ((MvPolynomial.renameEquiv ℚ (flatEquiv n)) : _ → _) :=
    (MvPolynomial.renameEquiv ℚ (flatEquiv n)).injective
  -- Via LinearMap.injOn_of_injective on the ambient linear map.
  have hmap_inj : Function.Injective
      (MvPolynomial.renameEquiv ℚ (flatEquiv n)).toLinearMap :=
    halg_inj
  exact LinearIndependent.map' hli
    (MvPolynomial.renameEquiv ℚ (flatEquiv n)).toLinearMap
    (LinearMap.ker_eq_bot.mpr hmap_inj)

/-- The flat span finrank equals `2^n`. -/
theorem finrank_span_permPolyFlat_cofactors_eq {n : ℕ} :
    Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range (fun S : Finset (Fin n) =>
          (MvPolynomial.renameEquiv ℚ (flatEquiv n))
            (iterDiagPderiv S (permPoly n))))) = 2 ^ n := by
  rw [finrank_span_eq_card linearIndependent_renamed_cofactors]
  rw [Fintype.card_finset]
  simp

/-- κ-restricted version of the flat span finrank. -/
theorem finrank_span_permPolyFlat_cofactors_card_eq {n : ℕ} (κ : ℕ) :
    Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range (fun S : { S : Finset (Fin n) // S.card = κ } =>
          (MvPolynomial.renameEquiv ℚ (flatEquiv n))
            (iterDiagPderiv S.val (permPoly n))))) = Nat.choose n κ := by
  have hli : LinearIndependent ℚ (fun S : { S : Finset (Fin n) // S.card = κ } =>
      (MvPolynomial.renameEquiv ℚ (flatEquiv n)) (iterDiagPderiv S.val (permPoly n))) := by
    apply LinearIndependent.comp linearIndependent_renamed_cofactors
    intro x y hxy
    exact Subtype.ext hxy
  rw [finrank_span_eq_card hli]
  exact card_subtype_size_eq_choose n κ

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
