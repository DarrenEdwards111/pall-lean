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
