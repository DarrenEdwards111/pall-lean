import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
/-!
# SPDP Definitions — Paper-Faithful (Pall §2)

Definitions 2.1–2.3. SPDP rank defined as the dimension of the row span
of the SPDP matrix M_{κ,ℓ}(f), whose rows are the polynomials m·∂_S f
for |S|=κ, deg(m)≤ℓ.

Since the dimension of the span of a set of polynomials equals the
matrix rank of their coefficient vectors, this is equivalent to
Module.finrank of the F-span. We use the submodule formulation.
-/

namespace SPDP

open MvPolynomial

/-! ## Block Partitions (Definition 2.3) -/

structure BlockPartition (n : ℕ) where
  numBlocks : ℕ
  assign : Fin n → Fin numBlocks

def isBlockAdmissible {n : ℕ} (B : BlockPartition n) (S : List (Fin n)) : Prop :=
  S.Nodup ∧ ∀ b : Fin B.numBlocks, (S.filter (fun i => B.assign i = b)).length ≤ 1

/-- Sublists of block-admissible lists are block-admissible. -/
theorem isBlockAdmissible_of_sublist {n : ℕ} {B : BlockPartition n}
    {S T : List (Fin n)} (hT : T.Sublist S) (hS : isBlockAdmissible B S) :
    isBlockAdmissible B T := by
  constructor
  · exact hS.1.sublist hT
  · intro b
    have : (T.filter (fun i => B.assign i = b)).Sublist (S.filter (fun i => B.assign i = b)) :=
      List.Sublist.filter _ hT
    exact le_trans (List.Sublist.length_le this) (hS.2 b)

structure SPDPParams where
  κ : ℕ
  ℓ : ℕ

def matchedParams (n : ℕ) : SPDPParams :=
  { κ := Nat.log 2 n, ℓ := Nat.log 2 n }

/-! ## Iterated Partial Derivatives -/

noncomputable def iterDerivList {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) F :=
  indices.foldl (fun q i => MvPolynomial.pderiv i q) p

/-! ## SPDP Subspace and Rank (Definitions 2.1–2.2)

The SPDP matrix M_{κ,ℓ}(f) has rows indexed by (S, m) where |S|=κ and
deg(m)≤ℓ. Each row is the coefficient vector of m · ∂_S f.

Γ_{κ,ℓ}(f) = rank(M_{κ,ℓ}(f)) = dim(span{m · ∂_S f : |S|=κ, deg(m)≤ℓ})

We define this as Module.finrank of the F-span. -/

noncomputable def spdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        q = m * iterDerivList S p }

noncomputable def spdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (spdpSubspace κ ℓ p)

noncomputable def blockedSpdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        q = m * iterDerivList S p }

noncomputable def blockedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (blockedSpdpSubspace B κ ℓ p)

/-! ## Basic Properties -/

theorem blockedSubspace_le {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    blockedSpdpSubspace B κ ℓ p ≤ spdpSubspace κ ℓ p := by
  apply Submodule.span_mono
  intro q ⟨S, m, hlen, hdeg, _, hq⟩
  exact ⟨S, m, hlen, hdeg, hq⟩

theorem foldl_pderiv_zero {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) :
    List.foldl (fun (q : MvPolynomial (Fin n) F) i => pderiv i q) 0 indices = 0 := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [List.foldl_cons, map_zero]; exact ih

/-! ## Finite-Dimensionality of SPDP Subspaces

Key chain: pderiv doesn't increase totalDegree, so every generator
m · ∂_S p has totalDegree ≤ ℓ + totalDegree(p). The subspace sits
inside restrictTotalDegree, which is Module.Finite in Mathlib. -/

/-- Partial derivative does not increase total degree. -/
theorem totalDegree_pderiv_le {F : Type*} [CommRing F] {n : ℕ}
    (i : Fin n) (p : MvPolynomial (Fin n) F) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  -- pderiv is linear: write p = ∑ over support
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply le_trans (totalDegree_finset_sum _ _)
  apply Finset.sup_le
  intro s hs
  rw [pderiv_monomial]
  apply le_trans (totalDegree_monomial_le _ _)
  -- Need: degree of (s - single i 1) ≤ degree of s ≤ totalDegree p
  apply le_trans _ (le_totalDegree hs)
  -- (s - single i 1).sum (fun x => id) ≤ s.sum (fun _ e => e)
  -- Both are the same as Finsupp.sum _ (fun _ n => n)
  -- Use Finsupp.sum_le_sum_index with tsub ≤ self
  classical
  have hle : s - Finsupp.single i 1 ≤ s := fun j => by simp [Finsupp.tsub_apply]
  exact Finsupp.sum_le_sum_index hle (fun j _ => monotone_id) (fun j _ => rfl)

/-- Iterated partial derivatives do not increase total degree. -/
theorem totalDegree_iterDerivList_le {F : Type*} [CommRing F] {n : ℕ}
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    (iterDerivList indices p).totalDegree ≤ p.totalDegree := by
  -- iterDerivList = foldl (fun q i => pderiv i q) p indices
  -- By induction: each foldl step applies pderiv which doesn't increase degree
  unfold iterDerivList
  induction indices generalizing p with
  | nil => exact le_refl _
  | cons i rest ih =>
    simp only [List.foldl_cons]
    -- foldl rest (pderiv i p) has degree ≤ (pderiv i p).totalDegree ≤ p.totalDegree
    exact le_trans (ih (pderiv i p)) (totalDegree_pderiv_le i p)

/-- Every generator of blockedSpdpSubspace has bounded total degree. -/
theorem blockedSpdpSubspace_le_restrictTotalDegree {F : Type*} [CommRing F] {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    blockedSpdpSubspace B κ ℓ p ≤
      MvPolynomial.restrictTotalDegree (Fin n) F (ℓ + p.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, _, hdeg, _, hq⟩
  show q ∈ MvPolynomial.restrictTotalDegree (Fin n) F (ℓ + p.totalDegree)
  rw [MvPolynomial.mem_restrictTotalDegree, hq]
  exact le_trans (totalDegree_mul m (iterDerivList S p))
    (Nat.add_le_add hdeg (totalDegree_iterDerivList_le S p))

/-- The blocked SPDP subspace is finite-dimensional (sits inside restrictTotalDegree). -/
instance blockedSpdpSubspace_finite {F : Type*} [Field F] {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Module.Finite F (blockedSpdpSubspace B κ ℓ p) := by
  -- blockedSpdpSubspace ≤ restrictTotalDegree, which is Module.Finite
  have hle := blockedSpdpSubspace_le_restrictTotalDegree B κ ℓ p
  have : Module.Finite F (MvPolynomial.restrictTotalDegree (Fin n) F (ℓ + p.totalDegree)) :=
    MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite _ _ _
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

/-- finrank of iSup over Fin m ≤ sum of finranks. -/
-- finrank of binary sup ≤ sum (wrapper for Submodule.finrank_add_le_finrank_add_finrank)
private theorem finrank_sup_le {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (U W : Submodule F V) [Module.Finite F U] [Module.Finite F W] :
    Module.finrank F ↥(U ⊔ W) ≤ Module.finrank F U + Module.finrank F W :=
  Submodule.finrank_add_le_finrank_add_finrank U W

/-- finrank of iSup over Fin m ≤ sum of finranks (by induction on m). -/
theorem finrank_iSup_fin_le {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (m : ℕ) (U : Fin m → Submodule F V) [∀ i, Module.Finite F ↥(U i)] :
    Module.finrank F ↥(⨆ i : Fin m, U i) ≤ ∑ i : Fin m, Module.finrank F ↥(U i) := by
  induction m with
  | zero =>
    have : (⨆ i : Fin 0, U i) = ⊥ := by simp [iSup_of_empty]
    simp [this, Submodule.finrank_eq_zero]
  | succ n ih =>
    haveI : ∀ i : Fin n, Module.Finite F ↥(U (Fin.castSucc i)) :=
      fun i => inferInstanceAs (Module.Finite F ↥(U (Fin.castSucc i)))
    haveI : Module.Finite F ↥(⨆ i : Fin n, U (Fin.castSucc i)) :=
      Submodule.finite_iSup _
    -- Key: ⨆ Fin (n+1) ≤ (⨆ Fin n via castSucc) ⊔ U (last n)
    have hle : (⨆ i : Fin (n + 1), U i) ≤
        (⨆ i : Fin n, U (Fin.castSucc i)) ⊔ U (Fin.last n) := by
      apply iSup_le; intro i
      refine Fin.lastCases ?_ ?_ i
      · exact le_sup_right
      · intro j; exact le_sup_of_le_left (le_iSup (fun i => U (Fin.castSucc i)) j)
    calc Module.finrank F ↥(⨆ i : Fin (n + 1), U i)
        ≤ Module.finrank F ↥((⨆ i : Fin n, U (Fin.castSucc i)) ⊔ U (Fin.last n)) :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank F ↥(⨆ i : Fin n, U (Fin.castSucc i)) +
          Module.finrank F ↥(U (Fin.last n)) :=
          finrank_sup_le _ _
      _ ≤ (∑ i : Fin n, Module.finrank F ↥(U (Fin.castSucc i))) +
          Module.finrank F ↥(U (Fin.last n)) :=
          Nat.add_le_add_right (@ih (U ∘ Fin.castSucc)
            (fun i => inferInstanceAs (Module.Finite F ↥(U (Fin.castSucc i))))) _
      _ = ∑ i : Fin (n + 1), Module.finrank F ↥(U i) := by
          rw [Fin.sum_univ_castSucc]

/-! ## Monotonicity Properties (Pall §2, basic properties)

These are fundamental properties of SPDP rank that hold because
each operation corresponds to a rank-nonincreasing operation on
the coefficient matrix M_{κ,ℓ}(f). -/

-- Restriction monotonicity and rename invariance are proved in
-- RestrictionProof.lean (using CoeffBridge infrastructure).
-- They are not used directly in the P ≠ NP proof chain but are
-- fundamental SPDP properties documented here for completeness.
--
-- restriction_rank_le: Setting x_i = c cannot increase Γ_{κ,ℓ}
-- rank_rename_eq: Injective rename preserves Γ_{κ,ℓ}

/-! ## Arithmetic (Theorem 19.1 step) -/

theorem superPoly_beats_poly (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀, ∀ n, n ≥ n₀ → n ^ (Nat.log 2 n / 4) > n ^ C := by
  use 2 ^ (4 * C + 4)
  intro n hn
  apply Nat.pow_lt_pow_right
  · have : (2 : ℕ) ^ 1 ≤ 2 ^ (4 * C + 4) := by
      apply Nat.pow_le_pow_right (by norm_num); omega
    omega
  · have h_log : Nat.log 2 n ≥ 4 * C + 4 := by
      have : 2 ^ (4 * C + 4) ≤ n := hn
      calc 4 * C + 4
          = Nat.log 2 (2 ^ (4 * C + 4)) := by
            rw [Nat.log_pow (by norm_num : 1 < 2)]
        _ ≤ Nat.log 2 n := Nat.log_mono_right this
    omega

/-! ## Locality Structure -/

/-- A polynomial with locality structure: sum of local gates, each
    touching ≤ width variables. Used for the P-side collapse argument. -/
structure HasLocalityStructure {v : ℕ} {F : Type*} [CommRing F]
    (p : MvPolynomial (Fin v) F) where
  numGates : ℕ
  width : ℕ
  gate : Fin numGates → MvPolynomial (Fin v) F
  sum_eq : p = ∑ i, gate i
  gate_width : ∀ i, (gate i).vars.card ≤ width

end SPDP
