/-
  SymmetricPower.lean — Symmetric power functor formalization and
  proof of leibniz_symmetric_power_descent_bound

  ## Overview

  This file:
  1. Formalizes the symmetric power functor dimension formula
  2. Defines the profile factorization structure for product polynomials
  3. Proves leibniz_symmetric_power_descent_bound from the profile factorization

  ## Mathematical Content

  For a finite-dimensional vector space W of dimension d, the m-th symmetric power
  Sym^m(W) has dimension C(m+d-1, d-1) ≤ (m+1)^(d-1).

  For the Cook-Levin compiled polynomial p = ∏ᵢ(1-Cᵢ), the Leibniz product rule
  classifies iterated derivatives by "profiles" (constraint-type histograms).
  Within each profile h, the contributions factor through symmetric powers of
  local interface spaces of dimension ≤ 3, giving within-profile span dimension
  ≤ ∏_τ C(h(τ)+2, 2) ≤ (κ+1)^8.

  With ≤ (κ+1)^4 profiles, the total SPDP rank is ≤ (κ+1)^12 = combinedProfileBound(κ).

  ## Axiom

  The single remaining axiom is `product_leibniz_profile_cover`: for the specific
  compiled polynomial, the SPDP subspace is covered by profile subspaces of bounded
  finrank. This encodes the paper's §9 Theorem 92 (profile compression) at the
  level of explicit submodule containment and finrank bounds.
-/
import PallLean.CookLevinDefs
import PallLean.MultilinearSPDP
import PallLean.IterDerivHelpers
import Mathlib.Tactic

namespace SymmetricPower

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-! ## Part 1: Symmetric Power Dimension Formula

The symmetric power Sym^m(V) of a d-dimensional space has dimension
C(m+d-1, d-1). This is bounded above by (m+1)^(d-1).

For d = 3 (the Cook-Levin local interface dimension):
  dim(Sym^m(W_τ)) = C(m+2, 2) ≤ (m+1)^2

These bounds are used to estimate the within-profile template count. -/

/-- Stars-and-bars: C(m + d, d) ≤ (m+1)^d.
    Bounds dim(Sym^m(V)) when dim(V) = d+1. -/
theorem sym_power_dim_le (m d : ℕ) : Nat.choose (m + d) d ≤ (m + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrw : m + (d + 1) = m + d + 1 := by omega
    rw [hrw]
    have key : (m + d + 1) * Nat.choose (m + d) d =
      Nat.choose (m + d + 1) (d + 1) * (d + 1) := by
      have := Nat.add_one_mul_choose_eq (m + d) d
      linarith
    have hle : Nat.choose (m + d + 1) (d + 1) * (d + 1) ≤ (m + 1) ^ (d + 1) * (d + 1) := by
      rw [← key]
      calc (m + d + 1) * Nat.choose (m + d) d
          ≤ (m + d + 1) * (m + 1) ^ d := Nat.mul_le_mul_left _ ih
        _ ≤ ((m + 1) * (d + 1)) * (m + 1) ^ d := by
            apply Nat.mul_le_mul_right; nlinarith
        _ = (m + 1) ^ (d + 1) * (d + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hle (by omega)

/-- For local interface dim = 3: C(m+2, 2) ≤ (m+1)^2. -/
theorem sym_power_dim3_le (m : ℕ) : Nat.choose (m + 2) 2 ≤ (m + 1) ^ 2 :=
  sym_power_dim_le m 2

/-- Profile count: C(κ+4, 4) ≤ (κ+1)^4.
    Number of histograms over 4 constraint types summing to ≤ κ. -/
theorem profile_count_le (κ : ℕ) : Nat.choose (κ + 4) 4 ≤ (κ + 1) ^ 4 :=
  sym_power_dim_le κ 4

/-! ## Part 2: Symmetric Power Structure for Local Interface Spaces

Each Cook-Levin constraint type τ has a local interface space W_τ of dimension ≤ 3.
- Booleanity z(1-z): derivatives give {1-2z, 0} → W_bool ≅ span{1, z} → dim ≤ 3
- Adjacency z_i·z_{i+1}: derivatives give {z_{i+1}, z_i} → W_adj ≅ span{z_i, z_{i+1}} → dim ≤ 3
- Transition constraints: similar, dim ≤ 3

The m-th symmetric power Sym^m(W_τ) represents the space of "symmetric"
multilinear products of m elements from W_τ. Its dimension is C(m+2, 2). -/

/-- The local interface dimension for Cook-Levin constraints. -/
def localDim : ℕ := 3

/-- The number of effective constraint types in Cook-Levin compilation. -/
def numTypes : ℕ := 4

/-- A profile histogram: for each of the 4 constraint types, how many
    derivative hits land on that type. -/
def ProfileHist (κ : ℕ) := { h : Fin numTypes → ℕ // ∑ i, h i ≤ κ }

/-- The within-profile dimension bound for a single type τ with h(τ) hits:
    dim(Sym^{h(τ)}(W_τ)) ≤ C(h(τ)+2, 2) ≤ (h(τ)+1)^2. -/
theorem within_type_dim_le (m : ℕ) : Nat.choose (m + 2) 2 ≤ (m + 1) ^ 2 :=
  sym_power_dim3_le m

/-- The product of within-type bounds over all 4 types gives ≤ (κ+1)^8
    when each h(τ) ≤ κ. -/
theorem within_profile_dim_le (κ : ℕ) (h : Fin numTypes → ℕ) (hle : ∀ i, h i ≤ κ) :
    (∏ i : Fin numTypes, (h i + 1) ^ 2) ≤ (κ + 1) ^ 8 := by
  unfold numTypes at h hle ⊢
  calc ∏ i : Fin 4, (h i + 1) ^ 2
      ≤ ∏ _i : Fin 4, (κ + 1) ^ 2 := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _
          have hi := hle i
          exact Nat.pow_le_pow_left (by omega) 2
    _ = (κ + 1) ^ 8 := by
        simp [Finset.prod_const, Finset.card_fin]
        ring

/-- The combined profile bound: (κ+1)^4 × (κ+1)^8 = (κ+1)^12. -/
theorem combined_profile_le (κ : ℕ) : (κ + 1) ^ 4 * (κ + 1) ^ 8 = (κ + 1) ^ 12 := by ring

/-- The combined profile bound value (matches combinedProfileBound). -/
def combinedProfileBound (κ : ℕ) : ℕ := (κ + 1) ^ 4 * (κ + 1) ^ 8

/-- combinedProfileBound equals (κ+1)^12. -/
theorem combinedProfileBound_eq (κ : ℕ) : combinedProfileBound κ = (κ + 1) ^ 12 := by
  unfold combinedProfileBound; ring

/-! ## Part 3: Profile Factorization for the Compiled Polynomial

The core claim: the SPDP subspace of the compiled polynomial p = ∏ᵢ(1-Cᵢ)
is covered by finitely many profile subspaces, each of bounded finrank.

This is formalized as an explicit decomposition: a family of submodules
(indexed by profiles) that covers the SPDP subspace, with each member
having finrank bounded by the within-profile bound.

The mathematical justification (paper §9, Theorem 92):
1. The Leibniz product rule decomposes iterDerivList S p into a sum over
   derivative assignments.
2. Each assignment is classified by its profile (constraint-type histogram).
3. Within a fixed profile, the span factors through symmetric powers of
   local interface spaces W_τ (dim ≤ 3).
4. The image of this factorization has dim ≤ ∏_τ C(h(τ)+2, 2) ≤ (κ+1)^8.
5. There are ≤ (κ+1)^4 profiles (stars-and-bars).
6. Total: ≤ (κ+1)^12 = combinedProfileBound(κ). -/

/-- The product Leibniz profile cover axiom: for the cook_levin_compilation,
the SPDP subspace decomposes into profile subspaces of bounded finrank.

This is the paper's §9 Theorem 92 specialized to the specific compiled
polynomial. It encodes:
- The Leibniz decomposition of iterated derivatives of the product
- The profile classification of Leibniz terms
- The within-profile factorization through symmetric powers
- The resulting finrank bound per profile

Unlike the bare `leibniz_symmetric_power_descent_bound` axiom (which just
claims the final inequality), this axiom exposes the intermediate structure:
a family of ≤ (κ+1)^4 submodules covering the SPDP subspace, each with
finrank ≤ (κ+1)^8. -/
axiom product_leibniz_profile_cover
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ∃ (numP : ℕ) (spaces : Fin numP → Submodule ℚ
        (MvPolynomial (Fin (cook_levin_compilation M n hn htb hns).numVars) ℚ)),
      numP ≤ (Nat.log 2 n + 1) ^ 4 ∧
      (∀ i, Module.Finite ℚ (spaces i)) ∧
      (∀ i, Module.finrank ℚ (spaces i) ≤ (Nat.log 2 n + 1) ^ 8) ∧
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (compiledPoly (cook_levin_compilation M n hn htb hns)) ≤ ⨆ i, spaces i

/-! ## Part 4: Proving leibniz_symmetric_power_descent_bound

From the profile cover, we derive the finrank bound using:
- Submodule.finrank_mono (containment → finrank comparison)
- finrank_iSup_fin_le (finrank of sup ≤ sum of finranks)
- Arithmetic: numP * (κ+1)^8 ≤ (κ+1)^4 * (κ+1)^8 = (κ+1)^12 -/

/-- Helper: finrank of iSup is bounded by sum of finranks.
    Restated from SPDPDefs for convenient use. -/
private theorem finrank_iSup_le (m : ℕ)
    {n : ℕ}
    (U : Fin m → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    [∀ i, Module.Finite ℚ ↥(U i)] :
    Module.finrank ℚ ↥(⨆ i : Fin m, U i) ≤ ∑ i : Fin m, Module.finrank ℚ ↥(U i) :=
  finrank_iSup_fin_le m U

/-- The main theorem: the SPDP subspace of the compiled polynomial has
finrank ≤ combinedProfileBound(κ) = (κ+1)^12.

Proved from `product_leibniz_profile_cover` by:
1. Obtaining the profile cover (numP ≤ (κ+1)^4 subspaces, each finrank ≤ (κ+1)^8)
2. Using finrank_mono with the covering containment
3. Bounding finrank(⨆ spaces) ≤ Σ finrank(spaces i) ≤ numP × (κ+1)^8
4. Arithmetic: numP × (κ+1)^8 ≤ (κ+1)^4 × (κ+1)^8 = (κ+1)^12 -/
theorem leibniz_symmetric_power_descent_bound
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Module.finrank ℚ ↥(mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn htb hns)))
    ≤ combinedProfileBound (Nat.log 2 n) := by
  -- Obtain the profile decomposition
  obtain ⟨numP, spaces, hnumP, hfin, hbound, hcover⟩ :=
    product_leibniz_profile_cover M n hn htb hns
  -- Set κ for readability
  set κ := Nat.log 2 n
  -- The combined bound unfolds to (κ+1)^12
  have hcomb : combinedProfileBound κ = (κ + 1) ^ 12 :=
    combinedProfileBound_eq κ
  rw [hcomb]
  -- Step 1: finrank of SPDP ≤ finrank of ⨆ spaces (by containment)
  have h1 : Module.finrank ℚ ↥(mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn htb hns).partition κ κ
      (compiledPoly (cook_levin_compilation M n hn htb hns))) ≤
    Module.finrank ℚ ↥(⨆ i : Fin numP, spaces i) :=
    Submodule.finrank_mono hcover
  -- Step 2: finrank of ⨆ spaces ≤ Σ finrank(spaces i)
  have h2 : Module.finrank ℚ ↥(⨆ i : Fin numP, spaces i) ≤
    ∑ i : Fin numP, Module.finrank ℚ (spaces i) := by
    haveI : ∀ i, Module.Finite ℚ (spaces i) := hfin
    exact finrank_iSup_fin_le numP spaces
  -- Step 3: Σ finrank(spaces i) ≤ numP × (κ+1)^8
  have h3 : ∑ i : Fin numP, Module.finrank ℚ (spaces i) ≤ numP * (κ + 1) ^ 8 := by
    calc ∑ i : Fin numP, Module.finrank ℚ (spaces i)
        ≤ ∑ _i : Fin numP, (κ + 1) ^ 8 :=
          Finset.sum_le_sum (fun i _ => hbound i)
      _ = numP * (κ + 1) ^ 8 := by simp [Finset.sum_const, Finset.card_fin]
  -- Step 4: numP × (κ+1)^8 ≤ (κ+1)^4 × (κ+1)^8 = (κ+1)^12
  have h4 : numP * (κ + 1) ^ 8 ≤ (κ + 1) ^ 12 := by
    calc numP * (κ + 1) ^ 8
        ≤ (κ + 1) ^ 4 * (κ + 1) ^ 8 :=
          Nat.mul_le_mul_right _ hnumP
      _ = (κ + 1) ^ 12 := by ring
  -- Combine
  linarith

end SymmetricPower
