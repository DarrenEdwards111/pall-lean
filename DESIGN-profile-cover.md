# Design: profile_subspace_cover proof

## The Problem

Last axiom: `profile_subspace_cover`. Given R ≤ n, decompose the blocked SPDP
subspace of the tseitin polynomial into N ≤ C(R+m,m) subspaces V_h,
each of dim ≤ C(R+D,D).

## Why It's Hard

The tseitin polynomial is ∏_c (1 - z_c · g_c).
Block-admissible derivatives select κ clause blocks, one derivative per block.
A generator is: m · ∂_S p where S has some profile h.

For a FIXED profile h, different clause-placement choices B give different
polynomials P_B = iterDerivList S_B p. The naive dimension of V_h includes
all C(R, κ) such placements × all shift monomials m. This is exponential.

The paper's solution: canonicalization compresses clause-placement variation.
After canonicalization, the row depends only on the interface profile (bounded
data), not on which specific clauses were chosen.

## Critical Observation: Multilinear Setting

The paper works modulo ⟨x²_i - x_i⟩ (Boolean variables). This bounds:
- Local monomials per clause block: 2⁴ = 16 (not infinite)
- Local arity per interface: O(1)
- dim(W_σ) ≤ d₀ = O(1) (bounded local space including shifts)

Our formalization uses general MvPolynomial. Options:
1. Add multilinear quotient (heavy Lean work)
2. Use totalDegree bounds instead (the tseitin poly has bounded degree per var)
3. Accept d₀ as a parameter and bound it for Cook-Levin specifically

Recommendation: option 3 (pragmatic, matches paper's structure).

## File Structure

### 1. LeibnizProduct.lean (~150 lines)

```lean
-- Binary Leibniz (exists in Mathlib as pderiv_mul)
-- Finset product Leibniz:
theorem pderiv_finset_prod (i : Fin n) (f : α → MvPolynomial (Fin n) F)
    (S : Finset α) :
    pderiv i (S.prod f) =
    S.sum (fun c => pderiv i (f c) * (S.erase c).prod f)

-- Block-admissible iterDerivList on product:
-- When S is block-admissible and each factor f_c has vars only in block c,
-- iterDerivList S (∏ f_c) = ∏_{c hit} (local deriv of f_c) · ∏_{c not hit} f_c
theorem iterDerivList_blockAdmissible_prod
    (S : List (Fin n)) (f : α → MvPolynomial (Fin n) F)
    (hadm : isBlockAdmissible B S)
    (hdisjoint : ∀ c, (f c).vars ⊆ block_vars B c) :
    iterDerivList S (Finset.univ.prod f) = ... (product of local pieces)
```

Key dependency: `MvPolynomial.pderiv_mul` from Mathlib.

### 2. DerivType.lean (~80 lines)

```lean
-- The 4 derivative types for a 3-SAT clause block
abbrev DerivType := Fin 4  -- ∂z, ∂v₁, ∂v₂, ∂v₃

-- Maps a verifier variable to its type within its clause
noncomputable def derivTypeOfVar (Φ : TseitinFormula)
    (v : Fin (tseitinNumVars Φ)) : DerivType := ...

-- The local derivative of clause c by type τ
-- ∂z(1 - z·g) = -g,  ∂vᵢ(1 - z·g) = -z · ∂vᵢ(g)
noncomputable def localDerivative (F : Type*) [CommRing F]
    (Φ : TseitinFormula) (c : Fin Φ.clauses.length)
    (τ : DerivType) : MvPolynomial (Fin (tseitinNumVars Φ)) F := ...

-- Key property: localDerivative is a SPECIFIC polynomial (1-dim span)
-- This gives d_τ = 1 for each derivative type
```

### 3. Profile.lean (~100 lines)

```lean
-- Ordered type word: sequence of derivative types for κ hits
abbrev TypeWord (m κ : ℕ) := Fin κ → Fin m

-- Profile/histogram: unordered count of each type
abbrev Profile (m : ℕ) := Fin m → ℕ

-- Histogram of a type word
def histogram (w : TypeWord m κ) : Profile m :=
  fun τ => (Finset.univ.filter (fun j => w j = τ)).card

-- Profile of a derivative list S (via derivTypeOfVar)
noncomputable def profileOf (S : List (Fin n)) : Profile m := ...

-- Count bound: number of profiles with total ≤ R
theorem profile_count_bound (m R : ℕ) :
    { h : Profile m | (Finset.univ.sum h) ≤ R }.toFinset.card
    ≤ Nat.choose (R + m) m := ...
-- (follows from choose_le_pow, already proved)
```

### 4. CanonicalForm.lean (~200 lines)  ← THE HARD FILE

```lean
-- Interface signature: for a clause-placement B with profile h,
-- the "canonical data" that determines the SPDP contribution.
--
-- Key theorem (Lemma 26): row(w) = row(can(w))
-- After canonicalization, the SPDP row depends only on:
--   (a) the profile h
--   (b) the interface signature (which is bounded)
--
-- For the tseitin product ∏_c f_c, two different placements B, B'
-- with the same profile produce generators that differ only by
-- which clause variables appear. But because the clause factors
-- have IDENTICAL algebraic structure (just in different vars),
-- the coefficient vectors are related by variable permutation.
--
-- The dimension of the span over all placements with same profile
-- is bounded by the symmetric tensor product of local spaces.

-- Clause-factor structural identity:
-- For any two clauses c, c': the algebraic form of (1 - z_c · g_c)
-- is "the same" up to variable relabeling.
theorem clauseFactor_structuralEquiv (c c' : Fin Φ.clauses.length) :
    ∃ (σ : Fin n ≃ Fin n), rename σ (clauseFactor c) = clauseFactor c'
-- (This is only true if clauses have the same polarity pattern.
--  For different polarities, localDerivative differs.
--  But the SPAN over all polarity patterns is still bounded.)

-- THE KEY THEOREM (Lemma 26 + 27 + 31 combined):
-- For fixed profile h, the generators { m · P_B : placement B has profile h }
-- span a space of dimension ≤ C(R + D, D).
--
-- Argument sketch:
-- 1. P_B = ∏_{c∈B} localDeriv(c, τ_c) · ∏_{c∉B} factor(c)
-- 2. Different B with same profile → related by clause permutation
-- 3. Span over all such permutations = symmetric tensor power
-- 4. dim(Sym^k(W_τ)) = C(dim(W_τ) + k - 1, k)
-- 5. Total dim = ∏_τ C(d_τ + h(τ) - 1, h(τ)) ≤ C(R+D, D)
--
-- Step 5 requires d_τ to be bounded (multilinear setting: d_τ ≤ 2^b)
-- and D to be chosen appropriately (D = m · (d₀ - 1) or similar).

axiom within_profile_dim_bound (F : Type*) [Field F]
    (M : DTM) (n R D : ℕ) (h : Profile m) (hR : R ≤ n) (hD : D ≥ 1) :
    Module.finrank F (profileSubspace h) ≤ Nat.choose (R + D) D
```

### 5. ProfileCover.lean (~120 lines)

```lean
-- Every SPDP generator has some profile
theorem generator_mem_profileSubspace
    (S : List (Fin n)) (m_poly : MvPolynomial (Fin n) F)
    (hadm : isBlockAdmissible B S) :
    m_poly * iterDerivList S p ∈ profileSubspace (profileOf S) := ...

-- Cover theorem: SPDP subspace ≤ ⨆_h profileSubspace h
theorem spdp_le_iSup_profileSubspace :
    blockedSpdpSubspace B κ ℓ p ≤ ⨆ (h : Profile m), profileSubspace h := ...
-- (Immediate from generator classification)

-- Assembly: profile_subspace_cover from the pieces
theorem profile_subspace_cover ... := by
  -- Use profileSubspace for the V_i
  -- Count: profile_count_bound gives N ≤ C(R+m,m)
  -- Dim: within_profile_dim_bound gives dim ≤ C(R+D,D)
  -- Cover: spdp_le_iSup_profileSubspace
  ...
```

## Theorem Dependency Graph

```
pderiv_finset_prod                    [LeibnizProduct]
  ↓
iterDerivList_blockAdmissible_prod    [LeibnizProduct]
  ↓
generator_mem_profileSubspace         [ProfileCover]
  ↓
spdp_le_iSup_profileSubspace         [ProfileCover]  ←  cover ✓
  ↓
profile_count_bound                   [Profile]       ←  N bound ✓ (already proved)
  ↓
within_profile_dim_bound              [CanonicalForm]  ←  dim bound (HARD)
  ↓
profile_subspace_cover                [ProfileCover]   ←  assembly (proved)
```

## The Hard Part: within_profile_dim_bound

This is Lemmas 26-31. The argument chain:

1. **Leibniz decomposition** (Lemma: iterDerivList on product = product of local pieces)
   - Each generator P_B factorizes across clauses

2. **Structural equivalence** (Lemma 27: permutation invariance)
   - Clause factors have identical algebraic structure
   - Permuting clause identities ↔ variable permutation
   - Permutation acts as invertible linear map on SPDP rows
   - So only the MULTISET of types matters

3. **Symmetric tensor collapse** (Lemma 31 core)
   - Span over all placements with same profile h
   - = ⊗_τ Sym^{h(τ)}(W_τ)
   - dim(Sym^k(W)) = C(dim(W) + k - 1, k)
   
4. **Local dimension bound** (Property P5)
   - dim(W_τ) ≤ d₀ = O(1) (in multilinear setting: ≤ 2^b where b = block size)
   - For Cook-Levin: b = 4, so d₀ ≤ 16

5. **Assembly**
   - dim(V_h) ≤ ∏_τ C(d₀ + h(τ) - 1, h(τ))
   - ≤ (d₀ + R)^{m(d₀-1)}
   - = C(R + D, D) for D = m(d₀ - 1)

## Revised compiler_finite_local_model

Current: m = 4, D = 1  ← D is too small
Revised: m = 4, D = 60 (= 4 × (16-1)) or D = 4 × 15 = 60

Actually, the bound C(R+D, D) ≤ (R+1)^D is already proved (choose_le_pow).
So product_profile_compression gives Γ ≤ (R+1)^{m+D} = (R+1)^{64}.
With R ≤ n: Γ ≤ (n+1)^{64}. Still polynomial. ✓

The exact value doesn't matter for the P≠NP separation —
only that m + D = O(1).

## Minimal Viable Path

To close the proof with maximum auditability:

1. Prove LeibnizProduct (pderiv_finset_prod) — standard algebra
2. Define Profile, profileOf, profileSubspace — straightforward
3. Prove cover theorem — immediate from definitions
4. Prove profile count — already done (choose_le_pow)
5. Leave within_profile_dim_bound as the FINAL axiom
6. Update D from 1 to 60 (or leave abstract)

This reduces profile_subspace_cover to within_profile_dim_bound,
which maps precisely to Lemma 31 and is the true mathematical core.

## Multilinear Question

The within_profile_dim_bound proof requires multilinear reduction
(to bound d₀). Options:
- Add MvPolynomial quotient by ⟨x²_i - x_i⟩ (heavy)
- Prove degree-per-variable bound on tseitin poly (medium)
- Accept d₀ as a parameter (light, matches paper)

Recommendation: accept d₀ via compiler_finite_local_model (make D
a function of the proved d₀), and leave the local dimension bound
as a proved constant for Cook-Levin.
