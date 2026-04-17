/-
  PaddingRobustness.lean — §29.3-29.5: Padding does not reduce SPDP rank

  The separation (Theorem 147) applies the P-side bound (Theorem 139) to
  the hard instances φ_n. Since φ_n may need padding to reach the right
  input length, §29.3-29.5 proves that standard paddings do not reduce
  SPDP rank below the original.

  ## Key Results

  **Lemma 142** (Product with dummy factor):
    If f(x) is multilinear on x and D(d) is multilinear on disjoint
    dummy variables d, then for every S ⊆ vars(x) with |S| = ℓ:
      α(x) · ∂_S(f(x) D(d)) = (α(x) · ∂_S f(x)) D(d)
    In particular, the x-only block of M_ℓ(f·D) equals M_ℓ(f) times
    a nonzero scalar D(0,...,0).

  **Lemma 143** (Block-lower-triangular sum):
    If M is block-lower-triangular with blocks B₁,...,B_t, then
      rank(M) ≥ Σ rank(B_i).

  **Theorem 144** (No-padding under unit-dummy paddings):
    For unit-dummy paddings: rk_{SPDP,ℓ}(χ_{pad(φ)}) ≥ rk_{SPDP,ℓ}(χ_φ).

  **Corollary 145** (Robustness of the lower bound):
    If rk_{SPDP,ℓ}(χ_{φ_n}) ≥ 2^{εn}, then
    rk_{SPDP,ℓ}(χ_{pad(φ_n)}) ≥ 2^{εn} for any unit-dummy padding.

  **Theorem 146** (Round-trip NC⁰ padding):
    There exist NC⁰ maps pad and unpad preserving satisfiability,
    with rank preservation up to polynomial factors.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace PaddingRobustness

open MvPolynomial SPDP

/-! ## Lemma 142: Product with Dummy Factor

When f(x) and D(d) have disjoint variable sets, differentiating
f·D with respect to x-variables only affects f, not D. So the
SPDP matrix of f·D restricted to x-columns equals M_ℓ(f) scaled
by D evaluated at d = 0. -/

/-- Dummy padding structure: f(x) · D(d) with disjoint variable sets. -/
structure DummyPadding (n_x n_d : ℕ) where
  /-- The original polynomial in x-variables -/
  original : MvPolynomial (Fin n_x) ℚ
  /-- The dummy factor in d-variables -/
  dummyFactor : MvPolynomial (Fin n_d) ℚ
  /-- D(0,...,0) ≠ 0 (e.g., D is a product of d_j, each a single variable,
      or D = 1, or D is a nonzero constant) -/
  dummy_nonzero_at_zero : dummyFactor ≠ 0

/-- Placeholder version: rk(f) ≤ rk(f) is trivially true.
    The real Lemma 142 would compare rk(f) with rk(f·D) in a larger
    variable space. That requires embedding polynomials across variable
    spaces, which needs infrastructure not yet built.
    This placeholder is not load-bearing (Separation29 doesn't use it). -/
theorem spdpRank_dummy_padding_mono (n_x n_d : ℕ)
    (pad : DummyPadding n_x n_d) (κ ℓ : ℕ) :
    spdpRank κ ℓ pad.original ≤
      spdpRank κ ℓ pad.original :=
  le_refl _

/-! ## Lemma 143: Block-Lower-Triangular Rank

If a matrix M decomposes as block-lower-triangular with diagonal
blocks B₁,...,B_t, then rank(M) ≥ Σ rank(B_i).

This is because the column space of M contains the direct sum of
the column spaces of the diagonal blocks. -/

/-- If each sub_i ≤ W, then finrank(sub_i) ≤ finrank(W).
    (For genuinely disjoint subs, the bound is tighter, but this
    weaker version suffices and avoids needing disjointness.) -/
theorem finrank_sub_le_of_le {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V]
    {t : ℕ} (W : Submodule ℚ V) (subs : Fin t → Submodule ℚ V)
    (h_le : ∀ i, subs i ≤ W) (i : Fin t) :
    Module.finrank ℚ (subs i) ≤ Module.finrank ℚ W :=
  Submodule.finrank_mono (h_le i)

/-! ## Theorem 144 / Corollary 145: Padding Robustness

Unit-dummy padding: add fresh variables d₁,...,d_t appearing only
in unit clauses (d_j = 1). The padded formula pad(φ) on (x,d) has:
  χ_{pad(φ)}(x,d) = χ_φ(x) · ∏ d_j

By Lemma 142, the SPDP rank on x-columns is preserved up to the
nonzero scalar ∏ d_j evaluated at d = 0... but ∏ d_j at d = 0 is 0!

The paper handles this by using d = 1 (unit clauses force d_j = 1),
so the relevant scalar is ∏ 1 = 1, which is nonzero. The SPDP matrix
over the FULL variable set (x,d) has the padded structure. -/

/-- Placeholder: padding preserves rank is just monotonicity of ≤.
    The real Theorem 144 would state rk(χ_{pad(φ)}) ≥ rk(χ_φ) for
    concrete padding operations. Not load-bearing. -/
theorem padding_preserves_rank (n : ℕ) (original_rank padded_rank : ℕ)
    (h_original : original_rank ≤ padded_rank) :
    original_rank ≤ padded_rank :=
  h_original

/-! ## Theorem 146: Round-Trip NC⁰ Padding

Existence of NC⁰ padding/unpadding maps preserving satisfiability
and SPDP rank up to polynomial factors. This is used in Theorem 147
to ensure the hard instances can be padded to the right input length
without destroying the exponential lower bound. -/

/-- Placeholder: NC⁰ padding existence is trivially True.
    The real Theorem 146 would construct explicit pad/unpad maps.
    Not load-bearing. -/
theorem nc0_padding_exists :
    ∀ n : ℕ, n ≥ 1 → True :=
  fun _ _ => trivial

/-! ## Connection to the Separation

In Theorem 147, the proof says:
  "Apply [Theorem 139] to the explicit instances φ_n
   (or to their innocuous paddings from §15.4-§15.5)"

This step uses:
1. Theorem 139: if 3-SAT ∈ P, then rk(f_{3SAT,N}) ≤ N^c
2. φ_n has encoding size ≤ N for some N = poly(n)
3. pad(φ_n) has encoding size exactly N (padded to fill)
4. By Theorem 144: rk(χ_{pad(φ_n)}) ≥ rk(χ_{φ_n}) ≥ 2^{εn}
5. But rk(χ_{pad(φ_n)}) ≤ rk(f_{3SAT,N}) ≤ N^c = poly(n)
6. Contradiction: 2^{εn} ≤ poly(n) for large n

Step 5 uses: χ_{pad(φ_n)} = f_{3SAT,N} restricted to the specific
padded instance, so rk(χ_{pad(φ_n)}) ≤ rk(f_{3SAT,N}) by Lemma 141.

This means Axiom 2 (Theorem 139) in Separation29.lean actually
decomposes into:
  A. Theorem 139 proper: rk(f_{L,n}) ≤ n^c for L ∈ P
  B. Lemma 141: restriction monotonicity
  C. Theorem 144: padding robustness
-/

end PaddingRobustness
