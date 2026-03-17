# SPDP Upper Bound Analysis — Open Issues

## Status
P_neq_NP proved with 3 custom axioms, 0 sorry. Build passes (3132 jobs).
But `decision_tree_spdp_rank` axiom is **provably false** — see below.

## The Counterexample

For AND of w live variables with k=ℓ=w (our formalization's parameters):

- The polynomial is ∏ X_i (product of all w live vars)
- The only nonzero k-th derivative (with distinct indices) is the constant 1
- Shifted SPDP generators: {m · 1 : deg(m) ≤ ℓ, vars(m) ⊆ liveVars}
- Over ℚ (our formalization): dimension = C(w+ℓ, ℓ) = C(2w, w)
- The axiom claims ≤ (k+1)·w

**Verified in Lean:**
- w=3: C(6,3) = 20 > 12 = (3+1)·3 ✗
- w=4: C(8,4) = 70 > 20 = (4+1)·4 ✗
- w=5: C(10,5) = 252 > 30 = (5+1)·5 ✗

Even with multilinear-only shifts (paper works over F_p):
- w=3: 2³ = 8 ≤ 12 ✓
- w=4: 2⁴ = 16 ≤ 20 ✓
- w=5: 2⁵ = 32 > 30 ✗ (STILL FAILS for w ≥ 5)

## Paper's Two P-Side Routes

The paper contains two distinct P-side upper bound arguments:

### Route A: Constant-parameter (Section 11 / Theorem 46 / local Appendix S)
- Uses k = ℓ = 4 (constant)
- Width-2 CNF has degree 2 < k = 4, so all 4th derivatives vanish
- SPDP rank = 0 ≤ (k+1)w = 5w trivially
- Bound: 5w = 5·O(log n) ≤ √N for large n
- **This route works** but is not the main/load-bearing theorem

### Route B: Compiled Θ(log n) (Sections 9, 17.3 / Theorem 92)
- Uses κ = ℓ = Θ(log n)
- "Polynomial Width⇒Rank via Constant-Type Profiles" (Section 9)
- "Global polynomial upper bound on Γ_{κ,ℓ}(P_{M,n})" (Section 17.3)
- **This is the main/load-bearing route** per the abstract and proof architecture
- Uses profile compression on compiled polynomial's sum-of-local-gates structure
- **We don't have these sections in our local copy** — newer arXiv version

## Paper's SPDP Definition (Definition 12)

Shifted SPDP matrix M^B_{κ,ℓ}(p):
- Rows indexed by pairs (τ, u) where |τ| = κ and deg(u) ≤ ℓ
- Entry = coeff_{x^β}(u · ∂^τ p)
- Γ^B_{κ,ℓ}(p) = rank of this matrix

Lemma 18: For multilinear p, Γ_{ℓ,ℓ}(p) ≤ C(N,ℓ) · 2^ℓ
- Key: admissible shifts have support ⊆ derivative set S
- At most 2^ℓ shifts per S (multilinear monomials with support ⊆ S)

## Our Formalization vs Paper

| Aspect | Our Formalization | Paper |
|--------|------------------|-------|
| Field | ℚ | F_p (safe prime > n^20) |
| Shifts | Any deg ≤ ℓ polynomial | Shifted, but Lemma 18 restricts to support ⊆ S |
| Parameters | k = ℓ = Nat.log 2 n | Load-bearing: κ = ℓ = Θ(log n) |
| P-side bound | (k+1)·w via decision tree | Profile compression (Sections 9/17.3) |

## What NOT to Do
- Do NOT switch to unshifted SPDP (paper is explicitly shifted)
- Do NOT tighten switching lemma by guesswork
- Do NOT change SPDP definition

## What TO Do Next
1. Obtain newer paper's Sections 9 and 17.3 for the compiled Θ(log n) route
2. Understand the profile compression argument
3. Restructure P-side axiom to match profile compression, not decision tree bound
4. Consider whether to work over F_p instead of ℚ (affects shift counting)
