import PallLean.SPDPDefs
import PallLean.TuringMachine
import PallLean.Tseitin
import Mathlib.Tactic
/-!
# Construction Axioms — Documentation and Decomposition

This file documents the remaining construction axioms in the Pall formalization,
explaining what each asserts, why it's true, and what would be needed to prove it.

## Axiom Classification

### Tier 1: Could be proved with moderate effort
- `compilationConstraints` — Algorithmic construction from TM
- `tseitinAt` / `tseitinAt_graph` / `tseitinAt_vertices` — Combinatorial construction
- `restriction_rank_le_axiom` — Linear algebra (matrix factorization)

### Tier 2: Requires substantial formalization infrastructure
- `binomial_lower_bound_axiom` — Real analysis (asymptotic dominance)
- `compilationConstraints_length` — Polynomial arithmetic bound

### Tier 3: Requires deep mathematics
- `ramanujanFamily` — Algebraic number theory (LPS/Morgenstern construction)

## Detailed Documentation

### `compilationConstraints` (Compiler.lean)

**Statement**: For any DTM M and input size n, produce a list of
`LocalConstraint M n (log₂ n) F`, each a polynomial over ≤6 variables.

**Construction** (§3.1 of Pall):
For each cell (t, i) in the T(n) × S(n) computation tableau:

1. **Booleanity**: z(1-z) = 0 for each variable z (1 variable each)
2. **One-hot state**: (Σ_q s_{t,q}) - 1 = 0 (numStates variables)
3. **One-hot head**: (Σ_i h_{t,i}) - 1 = 0 (tapeSize variables — NOT local!)
4. **Transition**: For head at position i at time t:
   b_{t+1,i} = δ_write(state_t, b_{t,i}) when head is at i
   b_{t+1,i} = b_{t,i} when head is not at i
   These involve variables {b_{t,i}, b_{t+1,i}, s_{t,q}, h_{t,i}, h_{t+1,i'}} — ≤6 vars

The key insight: constraints 1,2,4 are truly local (≤6 vars). Constraint 3
(one-hot head) is global but can be decomposed into local pairwise constraints
h_{t,i} · h_{t,j} = 0 for |i-j| > 0 (2 variables each) plus Σ h_{t,i} ≥ 1
(encoded via the transition constraints).

**Why axiom**: Full construction requires careful index arithmetic mapping
DTM transitions to polynomial constraints. Provable but tedious.

### `ramanujanFamily` (NPWitness.lean)

**Statement**: There exists a family of d-regular graphs {G_n} satisfying:
- Constant degree d
- n vertices at parameter n
- Girth Ω(log n) (Ramanujan spectral gap implies this)

**Construction** (§8.1):
The Lubotzky–Phillips–Sarnak (1988) construction:
- Fix primes p, q with p ≡ 1 (mod 4), (p/q) = -1
- Vertices: PGL(2, F_q) or PSL(2, F_q)
- Edges: Cayley graph with p+1 generators from Hurwitz quaternions
- The Ramanujan–Petersson conjecture (Deligne 1974) gives λ₂ ≤ 2√p

**Why axiom**: Proving the Ramanujan property requires:
1. Explicit quaternion algebra generators
2. Hecke operator theory on automorphic forms
3. Deligne's theorem (Weil conjectures) for the spectral bound
This is ~1000 pages of algebraic geometry. The existence of such families
is universally accepted in TCS.

### `tseitinAt` (NPWitness.lean)

**Statement**: For each n, construct a TseitinFormula on ramanujanFamily.graph n.

**Construction** (§8.2):
1. Set parity bits: b_0 = 1, all others 0 (odd total parity → unsatisfiable)
2. For each vertex v with incident edges e₁,...,e_d:
   XOR constraint: x_{e₁} ⊕ ... ⊕ x_{e_d} = b_v
3. Decompose each d-ary XOR into 3-CNF using auxiliary variables:
   x₁ ⊕ x₂ = y₁ (4 clauses), y₁ ⊕ x₃ = y₂ (4 clauses), etc.
   Total: 4(d-1) clauses per vertex, each with 3 literals

**Properties**:
- `tseitinAt_graph`: graph = ramanujanFamily.graph n (by construction)
- `tseitinAt_vertices`: numVertices = n (from ramanujanFamily.vertices_linear)
- Bounded occurrence: each edge variable in ≤ 2 vertices × 4(d-1) clauses
- Total clauses: 4(d-1)n ≤ 10n (for d ≤ 3.5)

**Why axiom**: The XOR→3-CNF decomposition is standard but requires
tracking clause-variable incidence through the encoding. Could be
formalized with ~200 lines of combinatorial bookkeeping.

### `binomial_lower_bound_axiom` (NPWitness.lean)

**Statement**: ∃ n₀, ∀ n ≥ n₀, C(n/30, log₂ n) ≥ n^{log₂ n / 4}

**Proof sketch**:
1. C(L, k) ≥ (L/k)^k (standard: each of k factors ≥ L-k+1/k ≥ L/(2k))
2. L = n/30, k = log₂ n: C(n/30, log n) ≥ (n/(30 log n))^{log n}
3. For n ≥ 2^40: n^{1/4} ≥ 30 log₂ n, so n/(30 log n) ≥ n^{3/4}
4. Therefore C(n/30, log n) ≥ n^{3 log n / 4} ≥ n^{log n / 4}

**Why axiom**: Step 3 requires showing n^{1/4} eventually dominates 30 log₂ n.
In Lean's Nat arithmetic, this needs careful bounds. With Mathlib's Real.log,
one could formalize this as: ∀ ε > 0, ∃ N, ∀ n ≥ N, n^ε > C · log n.

### `restriction_rank_le_axiom` (RestrictionProof.lean)

**Statement**: spdpRank κ ℓ (f|_{x_i=c}) ≤ spdpRank κ ℓ f

**Proof** (§2, Property 3):
The SPDP matrix M(f|_{x_i=c}) = Z · M(f) · T where:
- Z zeros rows with i ∈ S (derivative ∂_i is trivial after substitution)
- T maps column x^β to Σ_k c^k · column x^{β+k·eᵢ} (evaluation map)
Since rank(ZAT) ≤ rank(A), we get rank(f') ≤ rank(f).

**Why axiom**: Requires Module.finrank ↔ matrix rank bridge (CoeffBridge.lean).
Not in the P≠NP proof chain — included for completeness only.
-/

namespace ConstructionAxioms

-- This file is documentation-only. No new definitions or theorems.
-- All axioms remain in their original files for import compatibility.

end ConstructionAxioms
