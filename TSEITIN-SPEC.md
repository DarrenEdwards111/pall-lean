# Correct Tseitin Construction — Specification

## Problem with current `buildTseitin`

The current construction creates clauses with PRIVATE variables per clause:
- Clause e: var1=e, var2=E+e, var3=2E+e
- No variable sharing between clauses
- This makes the coupled verifier a product of INDEPENDENT factors
- SPDP rank = C(n, log n) ≈ n^{log n} — SUPERPOLYNOMIAL
- The axiom `tseitin_spdp_rank_bound ≤ n^200` is FALSE for this construction

## Correct Tseitin encoding

### Graph: 3-regular graph on n vertices
- Need degree ≥ 3 for width-3 clauses without auxiliaries
- 3-regular graph has 3n/2 edges (n must be even)
- Use Petersen-type construction or explicit 3-regular graph

### Variables
- E = 3n/2 edge variables: x_0, ..., x_{E-1}
- No auxiliary variables needed for degree-3 XOR→3-CNF

### Clauses per vertex
For vertex v with incident edges e₁, e₂, e₃:
- Parity constraint: x_{e₁} ⊕ x_{e₂} ⊕ x_{e₃} = b_v
- 4 clauses (for b_v = 0):
  1. (x_{e₁} ∨ x_{e₂} ∨ x_{e₃})
  2. (x_{e₁} ∨ ¬x_{e₂} ∨ ¬x_{e₃})
  3. (¬x_{e₁} ∨ x_{e₂} ∨ ¬x_{e₃})
  4. (¬x_{e₁} ∨ ¬x_{e₂} ∨ x_{e₃})
- For b_v = 1: flip all signs

### Variable sharing
- Edge e = (u,v) → x_e appears in clauses at vertex u AND vertex v
- Two clauses at adjacent vertices share exactly one edge variable
- Each edge variable appears in exactly 8 clauses (4 at each endpoint)
- Each clause has exactly 3 variables (the 3 edges incident to its vertex)

### Key structural properties
1. **Global edge-variable identity**: one variable per edge, shared across vertices
2. **Vertex-local clause generation**: each vertex generates 4 clauses using its 3 incident edges
3. **Bounded overlap**: two clause gadgets interact iff their vertices share an edge
   - On a 3-regular graph: each vertex has 3 neighbors
   - Each vertex's gadget (4 clauses) overlaps with at most 3 other vertex gadgets
   - Each clause overlaps with ≤ 12 other clauses (4 clauses × 3 neighbors)

### SPDP structure
- Selectors: one per clause (4n total)
- Body variables: edge variables (3n/2 total), shared between clauses
- Block partition: selector blocks are singletons; body variables grouped by edge
- Admissible derivative lists pick ≤ 1 element per block
- Neighbor structure: clauses at adjacent vertices share variables
  → profile compression can bound SPDP rank polynomially

### What changes in the proof
- `clauseVarSet` now has shared variables between clauses
- `conflicting_card_le` holds with the constant from the degree bound
- `neighborClauses w` is non-empty (as intended)
- `windowProfile` has non-trivial histograms
- Profile compression theorem becomes meaningful

## Implementation plan
1. Define a 3-regular graph (e.g., Cayley graph on Z/nZ with generators {1, -1, n/2})
2. Rewrite `buildTseitin` to use edge variables + proper XOR→3-CNF encoding
3. Update `tseitinNumVars`, `clauseVarSet`, gadget definitions
4. Verify `conflicting_card_le` still holds (now with actual conflicts)
5. Verify `bounded_occurrence` (each edge var in ≤ 8 clauses)
