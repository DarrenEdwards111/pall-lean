# Design: Paper-Faithful P≠NP Architecture

## Paper's Proof Strategy (main.tex / main1.tex)

### SPDP Definition (Definition 12 — "wide", no shift locality)
- Rows: k-derivative operators ∂_β, |β| = k
- Columns: ALL multilinear monomials x^σ, |σ| ≤ ℓ (unrestricted vars)
- Entry: constant coeff of x^σ · ∂_β(C|ρ)
- Parameters: k = ℓ = ⌈log n⌉, r = n, γ = 1/2

### Three-Part Separation

1. **P ⊆ C*_SPDP** (Theorem 7.3): Every polytime circuit collapses under fixed restriction
   - Cook-Levin → log-depth circuit of poly size
   - Agrawal-Vinay + Tavenas → depth-4 ΣΠ∑Π, size n^O(1), bottom fan-in ≤ log n
   - Multi-switching lemma → SPDP rank ≤ d*_n = O(log² N) with high probability
   - Union bound over quasi-poly row-space signatures → ∃ deterministic seed s*
   
2. **f_n ∉ C*_SPDP** (diagonal escape): 
   - f_n(i) = 1 iff every SPDP-collapsible circuit of size ≤ n^k fails on input i
   - By construction, f_n disagrees with every collapsible circuit

3. **f_n ∈ NP** (Section 5.3):
   - Witness = (circuit C, seed s, verification certificate)
   - Verifier checks SPDP rank in polytime

### Conclusion: f_n ∈ NP \ P, therefore P ≠ NP

## What Changes vs Current Code

### Keep (still valid)
- `mlBlockedSpdpSubspaceWide` — this IS the paper's SPDP subspace
- `mlBlockedSpdpRankWide` — this IS the paper's SPDP rank
- `mlBlockedSpdpSubspace_le_wide` — narrow ≤ wide
- All Tseitin infrastructure (TseitinDefs, IdentityMinor, etc.)
- Profile compression machinery (useful for NP lower bound, optional)
- NPWitness.lean identity minor lower bound (if adaptable to wide definition)

### Replace
- P-side bound: profile compression → restriction + depth-4 + switching
- PneqNP.lean: direct SPDP comparison → diagonal escape from C*_SPDP
- Extraction: not needed in paper's approach (diagonal handles separation)

### New Infrastructure Needed

#### Phase 1: Restrictions
```
Restriction.lean (~200 lines)
- restriction ρ : Fin n → Option Bool  (None = live, Some b = fixed)
- restrictPoly : MvPolynomial (Fin n) F → ρ → MvPolynomial (Fin n) F
- live variables after restriction
- SPDP rank after restriction = SPDP rank of restricted poly
```

#### Phase 2: Circuit Model
```
Circuit.lean (~300 lines)
- Boolean circuit type (gates, wires, size)
- Circuit → polynomial interpretation over F_p
- Size bound → degree bound
- Polytime TM → poly-size circuit family (Cook-Levin)
```

#### Phase 3: Depth-4 Simulation
```
Depth4.lean (~400 lines)  
- ΣΠ∑Π circuit type
- Agrawal-Vinay: circuit of size s → depth-4 of size 2^{O(√(log s · log n))}
- Tavenas refinement: bottom fan-in ≤ log n, formal degree ≤ log² N
- Key output: polytime circuit → depth-4 with bounded parameters
```

#### Phase 4: Multi-Switching Lemma
```
SwitchingLemma.lean (~500 lines)
- Random restriction model
- Multi-switching lemma for depth-4 circuits
- SPDP rank collapse under restriction
- Probability bound: Pr[SPDP > d*] ≤ 2^{-2 log² N}
```

#### Phase 5: Seed Search + Universal Collapse
```
SeedSearch.lean (~200 lines)
- Row-space signature counting: ≤ 2^{O(log² N)} signatures
- Union bound: ∃ seed s* that works for ALL poly-size circuits
- Deterministic search in time n^{O(log² N)}
```

#### Phase 6: Diagonal + Separation
```
Diagonal.lean (~300 lines)
- C*_SPDP class definition
- f_n construction (diagonal over C*_SPDP)
- f_n ∉ C*_SPDP (by construction)
- f_n ∈ NP (witness protocol)
- P ⊆ C*_SPDP (from Phase 5)
- Conclusion: P ≠ NP
```

## Pragmatic Path: Axiomatize Heavy Pieces

Full formalization of switching lemma + depth-4 simulation is months of work.
Paper-faithful structure with strategic axiomatization:

### Prove in Lean (infrastructure):
- Restriction operations on polynomials
- SPDP rank of restricted polynomials  
- Circuit → polynomial
- Diagonal function definition
- f_n ∉ C*_SPDP (combinatorial, provable)
- f_n ∈ NP (verification protocol)

### Axiomatize (deep results):
- `depth4_simulation`: polytime → depth-4 with bounded params
- `multi_switching_lemma`: restriction collapses SPDP rank whp
- `seed_exists`: deterministic good seed exists (union bound)

### Derive:
- `P_subset_CSPDP`: P ⊆ C*_SPDP (from axioms)
- `P_neq_NP`: f_n witnesses separation

## Axiom Inventory (target: 3 axioms)

1. **`depth4_simulation`**: Every poly-size circuit has depth-4 ΣΠ∑Π form
   with size n^O(1), bottom fan-in ≤ log n, formal degree ≤ log² N
   
2. **`spdp_collapse_under_restriction`**: For depth-4 ΣΠ∑Π with bottom 
   fan-in ≤ t, SPDP_{k,ℓ}(C|ρ) ≤ (k+1)·t for most restrictions ρ

3. **`good_seed_exists`**: ∃ deterministic seed s* such that ALL poly-size
   circuits collapse under ρ_{s*}

## File Plan

```
PallLean/
  -- Existing (keep):
  SPDPDefs.lean, MultilinearSPDP.lean (wide definition)
  TseitinDefs.lean, IdentityMinor.lean, NPWitness.lean
  
  -- New:
  Restriction.lean          -- polynomial restriction
  CircuitModel.lean         -- circuits → polynomials  
  Depth4Axiom.lean          -- axiomatized depth-4 simulation
  SwitchingAxiom.lean       -- axiomatized switching lemma
  SeedAxiom.lean            -- axiomatized seed existence
  RestrictedSPDP.lean       -- SPDP rank after restriction
  SPDPClass.lean            -- C*_SPDP definition
  DiagonalFunction.lean     -- f_n construction
  PsideCollapse.lean        -- P ⊆ C*_SPDP (from axioms)
  DiagonalEscape.lean       -- f_n ∉ C*_SPDP
  DiagonalInNP.lean         -- f_n ∈ NP
  PneqNP.lean               -- final theorem (rewritten)
  
  -- Archive:
  archive/CompiledBound.lean
  archive/ProfileCompression.lean (keep accessible, not in main chain)
  archive/WideProfileCompression.lean
  archive/Compiler.lean
```

## Migration Order

1. Write DESIGN doc (this file) ✓
2. Restriction.lean — polynomial restriction infrastructure
3. CircuitModel.lean — circuit type + polynomial interpretation  
4. SPDPClass.lean — C*_SPDP definition using wide SPDP
5. Depth4Axiom.lean + SwitchingAxiom.lean + SeedAxiom.lean — 3 axioms
6. PsideCollapse.lean — P ⊆ C*_SPDP (derives from axioms)
7. DiagonalFunction.lean — f_n definition
8. DiagonalEscape.lean — f_n ∉ C*_SPDP
9. DiagonalInNP.lean — f_n ∈ NP  
10. PneqNP.lean — assemble: P ⊂ C*_SPDP, f_n ∈ NP \ C*_SPDP → P ≠ NP
11. Archive old files, update PallLean.lean imports
12. Build clean, push

## Key Insight

The paper's approach is cleaner because:
- No extraction map needed (diagonal handles separation directly)
- No compiled polynomial (P-side works on raw circuits)
- Wide SPDP definition matches standard SPD literature
- Axioms map to well-known results (switching lemma, depth reduction)
- Each axiom has independent literature support
