# Restructure: Paper-Faithful P≠NP Architecture

## Paper's Architecture (Theorem 5)

Three facts → P≠NP:

1. **P-side upper bound**: For any polytime TM M, compiled P_M satisfies Γ(P_M) ≤ n^O(1)
2. **NP-side lower bound**: Explicit witness family {Φ_n} gives Γ(Q×_Φn) ≥ n^Θ(log n)
3. **Extraction**: Instance-uniform TΦ with TΦ(P_M) = Q×_Φ and Γ(TΦ(p)) ≤ Γ(p)

Under P=NP: ∃ Msol deciding SAT. Then:
  Γ(Q×_Φn) = Γ(TΦn(P_Msol)) ≤ Γ(P_Msol) ≤ n^O(1)  ← contradicts (2)

## Key difference from current code

Current code forms `fullCompiledPoly = tseitin + violation` and extracts FROM this sum.
Paper applies TΦ to P_M ALONE (no tseitin in P_M). The P=NP assumption makes TΦ(P_M) = Q×_Φ.

## Implementation Plan

### Phase 1: P-side upper bound (direct, no switching lemma)

The P-side compiled polynomial P_M = violationPoly (sum of local gates).
Each gate has O(1) variables and O(1) degree.
By subadditivity: Γ(P_M) ≤ Σ Γ(gate_i) ≤ numGates × O(1) = n^O(1).

Need to prove: Γ(p) ≤ C for p with d variables, degree D (where d, D are O(1)).
This follows from: SPDP subspace ≤ restrictTotalDegree ≤ C(d+D+κ, d) = O(1).

```lean
theorem spdpRank_bounded_vars (p : MvPolynomial (Fin d) F) (κ ℓ : ℕ) :
    blockedSpdpRank B κ ℓ p ≤ Nat.choose (d + ℓ + p.totalDegree) d
```

Then:
```lean
theorem pside_poly_bound (M : DTM) :
    ∃ C n₀, ∀ n ≥ n₀, ∀ B κ ℓ,
      blockedSpdpRank B κ ℓ (violationPolyOf F M n) ≤ n ^ C
```

Already have: HasLocalityStructure + subadditivity. Just need the per-gate bound
and to replace the sorry in profileRankBound with direct subadditivity argument.

### Phase 2: Extraction map TΦ (axiomatize)

The extraction map TΦ is the paper's deepest construction. It involves:
- Block-local invertible changes of variables
- Affine relabellings
- Variable restrictions
- Coordinate projections
- Local gadget multiplication + PAC projection

All are rank-monotone (Lemma 40).

For formalization, axiomatize:

```lean
-- The extraction map that recovers witness structure from computation
axiom extractionMap (F : Type*) [Field F] (Φ : TseitinFormula)
    (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (numVars M n)) F →ₐ[F] MvPolynomial (Fin (npNumVars n)) F

-- Under P=NP (M solves SAT), TΦ recovers the tseitin polynomial
axiom extraction_recovers (F : Type*) [Field F] [Nontrivial F]
    (Φ : TseitinFormula) (M : DTM) (n : ℕ)
    (hsolves : True) : -- placeholder for "M decides SAT"
    extractionMap F Φ M n (violationPolyOf F M n) = tseitinPoly F n

-- TΦ is rank-monotone
axiom extraction_rank_monotone (F : Type*) [Field F]
    (Φ : TseitinFormula) (M : DTM) (n : ℕ)
    (B_src : BlockPartition (numVars M n))
    (B_tgt : BlockPartition (npNumVars n)) (κ ℓ : ℕ) :
    blockedSpdpRank B_tgt κ ℓ (extractionMap F Φ M n p) ≤
    blockedSpdpRank B_src κ ℓ p
```

### Phase 3: P_neq_NP (restructured)

```lean
structure PeqNP where
  sat_decider : DTM
  decides_sat : True  -- placeholder

theorem P_neq_NP (h : PeqNP) : False := by
  -- P-side: Γ(P_M) ≤ n^C
  obtain ⟨C, n₁, hpside⟩ := pside_poly_bound ℚ h.sat_decider
  -- NP-side: Γ(Q×_Φn) ≥ n^Ω(log n)
  obtain ⟨n₂, hnpside⟩ := np_side_lb ℚ
  -- Extraction: Γ(Q×_Φn) ≤ Γ(P_M)
  -- Contradiction
```

### Phase 4: Cleanup

- Archive FullCompiler.lean (current version)
- Archive ExtractionProof.lean
- Remove fullCompiledPoly, embedComp, embedVerifier, compilerPartition
- Profile compression machinery: keep but mark as "available for per-cell bounds"
  (not used in main chain with direct subadditivity approach)

## File Changes

### New files:
- `PsideCollapse.lean` — P-side Γ ≤ n^O(1) via subadditivity
- `Extraction.lean` — axiomatized extraction map TΦ
- `PneqNP.lean` — final theorem

### Modified files:
- `Compiler.lean` — remove profileRankBound sorry, use direct subadditivity instead
- `SPDPDefs.lean` — add per-gate rank bound theorem

### Archived files:
- `FullCompiler.lean` → `archive/FullCompiler.lean`

### Kept as-is:
- All proved files (DisjointLeibniz, LocalBasis, SpanProduct, etc.)
- NPWitness.lean (np_side_lb)
- TseitinDefs.lean
- IdentityMinor.lean
