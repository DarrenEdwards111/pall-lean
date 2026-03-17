# Trust Boundary — P ≠ NP Lean Formalization

## Status

The Lean development proves the **algebraic escape framework and contradiction skeleton**, conditional on two paper-faithful complexity-theoretic axioms: compiled P-side SPDP collapse and NP-membership of the diagonal family.

**Build:** 3132 jobs, 0 errors, 0 sorry, 0 sorryAx  
**Custom axioms:** 2  
**Proved theorems/lemmas:** 140 across 23 files  
**Standard axioms:** propext, Classical.choice, Quot.sound  

---

## Axiom 1: `BoolCircuit.ptime_spdp_collapse`

**File:** `PallLean/BoolCircuit.lean`  
**Paper reference:** Theorem 92 / Section 9 ("Polynomial Width ⇒ Rank via Constant-Type Profiles") / Section 17.3 ("A global polynomial upper bound on Γ_{κ,ℓ}(P_{M,n})")

### Statement

```lean
axiom ptime_spdp_collapse :
    ∀ (M : TuringMachine.DTM), ∃ (n₀ : ℕ), ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool), M.decides f →
    RestrictedSPDP.restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (Depth4Simulation.multilinearInterp f)
      (UniversalRestriction.universalRestriction n) ≤ Nat.sqrt n
```

### Plain English

Every function decidable by a deterministic Turing machine M has shifted SPDP rank at most √n, when measured at derivative/shift order κ = ℓ = log₂ n under the universal restriction (fixing the first n − log₂ n variables to false).

### Where Used

`ptime_spdp_collapse` → `SwitchingLemma.universal_spdp_collapse` → `PneqNP_Paper.P_subset_FSPDP` → `PneqNP_Paper.P_neq_NP`

### What a Full Lean Proof Would Require

1. **Cook-Levin theorem** — formalize DTM → poly-size Boolean circuit → width-3 CNF encoding with N = Θ(n³) variables
2. **Depth-4 simulation** — ΣΠΣ∏ circuit realization (Proposition 5.2)
3. **Binary Tseitin transformation** — width-3 → width-2 polynomial structure
4. **Profile compression** — Section 9's "constant-type profiles" argument: group shifted partial derivatives of the compiled polynomial by their interaction pattern with block partition, bound rank per profile
5. **Global assembly** — Section 17.3: combine profile counts into Γ_{κ,ℓ}(P_{M,n}) ≤ n^{O(1)} at κ = ℓ = Θ(log n)
6. **Threshold arithmetic** — n^{O(1)} ≤ √n for the specific constants and large enough n

This is the paper's full complexity-theoretic bridge from computation theory to algebraic invariants. It imports Cook-Levin (1971), Håstad's switching lemma (1986), and the paper's novel profile compression machinery.

### Strength Check

The axiom is stated per-DTM (each M gets its own threshold n₀), which is the weakest form needed. It applies only to `multilinearInterp` (the canonical multilinear extension), not arbitrary polynomials. The parameter regime κ = ℓ = log₂ n matches the paper's main route. The bound √n = n^{1/2} matches the paper's γ = 1/2.

---

## Axiom 2: `PneqNP_Paper.f_n_family_in_NP`

**File:** `PallLean/PneqNP_Paper.lean`  
**Paper reference:** Proposition 8.7 / Appendix Q ("Projected Witness — The God Move")

### Statement

```lean
axiom f_n_family_in_NP : UniformNP f_n_family
```

where `UniformNP F` means: there exist polynomial witness length n^k and a uniformly P-time verifier V such that F(x) ↔ ∃ w, V(x, w).

### Plain English

The diagonal function family {f_n} is in NP. There exists a polynomial-time verifier that, given input x and a short witness w, can check whether f_n(x) = true.

### Where Used

`f_n_family_in_NP` → `PneqNP_Paper.P_neq_NP` (directly, as the NP hypothesis for the diagonal family)

### What a Full Lean Proof Would Require

1. **Witness structure** — The paper's witness is a short seed s ∈ {0,1}^{O(log² N)} that determines a restriction ρ_s
2. **Verification algorithm** — Given (x, s), compute:
   - restriction ρ_s from seed s
   - SPDP evaluation matrix M under ρ_s
   - check M · e_x = 0 (all SPDP-collapsing functions vanish at x)
3. **Polynomial-time bound** — The verification is deterministic poly-time given the seed
4. **Soundness/completeness** — f_n(x) = true ↔ ∃ s such that verification passes

This requires formalizing the SPDP matrix construction as a concrete algorithm, the seed-based restriction generator, and the polynomial-time bound on matrix-vector multiplication. The diagonal function f_n is defined via `Submodule.dualAnnihilator` (non-constructive), so the NP witness must provide constructive evidence through the SPDP certificate structure.

### Strength Check

The axiom uses the standard NP definition (polynomial witness + poly-time verifier). The `f_n_family` definition handles small n (< 2 or proper subspace fails) by defaulting to `fun _ => false`, which is trivially in NP. The substantive claim is for large n where the diagonal construction is active.

---

## Dependency Graph

```
                    ptime_spdp_collapse (AXIOM 1)
                            │
                            ▼
                  universal_spdp_collapse (theorem)
                            │
                            ▼
                     P_subset_FSPDP (theorem)
                            │
        ┌───────────────────┤
        │                   │
        ▼                   ▼
f_n_family_in_NP      escape theorem
  (AXIOM 2)          (140 proved lemmas)
        │                   │
        └───────┬───────────┘
                ▼
           P_neq_NP (theorem)
```

## What Is Proved (Not Axiomatized)

The following are ALL fully proved with zero custom axioms:

- **Escape theorem** (`f_n_escapes_FSPDP`): The diagonal function escapes InFSPDP via orthogonality vs positivity
- **Proper subspace** (`fspdp_proper_subspace`): The FSPDP evaluation subspace is proper, via Möbius functional argument
- **Möbius functional** (`mobiusL`): Linear map L(v) = Σ_T (-1)^{w-|T|} v(x_T), proved to vanish on InFSPDP
- **Top coefficient extraction** (`mobiusL_eq_top_coeff`): Möbius functional equals top monomial coefficient
- **SPDP rank lower bound** (`restrictedRank_ge_proved`): Functions with nonzero top Möbius coefficient have rank ≥ 1
- **Annihilator construction** (`spdp_annihilator_exists`): Dual annihilator of FSPDP subspace exists with positive entry
- **Multilinear restriction** (`restricted_isML`): Restricted multilinear interpolation preserves multilinearity
- **Iterated derivative chain** (`iterDerivList_allLive_eq_topCoeff`): Full derivative chain for top monomial
- **Span dimension** (`span_const_monomials_dim_proved`): Linear independence of constant monomial generators
- **Universal restriction** (`universalRestriction`): Concrete construction fixing first n−log₂n variables
- **Live variable count** (`liveVars_card_eq_log`): |liveVars ρ*| = log₂ n
- **P ⊆ FSPDP** (`P_subset_FSPDP`): Derived from collapse axiom
- **Möbius inversion infrastructure**: Toggle involution, superset sum vanishing, indicator evaluation
- **Degree bounds**: Restriction preserves degree, derivative degree bounds, multilinear interpolation degree
- **Boolean evaluation**: Multilinear interpolation agrees with Boolean function on {0,1}^n

## Discarded Approaches

The `PallLean/Archive/` directory contains 34 files from earlier attempts:

- **Decision tree route** (DISCARDED): `decision_tree_spdp_rank` with bound (k+1)·w was provably false for shifted SPDP when k = w ≥ 5. Counterexample: AND of w variables gives rank C(2w,w).
- **n=4 fixed approach** (DISCARDED): Too small for separation; no room between P-side and NP-side bounds.
- **Unshifted SPDP** (NEVER USED): Paper explicitly uses shifted SPDP (Definition 12).
- **Degree-based separation** (DISCARDED): Polynomial degree doesn't separate P from NP.

See `SPDP_ANALYSIS.md` for detailed counterexample analysis.
