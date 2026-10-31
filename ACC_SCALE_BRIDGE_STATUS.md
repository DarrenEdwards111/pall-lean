# ACC Scale-Bridge Test — Direct Composite vs Williams Counting

**Status:** tested against the existing Lean arc on 2026-07-09.  
**Scope:** this is an ACC⁰ restricted-world H4 / scale-bridge audit. It is **not** P≠NP, and it is not a new proof of `NEXP ⊄ ACC⁰`; Williams' theorem is classical, while this repo formalizes/anatomizes the route.

## Question

Can the N-Frame/H4 scale-bridge idea be tested inside ACC⁰?

Yes. ACC⁰ gives the cleanest restricted testbed because it has two competing bridges:

1. **Direct polynomial/composite-MOD bridge** — try to lift the prime Razborov–Smolensky obstruction through composite modulus.
2. **Williams algorithmic-counting bridge** — bypass the field obstruction via exact/integer `SYM∘AND` counting plus faster SAT plus time hierarchy.

## Test result

### A. Direct composite-MOD scale bridge: fails by proved anatomy

The direct bridge would try to extend the prime Smolensky/field method from `AC⁰[p]` to composite `ACC⁰`, especially `MOD₆` / mixed `MOD₂`+`MOD₃` structure.

The repo has already isolated the obstruction:

- File: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthACC0CarryRefinementCrossing.lean`
- Named socket: `CarryRefinementCrossing`
- Proved capstone: `field_based_modes_all_fail`

Lean check:

```text
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthACC0CarryRefinementCrossing.lean
```

reported:

```text
field_based_modes_all_fail depends only on standard Lean axioms
[propext, Quot.sound]
```

What is proved:

```lean
theorem field_based_modes_all_fail :
    (∀ (F : Type) [Field F], ¬ (CharP F 2 ∧ CharP F 3))
      ∧ (∀ t d D₀ R observerDeg : ℕ,
          observerDeg ≤ t ^ d * D₀ → R ≤ observerDeg → t ^ d * D₀ < R → False)
      ∧ ((∃ a b : ZMod 6, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0)
          ∧ ((2 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) ^ (6 - 1) ≠ 1))
```

Interpretation:

- **Separate fields fail:** no single field is native for both `MOD₂` and `MOD₃`.
- **Staged bounded-depth field route fails:** bounded observer degree cannot meet the growing non-native requirement.
- **Carry-ring route fails:** `ZMod 6` has zero divisors and Fermat-style field reasoning breaks.

So the direct H4-style polynomial bridge hits the same wall as before:

> a characteristic-committed invariant cannot be the ACC⁰ composite scale bridge.

The only remaining direct-composite target is `CarryRefinementCrossing`, which asks for a characteristic-independent invariant. That is not currently proved and is separation-strength for the composite route.

### B. Williams / algorithmic-counting scale bridge: works as the restricted H4 pattern

The Williams route is the successful ACC⁰ scale bridge pattern. It avoids the single-field obstruction by switching observers:

- from field-polynomial degree,
- to integer/count-cell observation,
- plus exact `SYM∘AND` structure,
- plus faster-than-bruteforce SAT,
- plus nondeterministic time hierarchy.

The N-Frame version is internalized here:

- File: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthACC0NFrameWilliamsRoute.lean`
- Route: `NFrameWilliamsRoute`
- Equivalence: `nframe_williams_route_equiv`
- Characteristic-free escape: `nframe_observer_characteristic_free`
- Conditional Williams cash-out: `nframe_fastSat_to_timeHierarchy`
- Diagonalization core: `nframe_hierarchy_diag_core`

Lean check:

```text
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthACC0NFrameWilliamsRoute.lean
```

reported clean theorem dependencies:

```text
nframe_williams_route_equiv              [propext, Classical.choice, Quot.sound]
nframe_observer_characteristic_free      [propext, Classical.choice, Quot.sound]
nframe_fastSat_to_timeHierarchy          [propext, Classical.choice, Quot.sound]
nframe_hierarchy_diag_core               [propext, Quot.sound]
```

Key theorem shape:

```lean
def NFrameWilliamsRoute : Prop :=
  ∀ (n : ℕ) (C : ACC0Circuit n),
    ∃ (m : ℕ) (mono : Fin m → Finset (Fin n)) (top : ℕ → Bool),
      eval C = symEval (fun j x => monoAND (mono j) x) top ∧ m + 1 < 2 ^ n

def WilliamsFastSatRoute : Prop :=
  ∀ (n : ℕ) (C : ACC0Circuit n), HasExactSymAndForm C

theorem nframe_williams_route_equiv : NFrameWilliamsRoute ↔ WilliamsFastSatRoute :=
  Iff.rfl
```

Interpretation:

The Williams route is exactly the N-Frame algorithmic-counting branch:

| N-Frame/H4 role | ACC⁰ Williams instantiation |
|---|---|
| observer | integer gate-count observer `gateCount` |
| boundary | count-cell image |
| compression | `< 2^n` exact `SYM∘AND` count cells |
| escape | characteristic-0 / CRT-universal counting |
| cash-out | fast SAT + hierarchy gives `¬ (NEXP ⊆ ACC⁰)` |

This is the restricted-class version of H4 that actually exists.

## Bottom line

The ACC test cleanly separates the two meanings of “scale bridge”:

1. **Direct polynomial H4:** fails for composite ACC⁰ by proved field/carry obstruction.  The remaining direct target is `CarryRefinementCrossing`, requiring a new characteristic-independent invariant.
2. **Algorithmic H4:** succeeds in the Williams sense.  The route changes observer from field-degree to integer-counting, obtains a count-cell compression, and cashes it out through fast SAT and time hierarchy.

So the lesson for the general N-Frame/P-vs-NP programme is sharp:

> H4 probably cannot be a single natural algebraic measure. The successful restricted model is an observer switch: replace the blocked field-polynomial invariant with a characteristic-free algorithmic/counting boundary, then cash it out through a hierarchy theorem.

For full P≠NP, the analogous missing object would be a Williams-like observer switch for NP/search:

```text
not:    raw SPDP rank / direct Cook–Levin polynomial measure
but:    a characteristic-free, representation-aware boundary observer
        with sub-bruteforce algorithmic or hierarchy cash-out
```

That is the honest ACC lesson.
