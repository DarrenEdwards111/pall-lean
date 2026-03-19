# Old Scaffold Correctness Assumption (Archived)

Date: 2026-03-19
Branch: `compiled-route`

## What was archived

Previous top-level assumption in `PallLean/CompiledSeparation.lean`:

```lean
axiom scaffold_correctness_exists :
  ∀ (M : DTM),
    ∃ nC : ℕ, ScaffoldCorrectAfter M nC
```

This has been replaced by a more semantic and paper-faithful assumption:

```lean
def InitialSemanticCorrectAt (M : DTM) (n : ℕ) : Prop :=
  ∀ (hn2 : n ≥ 2),
    IsCorrectEncoding M n (CookLevin.defaultK M)
      (CookLevin.initialSemanticCNF M n hn2)
      (CookLevin.initialSemantic_local M n hn2)

axiom initialSemantic_correctness_after_threshold :
  ∀ (M : DTM), ∃ nC : ℕ,
    ∀ n : ℕ, n ≥ nC → InitialSemanticCorrectAt M n
```

## Why this migration

- Old form packaged eventual correctness directly at the scaffold-bridge layer.
- New form states the semantic target explicitly (correctness of the `initialSemantic` Cook-Levin encoding at each size past threshold).
- This makes the remaining proof obligation clearer and closer to paper semantics.

## Compatibility

`CompiledSeparation.lean` now includes bridging theorems showing equivalence of packaging styles:

- `initialSemantic_correctness_after_threshold_of_scaffold_correctness`
- `scaffold_correctness_packaging_iff`

So legacy and new packaging are definitionally aligned; only the assumption boundary changed.
