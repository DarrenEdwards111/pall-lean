# Archived old approach (2026-03-18)

This note archives the previous proof-shape attempts that were replaced.

## What was archived

1. **Universal extraction over arbitrary CNFs**
   - Old shape: extraction axiom quantified over any `cnf : CookLevinCNF ...`.
   - Problem: unsound for adversarial/trivial CNFs (e.g. zero-polynomial/degenerate encodings).

2. **Combined contradictory formulation without correctness gate**
   - Old shape mixed low-rank and permanent-domination claims without explicitly tying CNF to a correct Cook-Levin encoding.
   - Problem: allowed inconsistency from CNFs unrelated to machine semantics.

## Current replacement (active)

- CNF assembly now being built with reusable scaffolding in `PallLean/CookLevin.lean`.
- Proof path requires correctness-gated Cook-Levin structure before applying NP-side extraction.
- We keep only the paper-faithful hard step as the remaining technical target.

## Why archive this

To preserve reasoning history while preventing accidental reintroduction of unsound quantification patterns.
