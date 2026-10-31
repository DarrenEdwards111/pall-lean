# Removing the contradictory PAC / MatrixSPDP gadget axioms

Branch `fix/remove-contradictory-axioms`, based on `main` @ `7f539465`. Prepared 31 Oct 2026 (Europe/London, GMT).

| file | what it is | how to check |
|---|---|---|
| `AxiomRefutations.lean` | **Post-fix regression.** Kernel proofs of `¬ PAC.GadgetSpdpSubspaceFactoring` and `¬ MatrixSPDP.GadgetFactoringLinearMapForm` (the former axiom statements, now plain `Prop`s) | `lake env lean research-audits/remove-contradictory-axioms/AxiomRefutations.lean` → both `[propext, Classical.choice, Quot.sound]` (`AxiomRefutations.out`) |
| `PreFix_AxiomInconsistency_main7f53946.lean.txt` | The same proofs stated against the old axioms, deriving `False`. Only type-checks on `main` @ 7f53946 | `git checkout 7f53946`, copy to `.lean`, `lake env lean …` → `False` with axioms `[…, PAC.gadget_spdp_subspace_factoring, …]` resp. `[…, MatrixSPDP.gadget_factoring_linearmap_form, …]` |
| `DependentCensus.lean` | Meta script. For every constant in the `PallLean` environment it decides, by memoised DFS over `ConstantInfo.getUsedConstantsAsSet` (type + value), pruned to modules that import the axiom's module, whether the constant transitively uses each target | `lake env lean …/DependentCensus.lean` → `dependents_<tree>.tsv` |
| `dependents_main7f53946.tsv` | Census output on main @ 7f53946 (pre-fix) | – |
| `dependents_postfix.tsv`, `DependentCensus_postfix.out` | Census output after this PR (dependents of the new hypothesis `Prop`s) | – |
| `EntryAxioms.lean` / `.out` | `#print axioms` for the entry theorems of the default target after the fix | `lake env lean …/EntryAxioms.lean` |

The derivation of `False` is the same for both statements. The instance is N = 2, singleton blocks, gadget g = X₀
(supportSize 1, degreeBound 1), p = X₁, κ = 1, ℓ = 0.

1. Shifted side, (κ+d, ℓ+d) = (2, 1): X₁ has degree 1, so every length-2 iterated derivative vanishes, and
   `mlBlockedSpdpSubspace B 2 1 X₁ = ⊥` (rank 0).
   * Finset form: `G.card ≤ 2^(1+1) · 0 = 0`, so G = ∅ and span G = ⊥.
   * Linear-map form: `Submodule.map L ⊥ = ⊥`.
2. Unshifted side: the admissible row S = [0], u = 1 of g·p = X₀X₁ contributes mlProj(∂₀(X₀X₁)) = X₁ to
   `mlBlockedSpdpSubspace B 1 0 (X₀X₁)`.
3. The axiom's containment then forces X₁ ∈ ⊥, i.e. X₁ = 0. Taking the coefficient at x₁ gives 1 = 0.

The repository already documented the numeric counterexample in `PallLean/Archive/GadgetSubspaceFactoringCounterexample.lean`,
but never derived `False`. The axioms stayed in the default build closure, which made that environment
inconsistent.
