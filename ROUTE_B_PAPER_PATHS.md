# Route B paper-faithful paths from `p vs np1.pdf`

Source checked: `/mnt/c/Users/darre/Desktop/p vs np1.pdf` via `/home/darre/pall-lean/.pvsnp1_full.txt`.

## Paper anchors

- Route B primary: lines ~660-682. Theorem 207 is the main theorem: universal P-side collapse + same-object extraction/rank monotonicity.
- P-side collapse driver: lines ~700-714. Theorem 170 gives the uniform `Γ_{κ,ℓ}(P_{M,n}) ≤ n^{O(1)}` bound for all compiled P computations.
- Width⇒Rank/profile compression: §9, especially lines ~1750-1995 and ~2148-2265.
- Instance-uniform extraction: lines ~10247-10435. Lemmas 205/206 extract coupled sheets by syntactic rank-monotone maps.
- Load-bearing restatement: line ~13859, Lemma 264 = compiled Width⇒Rank via profile compression.

## Correct Route B dependency spine

1. Assume `P = NP`, get a polytime 3SAT decider `M`.
2. Compile/instrument `M` into the same SPDP object/model, producing `P_{M',n}`.
3. Apply Width⇒Rank/profile compression to get the P-side upper bound:
   `Γ^B_{κ,ℓ}(P_{M',n}) ≤ n^{O(1)}` for `κ,ℓ = Θ(log n)`.
4. Use instance-uniform extraction `T_Φ`, made only of rank-monotone syntactic maps, to get coupled sheet `Q^×_Φ`/activated `Q^×_{Φ,S}` with
   `Γ(Q^×_Φ) ≤ Γ(P_{M',n})`.
5. Apply NP-side identity-minor lower bound:
   `Γ(Q^×_Φ) ≥ n^{Θ(log n)}`.
6. Contradiction.

## The key paper-faithful P-side subpath

The load-bearing part is not a raw window/support enumeration. It is:

```text
canonical windows
→ finite local monoid normal forms (Lemma 25)
→ interface-anonymous profiles (Definition 21)
→ profile count independent of κ (Lemma 29)
→ per-type constant-dimensional W_σ
→ profile subspace V_h = ⊗_σ Sym^{h(σ)}(W_σ)
→ rows of profile h land in V_h (Lemma 31)
→ sum over profiles (Width⇒Rank, Lemma 32 / Lemma 264)
```

## What Lemma 31 actually requires

For each interface-anonymous profile `h`, rows with local type statistics matching `h` land in

```text
V_h ⊆ ⊗_{σ∈Σ≤q} Sym^{h(σ)}(W_σ)
```

where each `W_σ` is a constant-dimensional space defined relative to the compiled coefficient basis. This is a profile-subspace/tensor-symmetric-power statement.

It is **not**:

- membership of the whole row/product in one single `W_σ`,
- a single-bucket `ConstraintType.booleanity` claim,
- ordered κ-step sequence counting,
- shifted-support enumeration,
- global/common span across unrelated profiles,
- semantic/witness-dependent extraction.

## Lean surfaces matching the paper path

Preferred final payload:

```lean
Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData
```

This is the closest match to paper Lemma 31: term-dependent local types assemble into selected profile-template bases bounded by `profileTemplateBound ρ.val`.

Checked adapter chain:

```lean
Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData
→ Step247UniformRouteBPaperFaithfulTPhiSourceSelectedProfileTemplateSpanData
→ Step247UniformRouteBPaperFaithfulTPhiSourceLeibnizLocalTypeCompressionData
→ Step247UniformRouteBPaperFaithfulTPhiStrictConstraintTypeProfileSubspaceData / P-side bound
→ NoBoundedSATDeciderAtPaperScale
→ PeqNP_Paper → False
```

Existing closeout:

```lean
P_ne_NP_canonical_routeB_profileTemplateTermFamily_conditional
```

## Also valid but slightly higher-level paper-faithful surfaces

1. Selected profile-template span:

```lean
Step247UniformRouteBPaperFaithfulTPhiSourceSelectedProfileTemplateSpanData
P_ne_NP_canonical_routeB_profileTemplateSpan_conditional
P_ne_NP_canonical_routeB_lemma31_profileSubspace_conditional
```

This is already at the profile-subspace frontier. It asks for selected row/profile membership directly.

2. Exact-profile/template-collapse:

```lean
Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizExactProfileTemplateCollapseData
P_ne_NP_canonical_routeB_lemma31_profileSubspace_from_exactProfileTemplateCollapse_conditional
```

This is paper-faithful if it proves actual selected profile post-span/template collapse, but may be stronger than needed.

3. Local monoid normal forms:

```lean
Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizLocalMonoidNormalForms
Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizProfileTemplateLocalMonoidNormalForms
```

This corresponds directly to Lemmas 25/29/31: finite local monoid normal forms, then profile-template budget.

## Lower seams that are useful but risky/overstrong

The fixed-q event-atom route:

```lean
Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimBudgetData
Step247UniformRouteBPaperFaithfulTPhiSourceWitnessedLeibnizNFOfWordEventAtomQDimRowWitness
```

is over-refined. The current diagnostic theorem shows the row witness forces unshifted product membership in the folded singleton atom span. That is stronger than Lemma 31 and should be treated as diagnostic unless the atom-span membership is genuinely proved.

The exact slot/fiber/local-algebra route can still be useful if it constructs the same profile-subspace data:

```lean
Step247UniformRouteBPaperFaithfulTPhiExactInterfaceSlotFactorizationWithSelectedShiftClosureData
Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductInterfaceSlotFactorizationData
Step247UniformRouteBPaperFaithfulTPhiShiftedLeibnizProductCompiledBasisLocalAlgebraData
```

but the final claim must pass through selected profile/local-type/profile-template assembly, not single-bucket membership.

## Recommendation

Attack in this order:

1. Prove/construct `Step247UniformRouteBPaperFaithfulTPhiSourceProfileTemplateTermFamilyData`.
2. If too hard, construct `Step247UniformRouteBPaperFaithfulTPhiSourceSelectedProfileTemplateSpanData` directly.
3. If using local algebra/exact slots, only accept it once it feeds `SourceLeibnizLocalTypeCompressionData` through the profile-template adapters.
4. Avoid claiming final closure from `EventAtomQDimRowWitness` unless the atom-span proof is real; it is stronger than the paper’s Lemma 31.

## Property 1 Row-Containment Guardrail (2026-05-15)

For the Lemma 31 / Property 1 row-containment proof, always state which `W` is being targeted.

- Correct target: `profileSubspace h (fun σ => interfaceSpace_compiledBasis B κ ℓ σ)` or the local `D.interfaceSpace` adapter that instantiates to that family. This is coordinate/profile-local and connects to the Half-A dimension bound.
- Dead-chain target: `cookLevinProfileSubspace bp (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)`. This reintroduces the fixed canonical coordinate obstruction for variable-dependent booleanity/adjacency rows and should only be used for diagnostics/negative pressure tests, not final closure.

If a proof attempt drifts into `concreteW`, pivot back to `interfaceSpace_compiledBasis` and land the row embeddings there.

### Archived concreteW dead-chain modules

The unused fixed-canonical concreteW closeout/diagnostic modules were moved to:

```text
archive/routeb-concretew-dead-chain/
```

These are retained for historical diagnostics only. Do not use them as the final Lemma 31 / Property 1 row-containment path.
