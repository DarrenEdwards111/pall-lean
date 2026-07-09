# Applying the ACC Scale-Bridge Lesson to P vs NP

**Status:** strategic H4 target extraction, not a proof of `P ≠ NP`.

## ACC lesson

The ACC⁰ audit separated two kinds of scale bridge:

1. **Direct algebraic bridge** — try to push a field/polynomial lower-bound measure through the hard class.
   - For ACC⁰ this fails at composite modulus: `CarryRefinementCrossing`.
   - Proved anatomy: `field_based_modes_all_fail`.

2. **Observer-switch / algorithmic bridge** — change the observer from the blocked algebraic measure to a characteristic-free counting boundary, then cash it out by fast SAT + hierarchy.
   - For ACC⁰ this is Williams.
   - Formal N-Frame version: `NFrameWilliamsRoute ↔ WilliamsFastSatRoute`.

The successful bridge is not “make the old measure stronger.” It is:

```text
blocked invariant
  → observer switch
  → compressed boundary representation
  → algorithmic speedup / hierarchy contradiction
```

## P-vs-NP translation

The failed direct P-vs-NP route was:

```text
raw Cook-Levin / SPDP rank high on SAT-search
raw Cook-Levin / SPDP rank low on P-time computation
therefore P ≠ NP
```

This is false as stated. The repo already found the obstruction:

- raw SPDP rank sees **compilation junk**;
- the trivial/P-side Cook-Levin object can have the same identity-minor-style rank floor;
- `piPhi` / flat projection is effectively identity on the important objects;
- the useful non-flat projection is unbuilt and is exactly the far shore.

So the ACC lesson says: do **not** keep strengthening raw SPDP rank. Search for the P-vs-NP analogue of Williams' observer switch.

## New H4 target

Old H4:

```text
Find a super-polynomial separating measure.
```

New H4:

```text
Find an observer/boundary transform Π★ and a cash-out theorem such that:

1. Π★ kills representation/compilation junk on every P-time computation;
2. Π★ preserves genuine SAT/search obstruction;
3. Π★ is not an efficiently checkable large truth-table property;
4. Π★ yields an algorithmic or hierarchy contradiction if SAT has polynomial-time algorithms.
```

In symbols, the target is not merely:

```text
μ(SAT) ≥ superpoly  and  μ(P) ≤ poly
```

but rather:

```text
P-machine M deciding SAT
   ↓ Cook-Levin / search trace object T_M
Π★(T_M) has compressed boundary form
   ↓ cash-out
subcritical search / diagonalization / hierarchy contradiction
```

## Required tests for any candidate Π★

A candidate observer switch must pass four filters.

### Test 1 — trivial-machine / compilation-junk test

For the trivial or bounded DTM compiled object:

```text
rank_or_complexity(Π★(compiled trivial/P object)) ≤ poly(n)
```

If it remains high, the candidate is only measuring Cook-Levin grid junk and dies.

### Test 2 — parity/Tseitin easy-object test

Π★ must not be high merely because an object has high spectral/proof-algebraic structure.

It must not be fooled by:

- parity, which is in `P` but maxes spectral/high-degree measures;
- Tseitin linear systems, which can be hard for some proof systems but are in `P` by Gaussian elimination;
- trivial Cook-Levin compilation, which is syntactically huge but semantically easy.

### Test 3 — SAT/search preservation test

Π★ must preserve the actual NP/search obstruction:

```text
rank_or_boundary_complexity(Π★(SAT/search identity-minor object)) ≥ superpoly(n)
```

Not vacuously. If Π★ is identity on the SAT object, that proves nothing unless it also compresses the P-side.

### Test 4 — non-naturalness / non-largeness test

Π★ cannot be a computable large truth-table property. Otherwise the Razborov–Rudich filter kills it.

So the live designs must be one of:

- **algorithmic/diagonalizing**: Williams-style, not a truth-table property;
- **non-large/geometric**: GCT/multiplicity-style, keyed to exceptional SAT/permanent structure;
- **proof-theoretic/non-computable**: bounded-arithmetic/proof-complexity obstruction.

## Candidate P-vs-NP observer switches

### A. Williams-style search observer

Try to replace raw SPDP rank with a search-process observer:

```text
observer = count/structure of partial witnesses explored by a supposed P-time SAT solver
boundary = compressed family of reachable residual search states
compression = polynomial-time solver implies small boundary
escape = SAT self-reduction / diagonalization forces too many distinguishable residuals
```

This is the closest analogue of Williams.

Honest risk: known barriers say general P-time algorithms may exploit arbitrary adaptive structure; proving too many residuals is essentially lower-bound strength.

### B. Proof-complexity observer

Translate `P = NP` into short certificates/proofs for all unsat formulas, then seek a boundary invariant that is low for P-search but high for explicit formulas.

Candidate cash-out:

```text
P = NP → short/producible proofs/search traces
explicit proof-complexity lower bound → contradiction
```

This dodges natural proofs only if the invariant is proof-system-specific/non-natural, not a large truth-table property.

Honest risk: strong lower bounds for general proof systems are themselves major open problems.

### C. GCT / non-large geometric observer

Use a highly non-large geometric obstruction keyed to SAT/permanent-like structure rather than all hard truth tables.

Candidate cash-out:

```text
small circuits/algorithms imply orbit-closure containment
multiplicity/representation obstruction forbids containment
```

Honest risk: occurrence obstructions are known insufficient; multiplicity-style obstructions remain hard and must avoid known GCT no-go results.

### D. PAC/amplituhedron flexible boundary

The Book 1 route:

```text
Π★ = positivity-preserving flexible boundary projection
```

Desired behavior:

```text
Π★(P/Cook-Levin junk) compresses
Π★(SAT/search obstruction) survives
```

This is philosophically aligned with N-Frame, but currently formal status is:

- flat `piPhi` is too weak / identity-like;
- useful non-flat projection is unbuilt;
- proving it is exactly H4.

## Immediate conclusion

The ACC test does help P-vs-NP by changing the target.

Do not search for a better raw SPDP measure.

Search for:

```text
a Williams-style observer switch for NP search
```

with:

```text
boundary compression + non-natural/non-large design + hierarchy/proof/search cash-out.
```

## First formal core proved

The minimal finite H4 core has now been formalized in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPObserverSwitchToy.lean
```

Clean theorem dependencies were checked with:

```text
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPObserverSwitchToy.lean
```

The proved theorems are:

```lean
card_assignment
boundary_card_ge_exp
small_boundary_not_residual_distinguishing
poly_boundary_not_residual_distinguishing
residual_distinguishing_contradicts_poly_boundary
```

They establish the finite pigeonhole core:

```text
P-side compression:        |boundary| ≤ n^k
NP-side preservation:      observer injective on 2^n residual branches
scale gap:                 n^k < 2^n
--------------------------------------------------
contradiction
```

This is not `P ≠ NP`; it is the first theorem-shaped obligation any Williams-style NP-search observer switch must satisfy.

## Concrete residual-observer interface added

The next SAT-side instantiation has now been added in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPResidualObserver.lean
```

Lean check:

```text
~/.elan/bin/lake build PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPObserverSwitchToy
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPResidualObserver.lean
```

The file defines:

```lean
assignmentPrefix
ResidualObserver
fullBranchObserver
FullResidualDistinguishing
PolyBoundaryAt
residualSATTruth
ResidualTruthSound
```

and proves:

```lean
full_residual_boundary_card_ge_exp
small_boundary_not_full_residual_distinguishing
poly_boundary_not_full_residual_distinguishing
full_residual_distinguishing_contradicts_poly_boundary
full_distinguishing_truth_sound_on_full_branches
```

So the pipeline is now two Lean modules:

```text
Toy finite core:
  polynomial boundary + injective 2^n branches + n^k < 2^n ⇒ contradiction

Residual SAT interface:
  residual observer (φ,prefix) ↦ boundary state
  full residual distinction plugs into the toy core
```

## Naive missing lemma refuted, dynamic SPDP formalized

The first attempted missing lemma would be:

```text
SAT self-reduction / residual SAT truth forces full residual distinction.
```

That is false.  It has now been formalized as a no-go in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPResidualObserverNoGo.lean
```

Lean check:

```text
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPResidualObserverNoGo.lean
```

The file proves:

```lean
prefix_oracle_truth_sound
bool_prefix_observer_poly_but_not_full_distinguishing
```

Meaning:

```text
a correct SAT prefix oracle is residual-truth-sound with only Bool = 2 boundary states,
and therefore cannot distinguish all 2^n full branches when 2^n is larger than the chosen polynomial bound.
```

So SAT self-reduction alone does not force exponential boundary.  The observer cannot be mere residual SAT truth.

The corrected statement — **SPDP must be dynamic** — is now formalized in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthDynamicSPDP.lean
```

Lean check:

```text
~/.elan/bin/lake build PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPResidualObserverNoGo
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthDynamicSPDP.lean
```

The file proves:

```lean
dynamicTranscriptObserver_injective
dynamicTranscript_card
dynamic_full_distinction_contradicts_poly_boundary
bool_static_cannot_be_dynamic_full_distinguishing
dynamicTranscript_not_poly_below_exp
truth_sound_does_not_supply_dynamic_distinction
```

Formal content:

```text
static residual truth:
  Bool boundary, truth-sound, not full-distinguishing

dynamic transcript/state:
  records branch/search path, can distinguish all 2^n branches,
  and therefore cannot be polynomial-bounded below the exponential gap
```

This proves the design correction:

```text
H4 cannot be static residual truth.
H4 must be dynamic transcript/state/fooling-set structure.
```

## Dynamic transcript/fooling-set schema proved

The next H4 layer has now been formalized in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPTranscriptObserver.lean
```

Lean check:

```text
~/.elan/bin/lake build PallLean.Paper93.DeepMath.PathB.ComputationalDepthDynamicSPDP
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPTranscriptObserver.lean
```

The file defines:

```lean
ResidualInstance
TranscriptObserver
FoolingResidualFamily
identityFoolingFamily
SoundOnFoolingFamily
branchTranscriptObserver
```

and proves:

```lean
branchTranscript_injective_of_sound
transcript_boundary_card_ge_exp_of_fooling
transcript_fooling_contradicts_poly_boundary
poly_transcript_boundary_fails_fooling_soundness
identity_fooling_sound_iff_branch_injective
```

Formal content:

```text
fooling residual family indexed by 2^m branches
+ transcript observer soundness on semantic/search labels
+ injective labels
--------------------------------------------------------
observer boundary has ≥ 2^m states
```

and therefore:

```text
polynomial transcript boundary + exponential gap
⇒ observer cannot be sound on the fooling family.
```

## Concrete forced-assignment CNF family instantiated

A first concrete SAT-shaped family has now been added in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPForcedAssignmentFamily.lean
```

Lean check:

```text
~/.elan/bin/lake build PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPTranscriptObserver
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPForcedAssignmentFamily.lean
```

The file defines:

```lean
forcedLit
forcedClause
forcedAssignmentCNF
forcedResidualInstance
forcedAssignmentFamily
AssignmentDecoder
DecodesForcedLabels
```

and proves:

```lean
soundOnForcedFamily_of_decodes
forced_family_boundary_card_ge_exp
forced_family_contradicts_poly_boundary
poly_boundary_fails_forced_label_decoding
forcedIndexObserver_injective
```

Formal content:

```text
for every m-bit assignment a,
  forcedAssignmentCNF a = unit clauses pinning every bit of a

any finite transcript boundary that decodes every forced label correctly
  has ≥ 2^m states
```

This is intentionally an easy SAT family, so it does not prove `P ≠ NP`.  Its role is to show the dynamic H4/fooling
machinery now fires on a real CNF residual family.  The live bridge is to replace the forced-assignment family by a hard
SAT/search family where correctness of a P-time solver forces analogous decoded transcript labels.

## Conditional dynamic-H4 theorem shape closed

The current route has now been closed into one exact conditional theorem in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPDynamicH4Theorem.lean
```

Lean check:

```text
~/.elan/bin/lake build PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPTranscriptObserver
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPDynamicH4Theorem.lean
```

The file defines:

```lean
DynamicH4Witness
DynamicH4ForPTimeSAT
```

and proves:

```lean
dynamicH4Witness_impossible
no_SATDecisionInP_of_DynamicH4
deepSATSearch_of_DynamicH4_with_selfReduction
```

Formal content:

```text
DynamicH4ForPTimeSAT U
⇒ ¬ SATDecisionInP U
```

where `DynamicH4ForPTimeSAT U` means:

```text
every correct polynomial-time SAT decider yields
  a finite transcript observer,
  a hard 2^m fooling residual family,
  soundness on that family,
  polynomial boundary size,
  and an exponential gap.
```

Those fields are jointly inconsistent by the already-proved transcript/fooling lower bound.

So the dynamic H4 bridge is now exactly one theorem-shaped instantiation obligation:

```lean
DynamicH4ForPTimeSAT U
```

To prove unconditional P≠NP in this machine model, prove `DynamicH4ForPTimeSAT U` for a genuine hard SAT/search residual family.

The Bool-prefix no-go proves why the observer must include more than truth values; `ComputationalDepthDynamicSPDP.lean` proves the corrected dynamic shape; `ComputationalDepthPvsNPTranscriptObserver.lean` proves the fooling-set lower-bound schema; `ComputationalDepthPvsNPForcedAssignmentFamily.lean` proves the schema on concrete CNF residuals; `ComputationalDepthPvsNPDynamicH4Theorem.lean` proves dynamic H4 would rule out polynomial-time SAT.
