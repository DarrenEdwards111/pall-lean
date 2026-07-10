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

## PAC / amplituhedron projection socket formalized

The PAC/amplituhedron layer has now been formalized as an explicit dynamic boundary projection in:

```text
PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPPACAmplituhedronProjection.lean
```

Lean check:

```text
~/.elan/bin/lake build PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicH4Theorem
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPPACAmplituhedronProjection.lean
```

The file defines:

```lean
PACAmplituhedronProjection
projectedTranscriptObserver
PACPreservesFoolingLabels
PACCompressedAt
identityPACProjection
```

and proves:

```lean
projected_sound_of_PACPreserves
PAC_projection_contradicts_poly_boundary
PAC_projection_must_lose_labels
dynamicH4Witness_of_PAC_projection
dynamicH4Witness_of_PAC_projection_impossible
identityPAC_preserves_iff
```

Formal content:

```text
raw dynamic transcript states α
  -- PAC/amplituhedron projection --> positive boundary cells β

if β is polynomial-sized
and the projection preserves fooling labels
and m^k < 2^m
then contradiction.
```

So the geometric PAC/amplituhedron idea is now a precise Lean projection socket.  What remains is not the abstract projection theorem; it is instantiating a nontrivial projection that both:

```text
compresses P-time solver transcript/state boundaries
preserves hard SAT/search fooling labels
```

The identity projection is included as a sanity check: it preserves labels but does not compress.

## 2026-07-09 — Dynamic H4 equivalence audit

Lean file: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPDynamicH4Equivalence.lean`.

Result: the named bridge `DynamicH4ForPTimeSAT U` is data-producing (`Type 1`), so the exact audit is by inhabitation:

```lean
Nonempty (DynamicH4ForPTimeSAT U) ↔ ¬ SATDecisionInP U
```

The forward direction is the existing H4 theorem. The reverse direction is vacuity: if no SAT decider exists, then any alleged decider gives contradiction, from which the requested `DynamicH4Witness` can be produced.

Interpretation: the dynamic transcript/fooling-set machinery is sound, but the current bridge statement is theorem-equivalent to the target lower bound. Proving it directly would be proving P≠NP in renamed form. The next non-circular target must be a more structured extraction theorem that explicitly constructs the residual family, transcript observer, decoder/projection, and polynomial boundary from a concrete solver model before contradiction.

## 2026-07-09 — Structured dynamic-H4 extraction interface

Lean file: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPStructuredExtraction.lean`.

After the equivalence audit showed the old bridge is too extensional, this file introduces `StructuredDynamicH4ExtractionFor U D hD`, parameterized by a concrete claimed SAT decider. It separates the fields that a non-circular proof must actually construct:

- raw transcript/state type
- finite projected boundary type
- transcript observer on residual SAT instances
- boundary projection / positive-cell map
- fooling residual family
- preservation of fooling labels after projection
- polynomial boundary bound
- exponential gap

Cash-out theorems proved:

```lean
StructuredDynamicH4ExtractionFor.impossible
StructuredDynamicH4ExtractionFor.impossible_via_PAC
DynamicH4ForPTimeSAT_of_structured
no_SATDecisionInP_of_structuredDynamicH4
no_SATDecisionInP_of_structuredDynamicH4_direct
```

Most important diagnostic theorem:

```lean
StructuredDynamicH4ExtractionFor.preservation_is_the_only_gap
```

This proves that once polynomial compression and the exponential gap are fixed, the preservation field cannot hold on a true `2^m` fooling family. So the live mathematical obstacle is exactly the preservation theorem: equality of projected boundary cells must force equality of hard residual/search labels.

## 2026-07-09 — Ramanujan → holographic projection → amplituhedron extraction socket

Lean file: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPRamanujanHolographicAmplituhedronExtraction.lean`.

Darren suggested the extraction theorem should link Ramanujan expander structure, holographic projection, and amplituhedron/positive-cell compression. This file formalizes that exact pipeline:

```lean
RamanujanBoundaryCertificate
  -> HolographicProjectionStage
  -> AmplituhedronPositiveCellStage
  -> StructuredDynamicH4ExtractionFor
  -> ¬ SATDecisionInP
```

Main theorem object:

```lean
RamanujanHolographicAmplituhedronForPTimeSAT U
```

For each claimed SAT decider it must provide a factored extraction with:

- Ramanujan/expander boundary certificate
- holographic projection from raw transcript states to screen data
- amplituhedron projection from screen data to positive cells
- hard fooling residual family
- label preservation by the composed positive-cell projection
- polynomial positive-cell bound
- exponential gap

Cash-outs proved:

```lean
structuredDynamicH4_of_RamanujanHolographicAmplituhedron
no_SATDecisionInP_of_RamanujanHolographicAmplituhedron
no_SATDecisionInP_of_RamanujanHolographicAmplituhedron_direct
```

Diagnostic theorem:

```lean
RamanujanHolographicAmplituhedronExtractionFor.preservation_is_still_the_gap
```

Even with Ramanujan and holographic payloads realized, polynomially many positive cells below the exponential gap cannot preserve all fooling labels. Thus the actual mathematical frontier is to prove that the Ramanujan/holographic/amplituhedron geometry gives label preservation for a genuine hard SAT residual family, without making the positive cell set exponential.

## 2026-07-09 — Tseitin-expander specialization of RHA extraction

Lean file: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPTseitinExpanderRHAExtraction.lean`.

This specializes the Ramanujan/holographic/amplituhedron extraction route to Tseitin residuals on expander/Ramanujan graphs. It imports the already-proved `ComputationalDepthExpanderTseitinWidthKernel`, so the expander lever is genuine:

```lean
support_combination_eq_boundary
combination_support_card_ge_of_expansion
exists_combination_ne_zero_of_expansion
```

New structures/theorems:

```lean
TseitinExpanderCertificate
TseitinExpanderResidualFamily
TseitinExpanderRHAExtractionFor
TseitinExpanderRHAForPTimeSAT
no_SATDecisionInP_of_TseitinExpanderRHA
```

Concrete non-vacuity sanity check:

```lean
K4_tseitinExpanderCertificate
```

uses the already-proved `K4_hasExpansion` certificate. This is not asymptotic, but it proves the certificate type is inhabited by a real graph.

Exact final frontier now:

```lean
preservesTseitinLabels
```

The composed projection

```text
raw SAT-solver transcript -> holographic screen -> amplituhedron positive cell
```

must not merge distinct labels of the Tseitin-expander residual fooling family while keeping the positive-cell set polynomially bounded.

Diagnostic theorem:

```lean
TseitinExpanderRHAExtractionFor.tseitin_label_preservation_is_the_gap
```

This proves that below the exponential gap, polynomial positive cells cannot preserve all Tseitin labels. Thus the proof must show the geometry/solver interaction forces such preservation from any alleged P-time SAT decider — that is the remaining hard theorem, now in Tseitin-expander form.

## 2026-07-10 — N-Frame trace-channel capacity pressure test

Source inspiration: Darren's `An N64.docx`, whose observer-boundary trace model uses a latent process,
boundary projection/Markov kernel, finite information capacity, hierarchical compression, and variational
stabilization.  Lean extraction:

`PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPNFrameTraceCapacity.lean`.

The discrete channel is:

```text
m-bit latent residual branch -> finite observer boundary -> stabilized semantic label
```

with `capacityBits` defined by `card boundary ≤ 2^capacityBits`.  Proved:

```lean
trace_injective
stateCount_ge_labels
label_bits_le_capacity
sublinear_capacity_impossible
```

Thus correct stabilization of an injective `m`-bit label requires at least `m` boundary bits.  The bound is
tight: `identityTraceChannel` uses exactly `m` bits and has exactly `2^m` states, with theorem
`identityTrace_states_exceed_bit_count` showing the state count is already larger than the bit count.

Decisive pressure-test verdict: a polynomial **bit-capacity** bound does not imply the old H4 polynomial
**state-count** bound.  Polynomial-time/space traces can carry at least linearly many bits and hence exponentially
many states.  N-Frame supplies a useful formal language for projection and stabilization, but a P-vs-NP application
still needs an additional, solver-specific theorem forcing the task-relevant stabilized quotient below `m` bits.
Finiteness, Markovianity, support projection, and MERA-style hierarchical compression alone do not provide that bound.

The follow-up calibration is now also machine-checked.  `exact_capacity_achievable` constructs an
exact-recovery channel at the lower bound, and `capacity_eq_label_bits_of_le` proves that any channel
advertised with at most `m` bits must use exactly `m`.  The proposed solver-specific escape hatch was
packaged as `CapacityDeficitFromCorrectnessFor`: SAT correctness would have to yield both an exact-recovery
channel and a capacity bound strictly below `m`.  Its global form satisfies

```lean
Nonempty (CapacityDeficitFromCorrectnessForAllMachines U) ↔ ¬ SATDecisionInP U
```

by `capacityDeficit_iff_no_SATDecisionInP`.  This closes the logical audit: the sublinear stabilized-quotient
claim is not a weaker trace lemma waiting to be derived from polynomial runtime.  For all machines it is
exactly the desired separation, with the reverse direction inhabited only vacuously once SAT-in-P is denied.

The next operational strengthening was also pressure-tested.  `AccessBoundedTraceChannel` annotates an
N-Frame channel with a step count and per-step task-relevant bandwidth, assuming
`capacityBits ≤ steps * bitsPerStep`.  Exact recovery then proves the genuine access bound

```lean
m ≤ steps * bitsPerStep
```

via `label_bits_le_total_access`.  Two tight countermodels delimit what this buys:
`linearAccessIdentityChannel` uses one bit per step for exactly `m` steps, while
`oneStepIdentityChannel` uses one step of bandwidth `m`.  Thus even after adding sequential access,
the N-Frame information argument yields only a linear total-access requirement, compatible with P.
A super-polynomial SAT lower bound still needs new solver-specific structure that makes the required
task information super-polynomial in the actual encoded input length or prevents polynomial-time
computation of the Boolean decision; neither follows from exact label recovery plus bounded bandwidth.

## 2026-07-10 — Holographic area-law pressure test

Lean file: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPNFrameHolographicAreaLaw.lean`.

The black-hole-inspired refinement is formalized at radius `R` as `R^3` bulk task-label bits and
`R^2` boundary bits per sequential boundary use.  `HolographicAreaLawChannel` packages an exact-recovery
N-Frame channel with the bound

```lean
capacityBits ≤ boundaryUses * R^2.
```

Machine-checked results:

```lean
bulk_bits_le_reused_area
impossible_below_radius_reuse
impossible_one_use
saturatedStreamingChannel
saturated_total_boundary_capacity
saturated_recovers_bulk
```

The static area/volume idea works exactly: one `R^2` boundary cannot recover an injective `R^3`-bit
bulk label for `R ≥ 2`.  More generally, recovery is impossible whenever `boundaryUses < R`.
The tight countermodel reuses the boundary exactly `R` times and reaches total capacity `R * R^2 = R^3`,
with the identity channel recovering the full bulk label.  Since `R` reuse steps are polynomial, the
holographic area law alone does not yield a super-polynomial time lower bound.  The remaining bridge must
prove a sub-`R` reuse restriction for arbitrary SAT solvers or a genuine holographic decoding-complexity
lower bound; neither is supplied by the physical area law itself.

## 2026-07-10 — Holographic decoding-complexity route

Lean file: `PallLean/Paper93/DeepMath/PathB/ComputationalDepthPvsNPNFrameHolographicDecodingComplexity.lean`.

This formalizes the Harlow--Hayden-style alternative: the complete bulk information may fit on the
boundary, while extracting the task-relevant SAT result is computationally hard.  The audit has two sides.

First, `oneStepSaturatedDecoder` proves that area law plus exact recovery alone is compatible with an
abstract decoding-time annotation of one.  Geometry does not automatically supply decoder complexity.

Second, `HolographicSATDecodingLowerBoundFor U D` names the actual solver-specific theorem.  From
`DecidesSAT U D`, the alleged solver gives a polynomial decoding time, while concrete holographic dynamics
would need to force a super-polynomial lower threshold.  Proved:

```lean
explicitSuperPolyThreshold_superPoly
HolographicSATDecodingLowerBoundFor.not_decidesSAT
no_SATDecisionInP_of_holographicDecoding
holographicDecoding_iff_no_SATDecisionInP
```

The last theorem calibrates the global route exactly:

```lean
Nonempty (HolographicSATDecodingLowerBoundForAllMachines U) ↔ ¬ SATDecisionInP U.
```

Thus decoding complexity is the right *kind* of missing invariant, but deriving its super-polynomial
lower bound from a concrete NP-complete residual family and every solver's internal holographic dynamics
is exactly the separation.  The physical area law and N-Frame stabilization do not prove that field.
