# Depth-3 (AC⁰) switching → Tseitin lower bound — status

**Entrypoint:** `ComputationalDepthDepth3FullPipelineManifest.lean` (machine-checked
index of the whole pipeline).

**State:** complete formal pipeline **modulo exactly two explicitly-fenced
switching/BSW research cores**. All files clean `[propext, Classical.choice,
Quot.sound]`, no `sorry`, no `native_decide`.

Three end-to-end theorems (all reduce the AC⁰ lower bound to the cores below):
- `depth3_explicit_circuit_no_shallow_refutation` (explicit circuit, size route)
- `depth3_size_route_modulo_collapse` (size route over `TseitinCNF`; BSW-internal)
- `depth3_lower_bound_modulo_collapse` (width route)

Discharged: circuit construction, literal+assignment bijections, Tseitin
instantiation (`hAxiom`+unsat), BSW size LB, tree→`ResolutionDerivation`,
falsify-deepest extraction (count + residual + star-bound).

**The two fenced cores (genuine research walls, not faked):**
1. **Obligation 1** — satisfy-step switching depth bound (good restriction ⇒ shallow
   tree), via `ReconstructionCorrect`. Now discharged in **five regimes** (pure-satisfy,
   pure-falsify, no-skip, `align`, clean-skip — see `ComputationalDepthDepth3DepthGapManifest`),
   isolating the residual to the **confound**: a clause falsified at the leaf that *also*
   received satisfy steps. The confound is machine-checked real and uncovered
   (`confound_uncovered` on `[{x₀},{x₁,x₂}]`), fenced by `encLits_length_lt_depth`
   (pointwise no-go) + `tight_pack_skip_invariant` (empty-skip wall). Closing it =
   Razborov's forward-replay `ρ`-reconstruction = Håstad's switching lemma.
2. **∅-lift** (falsify-deepest) — restricted-Tseitin-is-expander + specific-ρ union
   bound (BSW probabilistic combinatorics). Untouched.

Ceiling: AC⁰/depth-3. `Depth3CollapseModel.collapse` (general circuit ↔ collapse)
and P vs NP are untouched.
