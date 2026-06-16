# Route B — a machine-checked conditional anatomy of `NEXP ⊄ ACC⁰`

**Status.** This is **not** a proof of `NEXP ⊄ ACC⁰`, and nothing in it is `P ≠ NP`.  It is a complete,
machine-checked **conditional anatomy** of the Williams / Razborov–Smolensky / Beigel–Tarui route: every *gluing*,
*architecture*, and *accounting* step is proved (clean axioms, no `sorry`), and the separation is faithfully
**reduced** to a small set of named classical theorems that remain as sockets.

All theorems live under `PallLean.Paper93.DeepMath.PathB`; the master re-export is
`ComputationalDepthACC0FrontierSummary.lean`.

---

## 0. How we got here — N-Frame / tri-aspect did its job

The N-Frame programme was used as a **selector**, not the engine:

- The *incidence / rank* observer was honestly **refuted**: `NFrameRankShrink` is false for the membership-rank
  observer — adversarial singleton supports have injective patterns, so `RankCellCollapse` never fires
  (`…ACC0RankShrinkWall`).
- Tri-aspect monism was turned into a theorem map (`…ACC0TriAspectBoundary`): one boundary object, three projections
  (incidence / algebraic / cost).  The **incidence projection is refuted**; the **algebraic (effective-dimension)
  projection is viable** for `AC⁰[p]` (parity escapes the low-degree span — RS core).
- Conclusion: the working route is **Route B** (the polynomial method), not the observer route.

---

## 1. The composite-`MOD` object and the product-residue observer

- `MOD₆ = MOD₂ ∧ MOD₃` (`…ACC0CompositeBTTarget.mod6_iff_mod2_and_mod3`).
- **Single-field RS provably fails for composite modulus**: no injective ring hom `ZMod 6 → ZMod p` (the zero-divisor
  `2·3 = 0` cannot survive in a field) — `field_polynomial_projection_fails_for_MOD6`.
- The replacement is the **integer / product observer** `ZMod 6 ≃+* ZMod 2 × ZMod 3` (`compositeResidueObserver`),
  faithful where no single field is.
- Depth-2 `MOD₆∘AND` has an exact `SYM∘AND` representation read by the residue pair (`…ACC0Mod6SymAndDepth2`).

## 2. Composition: what composes, and the wall that is not a wall

- `…ACC0SymAndComposition`: `NOT`, shared-layer `AND`/`OR`, and cross-modulus CRT all compose; cross-layer `AND`/`OR`
  lands in a **joint two-count** representation.
- `…ACC0MiniBTTwoCount`: the two-count collapse is **provable exactly** by a mixed-radix encoding
  (`miniBTCollapse_holds`).  Correcting an earlier guess: the wall is **not** impossibility but the **multiplicative
  size blow-up** (`…ACC0BTSizeRecurrence.iterSize_ge`: `b·(b+1)^k`, exponential in fan-in).

## 3. The probabilistic-polynomial layer (the RS analytic core, PROVED)

- **`MOD` gates are exactly low-degree** — `mod2_indicator` (`1+a`, deg 1), `mod3_indicator` (`1−a²`, deg 2).  No
  probabilism needed for `MOD`.
- The genuine probabilistic ingredient is the **`OR` polynomial**:
  - `linear_form_balance` — a random `F_p`-linear form vanishes on a fixed nonzero vector with probability **exactly
    `1/p`** (additive equidistribution).
  - `orPoly_error` — the `OR` polynomial `(∑ rᵢvᵢ)^{p-1}` has degree `p-1` and error exactly `1/p`.
- **Amplification** (`…ACC0ProbabilisticAmplification`): `t` independent forms ⇒ error `(1/p)^t`
  (`amplified_form_balance`), degree `t(p-1)`.

## 4. Substitution: degree and error both bounded (PROVED interfaces)

- **Circuit substitution error** (`…ACC0CircuitSubstitution.circuit_error_bound`): total error `≤ size·ε` (the hybrid
  union bound over gates).
- **Multilinearisation** (`…ACC0Multilinearisation`): a bounded-degree polynomial on the Boolean cube is a sparse
  `AND`-feature sum; **`…ACC0SubstitutionPoly.circuit_cube_count`**: the circuit *is* an `MvPolynomial` whose accept
  count is the sparse cube sum.
- **Degree composition** (`…ACC0AevalDegree.aeval_totalDegree_le` + `…ACC0LowDegreeSubstitution.psubst_degree`): low
  degree survives constant-depth composition (`δ^{depth}`); the per-gate degree factor is **discharged** from local
  gate degrees.
- **Error averaging** (`…ACC0ErrorAveraging.exists_good_seed`): per-input seed error ⇒ a fixed seed with bounded
  input error.
- **Calibration** (`…ACC0ErrorCalibration`): `p^t > 10·size` ⇒ circuit error `< 2^n/10`.

## 5. Read-off and the Route-B capstone (PROVED conditional)

- **Sparse read-off** (`…ACC0SparsePolyReadoff.sparse_readoff`): the cube sum is a sub-`2^n` count over `≤ (n+1)^D`
  features — the Williams `ACC⁰`-SAT speedup input.
- **`…ACC0RouteBComplete.routeB_to_NEXP_not_ACC0`** (axiom-free conditional): the proved approximation side backs the
  RS representation; with the abstract counting / Williams / hierarchy sockets, `¬ NEXPHasACC0Circuits`.

## 6. The Williams side — architecture proved, deep theorems socketed

- **Williams meta-theorem** (`…ACC0WilliamsMetaTheorem.williams_meta_theorem`, axiom-free): the easy-witness collapse
  + nondeterministic time hierarchy ⇒ `¬ (NEXP ⊆ ACC⁰)` (modus tollens).
- **Easy-witness collapse** (`…ACC0EasyWitness`): decomposed into the **IKW easy-witness lemma** and **guess-and-verify**;
  composition glue proved (`easyWitnessCollapse_from_parts`, axiom-free).
- **Concrete NTM hierarchy infrastructure**:
  - `…ACC0NTM` — abstract nondeterministic model, `NTIME`/`NEXP`, `acceptsWithin_mono`, `reachIn_add`.
  - `…ACC0ConcreteNTM` — concrete **encodable** machine model; `machineEquiv : TMachine ≃ ℕ` (machines enumerable).
  - `…ACC0TimeHierarchyDiagonal` — the **Cantor diagonal core proved** (`diag_not_mem_range`); hierarchy from
    enumerability + diagonal-simulatability.
  - `…ACC0UniversalNTM` — interpreter-level universal simulation; **`enum_covers` discharged** (a hierarchy socket is
    now a theorem); hierarchy down to one socket.
  - `…ACC0SimulationStep` — single-step ⇒ linear overhead `t·B` (`sim_acceptsWithin`).
  - Physical-`U` sub-machine **contracts proved**: tape encoding faithful (`…ACC0TapeEncoding`), rule-lookup correct
    (`…ACC0RuleLookup`), head-movement local (`…ACC0HeadLocation`), tape-rewrite contract (`…ACC0TapeRewrite`), atomic
    step (`…ACC0PhysicalStep`), decode round-trip (`…ACC0UniversalDecode`).

---

## The remaining sockets (the genuine classical mountains)

The separation reduces to these, each a classical theorem and a major formalization project in its own right:

1. **Physical universal Turing machine** (`hstep`) — construct `U` as an actual transition table that decodes `M` from
   its own tape and simulates one `M`-step in `B` of its own steps.  *Status:* model, enumeration, interpreter sim,
   overhead accounting, tape encoding, and all four sub-machine contracts + atomic step + decode round-trip are proved;
   the decode→step→re-encode **loop as `U`-transitions with a `B` bound** remains.
2. **IKW easy-witness lemma** — `NEXP ⊆ ACC⁰` ⇒ accepting `NTIME[2ⁿ]` computations have small `ACC⁰` witness circuits.
3. **Guess-and-verify** — small witness circuits + `ACC⁰`-SAT speedup ⇒ `NTIME[2ⁿ] ⊆ NTIME[2ⁿ/superpoly]`.
4. **Composite Beigel–Tarui degree** — the quasipolynomial composite `SYM∘AND` representation (the only deep open on
   the otherwise-proved approximation side).

**Bottom line.** The ACC⁰ / RS / BT approximation side is essentially worked through and machine-checked.  The route is
no longer vague: it is a precise reduction to named classical complexity-theory theorems.  Proving `NEXP ⊄ ACC⁰`
requires discharging the mountains above — none of which is new, and each of which is its own serious project.
