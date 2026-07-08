# Audit — `p vs np1.pdf` mapped to Lean status

**Purpose: for each part of the paper's spine, state exactly what is *proved*, *conditional*, *archived
unsafe*, or *axiomatised* in the live (non-archived) Lean repo — so we know whether a salvageable new lemma
hides in the paper, or whether it all reduces to `CookLevinFrontierHyp`.**

Verification key: **[K]** = I checked it with the kernel (`#print axioms`); **[G]** = grep / source
inspection; **[E]** = reported by a thorough Explore read of the files (not personally kernel-rechecked —
deep namespace nesting blocked a few direct prints).

---

## The paper's spine

1. **P-side upper bound** — every P-time / Cook–Levin-compiled computation has *low* SPDP rank.
2. **NP-side lower bound** — an explicit 3SAT/Tseitin/expander family has *high* SPDP rank.
3. **Global God-Move / extraction** — a witness-free rank-monotone map `T_Φ` with `rank(T_Φ p) ≤ rank(p)`
   pulls the NP-hard object out of the P-side solver compilation.
4. **Contradiction** under `P = NP`.

## Status table

| Item | Lean symbol(s) | Status | Axioms |
|---|---|---|---|
| **1. P-side rank ≤ n²⁰⁰** | `p_side_rank_bound_for_cook_levin_of_exactWithinProfileLemma`, `totalProfileBound_le_pow` | **CONDITIONAL** on the socket `CookLevinExactWithinProfileFinrankLemma` | none (the arithmetic part is clean) **[E]** |
| **1. the socket** | `CookLevinExactWithinProfileFinrankLemma`, `CookLevinFrontierHyp` (`def : Prop`) | **SOCKET / named hypothesis** (unproved Prop) | n/a **[G]** |
| **1. old unsafe route** | `spdp_profile_generators` | **ARCHIVED UNSAFE** (`Archive/Paper93Unsafe/`), not in live chain | (false axiom, fenced) **[G]** |
| **2. NP-side `C(n/3, log n)`** | `identity_minor_finrank_bound`, `identity_minor_lower_bound`, `identity_minor_beats_poly`, `tseitin_identity_minor_rank`, `compiled_np_lower_bound_any_dtm` | **PROVED, axiom-free** | clean **[E]** |
| **3. rank-monotone extraction** | `piStar_rank_monotone` (`rank(π* p) ≤ rank p`) | **PROVED *from a custom axiom*** | **`exists_amplituhedron_gauge`** **[G]** |
| **3. Theorem-207 witness** | `exists_theorem207_witness`, `exists_theorem207_semantic_identity_minor_gap_source_transport_data` | **CUSTOM AXIOM** (live) | custom **[G]** |
| **3. SAT-decider variant** | `exists_amplituhedron_gauge_for_sat_decider` | **CUSTOM AXIOM** (live) | custom **[G]** |
| **4. arithmetic sandwich** | `no_rank_sandwich_at_2pow804` | **PROVED** (pure arithmetic) | clean **[E]** |
| **4. clean closeout** | `peqnp_false_of_frontier : CookLevinFrontierHyp → (PeqNP_Paper → False)` | **CONDITIONAL** on `CookLevinFrontierHyp` | **`[propext, Classical.choice, Quot.sound]`** **[K]** |
| **4. final** | `P_ne_NP_finally_closed (hfront : CookLevinFrontierHyp) : P ≠ NP` | **CONDITIONAL** on `CookLevinFrontierHyp` | clean (composes the above) **[E/K]** |
| **4. "unconditional" claims** | `P_ne_NP_fully_unconditional (hF5 hG4)`, `P_ne_NP_absolute_zero_args (hF5 hG4)`, `P_ne_NP_paper_faithful (hfront)` | **CONDITIONAL** — every one takes an explicit hypothesis (`AgentF5_…`, `AgentG4_…`, or `CookLevinFrontierHyp`) | clean-conditional **[G]** |
| **4. "hypothesis-free" marker** | `P_ne_NP_absolute_zero_hypothesis_is_hypothesis_free : True := trivial` | **NOT A PROOF** — a `True := trivial` status stub | n/a **[G]** |

## Live custom axioms (the whole repo, non-archived)

Confirmed by grep `[G]`:
- `MatrixSPDP.gadget_factoring_linearmap_form`
- `PAC.gadget_spdp_subspace_factoring`, `PAC.gadget_spdp_subspace_factoring_paperFaithful`
- `GlobalGodMoveGauge.exists_amplituhedron_gauge`, `…_for_sat_decider`,
  `GlobalGodMoveGauge.exists_theorem207_witness`,
  `…exists_theorem207_semantic_identity_minor_gap_source_transport_data`

> **RESOLVED (axiom→hypothesis demotion, commits `872d41e1`, `cea13b05`).**  All four God-Move axioms in
> `GlobalGodMoveGauge.lean` are now **demoted to explicit named hypotheses** (`def … : Prop`/`Type`), threaded
> through their consumer chains (entirely contained to that file; zero external code used them):
> `exists_amplituhedron_gauge → AmplituhedronGaugeHyp`,
> `exists_amplituhedron_gauge_for_sat_decider → SatDeciderGaugeHyp`,
> `exists_theorem207_witness → Theorem207WitnessHyp`,
> `exists_theorem207_semantic_… → Theorem207SemanticHyp`.
> **No `axiom` declarations remain in the file.**  Kernel-verified: `piStar_rank_monotone` and
> `no_bounded_sat_decider_…_from_rank_sandwich` are now `[propext, Classical.choice, Quot.sound]` — Route G is
> now conditional on the explicit hypotheses, never on custom axioms.  Full build green (8068 jobs).
> *Remaining (separate, outside this demotion):* the non-God-Move axioms `gadget_factoring_linearmap_form`
> (`MatrixSPDP`) and `gadget_spdp_subspace_factoring*` (`PAC`).

**These power Item 3 (the God-Move / extraction).**  They are *not* used by the clean Item-4 route
`peqnp_false_of_frontier` (which I kernel-checked is `[propext, Classical.choice, Quot.sound]`).  So the
repo has **two distinct routes** to the conditional separation:

* **Route F (clean):** `CookLevinFrontierHyp` (a Prop socket) `+` the axiom-free NP-side bound
  `⇒ P ≠ NP`, with kernel-only axioms.  The single unproved object is the **Prop** `CookLevinFrontierHyp`.
* **Route G (God-Move):** rests on the **custom axioms** `exists_amplituhedron_gauge` /
  `exists_theorem207_witness`.  These are *not* Props-to-discharge; they are *asserted axioms*, exactly the
  "disguised assumption" risk.  The rank-monotone extraction `T_Φ` is **axiomatised, not proved.**

## Answers to the two questions

**Does it all reduce to `CookLevinFrontierHyp`?**
On **Route F (the clean route): yes.**  The P-side upper bound (Item 1) is the only unproved object, packaged
as the Prop `CookLevinFrontierHyp`; the NP-side (Item 2) and the arithmetic sandwich (Item 4) are genuinely
proved and axiom-free.  Discharging `CookLevinFrontierHyp` would give `P ≠ NP` with clean axioms.

**What must `CookLevinFrontierHyp` contain?**
After the N-frame/KRW amortization audit, the P-side gap is sharper: `CookLevinFrontierHyp` must include a
**No Fixed-Structure Amortization** theorem.  It is not enough to assert that the compiled object has low local
rank/cost.  One must also prove that a P-time compiled computation cannot exploit the fixed known global
structure of the search object to reuse/cancel the fresh cost across recursive levels.  In recurrence form, the
missing statement is that

```text
Amort(C_k) = 2·cost(C_{k-1}) + fresh_cost_k - cost(C_k)
```

is bounded by the allowed linear/error term at every level.  Without this no-amortization theorem, the P-side
claim is exactly the fixed-object amortization frontier identified in the circuit/KRW barrier map.  See
`PVSNP1_NO_AMORTIZATION_PATCH.md` for the paper-facing insertion.

**But there is a second, *non-equivalent* load-bearing assumption.**
Route G's God-Move extraction is **a live custom axiom** (`exists_amplituhedron_gauge` and the Theorem-207
witnesses), **not** reducible to `CookLevinFrontierHyp` and **not** proved.  This is precisely item 3 of the
spine, and the audit confirms the worry: *the "Global God-Move" is currently an axiom, not a theorem.*  If a
proof ever asserts `P ≠ NP` via Route G, it is resting on these axioms — treat any such claim as
**conditional on unproved custom axioms**, not unconditional.

**Is there a salvageable new lemma?**
Yes — **Item 2 is the genuine asset**: an axiom-free, proved *super-polynomial SPDP-rank lower bound* for an
explicit Tseitin / identity-minor family (`compiled_np_lower_bound_any_dtm`, `C(n/3, log n)`), consistent
with the genuinely-proved BSW expander–Tseitin width kernel elsewhere in the repo.  That is real
mathematics and survives the audit.  Items 1 and 3 are *not* salvageable as proofs: Item 1 is an honest
unproved Prop (`CookLevinFrontierHyp`), and Item 3 is an unproved custom axiom.

## Relation to the Layer-10 frontier scaffold

This audit's structure matches the Layer-10D scaffold already built:
- `CookLevinFrontierHyp → P ≠ NP` is the Step4Compiler analogue of
  `Layer10.p_ne_np_of_np_hard` / `Layer11.p_ne_np_of_np_hard_dag`.
- `ObserverFrontierHyp L → ¬ Ppoly L` (`Layer10ObserverHolography`) is the same shape for the God-Move /
  observer idea — and, crucially, it is a **named hypothesis with a proven bridge**, *not* a custom axiom.
  The honest upgrade for Route G is to **demote `exists_amplituhedron_gauge` from an `axiom` to a `def …
  : Prop` hypothesis** and re-derive `piStar_rank_monotone` *conditionally* on it — then the God-Move stops
  being a disguised assertion and becomes an explicit, falsifiable hypothesis like `CookLevinFrontierHyp`.

## Recommendation

1. **Route F is the honest spine.**  Keep `P ≠ NP` strictly conditional on `CookLevinFrontierHyp`; the
   NP-side lower bound is the proved core to build on.
2. **Quarantine Route G's axioms.**  Convert `exists_amplituhedron_gauge` / `exists_theorem207_witness` from
   `axiom` to explicit `Prop` hypotheses (or move them beside the archived unsafe set), so no theorem
   silently depends on them.  The rank-monotone extraction is the paper's real gap and must be a hypothesis,
   not an axiom.
3. **No unconditional `P ≠ NP` exists in the repo.**  Every top-level `P ≠ NP` carries an explicit
   hypothesis (`CookLevinFrontierHyp`, `AgentF5/G4`); the "hypothesis-free" symbol is a `True := trivial`
   stub.  This is the correct, honest state — keep it that way.
