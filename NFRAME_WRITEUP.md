# The Amortization Barrier: A Conditional Framework Unifying Circuit Direct-Sum and KRW Composition

*A machine-checked synthesis (branch `razborov-recoverRho-wip`). Every Lean theorem cited below builds with
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`, no `sorry`. Files under
`PallLean/Paper93/DeepMath/PathB/`, prefix `ComputationalDepthNFrame`.*

---

## Scope, stated once and honestly

This document assembles a conditional framework, a barrier map, and a proved restricted-class stepping
stone. It reduces an explicit super-linear circuit lower bound to a single inequality, proves that
inequality is **equivalent to** the general super-linear lower bound (so it is not a shortcut), maps why
every technique tried terminates at one identifiable obstruction, and then **proves** the analogous
statement in restricted models (formula / linear / monotone circuits) and carries the monotone case to an
explicit number. **Nothing here is a proof of `P ≠ NP`, `P ⊄ NC¹`, or `NEXP ⊄ ACC⁰`.** The value is a
precise, honest map: *where* the difficulty lives, *why*, and *where it dissolves*.

The one non-obvious thing the arc establishes:

> **The barrier is AMORTIZATION; its enabler is NEGATION; it is provable in the monotone case in both the
> circuit and communication worlds, and open in the general case in both.**

---

## 0. The object

The recursive expander-mixer family on `N = Θ(2^k)` inputs:
```
    F_0(x)      = base function on constant-size cells
    F_{k+1}(x)  = Mix_G( F_k(x_L), F_k(x_R) )      on disjoint blocks x_L, x_R
```
`Mix_G` is an injective multi-output mixer from a `d`-regular Ramanujan graph. Complexity is measured by
`coneExcess = Σ_wires (readers − 1)`, tied to circuit length by the ledger `2·K + coneExcess ≤ length + 1`.
`cN := Θ(N/d)` is the mixer's fresh charge (`…FreshLinear · fresh_cut_rank_linear`, correcting an earlier
`N/d²`).

---

## Part I — The circuit route: a conditional theorem and its wall

**Conditional Theorem (machine-checked reduction).** If the cross-branch direct sum
`CE_share(F_k) ≤ cN` holds at every scale, then `CE(F_k) = Ω(N log N)` — super-linear. Assembled from
frozen links: `…CrossBranch · single_scale_recurrence_deficit` (the deficit from the ideal `2×` recurrence
is *exactly* the shared-gate count `CE_share`), `…ConeIntersection · cone_intersection_deficit` (cone
inclusion–exclusion charges the mixer as fresh), and `…ConeAmplify · amplify_exceeds_linear` (the recursion
`2·T k + c·2^{k+1} ≤ T(k+1)` unrolls to `Θ(N log N)`). Tightness at both ends is proved
(`…ShareChargeBound`: a per-share *ratio* is insufficient, only the absolute `CE_share ≤ cN` closes it;
`…CrossBranchDichotomy`: the open content is confined to one bounded regime).

**Reduction Theorem.** `CE_share ≤ cN` **⟺** the general super-linear circuit lower bound for `F_k`. It is
not a sub-problem — it *is* the problem. Every reformulation (`savings ≤ cN`, `coneInter ≤ cN`,
rank-additivity of the mixer) is the same quantity: the sharing between two disjoint-input copies of `F_k`
(direct-sum-for-circuits / Uhlig mass production).

---

## Part II — The barrier map: every exit terminates at amortization

Both directions of attack were walked to their end.

**Exit 0 (prove `CE_share ≤ cN`).** Each technique's death is machine-checked or grounded:
- restriction measures cap at `N` (`…MeasureBarrier · restriction_lipschitz_linear` — the drag ceiling);
  `ω(1)`-Lipschitz ones are circular (`= cbudget`);
- rank / info / spectral bound *bits*, not *gates* — the info-vs-size gap
  (`…InfoSizeGap · coneExcess_not_bounded_by_info`); linear sharing *is* bounded
  (`…ShareKernel · share_kernel_left_dim_bound`, rank–nullity), so only nonlinear sharing survives;
- tensor rigidity + additivity lands on Valiant / Strassen–Shitov, and crucially the tensor is **not the
  wall**: an explicit tensor (`identity ⊕ n W-gadgets`) meets every rank condition
  (`…BridgeObstruction · rank_spec_satisfiable`) yet the direct sum still fails, because the load-bearing
  hypothesis is the *bridge* `CE_share ≤ 2R − R2` (`bridge_is_load_bearing`) — the info-vs-size gap in rank
  costume;
- gate-elimination caps at `~3n` — itself the drag ceiling.

**Exit 1 (refute — mass-produce two copies).** SAT-based exact synthesis over the full binary basis: the
real 4-input W-coupling mixer and 10 other functions all have `cbudget(F ⊕ F) = 2·cbudget(F)` exactly
(`CE_share = 0`, forced disjointness), and every mass-production mechanism fails structurally (disjoint
inputs → no reusable gate; bilinear mixer → cancellation costs more; injective mixer → no Uhlig
bottleneck). But this is *failure to refute*, not *proof of resistance*.

**The information/work boundary charge cannot escape it.** Any charge dominated by information is blind
(`…InfoBoundaryTest · info_bounded_charge_blind_to_gate_sharing`); the thermodynamic *work* version is also
blind, because Bennett's reversible computing decouples erasure work from gate count
(`thermo_work_blind_reversible_computing`). A working certificate must be gate-valued, non-incremental, and
non-natural — no such object is known.

---

## Part III — The amortization core, and where it splits

The deficit `CE_share` equals the count of **mixed gates** — gates depending on both blocks
(`…FreshnessLemma · deficit_is_mixed`, via the restriction pillar `foreign_inputs_no_speedup`: `b`-inputs
never reduce `cbudget(F_k(a))`). Each mixed gate's foreign content must cancel. The question — the whole
frontier — is whether that cancellation is **non-reusable** (fresh) or can be **amortized**.

Analysed to the finest operational level (the `√m`-carrier construction: `s` carriers `op(P_j,Q_j)` feed
`C(s,2) ≈ m` double-duty gates, counting saving `m − √m > 0`):

> **net saving = (counting saving) − (foreign-content cancellation cost),**

and the cancellation cost is a *tensor-rank-under-direct-sum* quantity:
- **linear circuits:** rank–nullity ⟹ cost ≥ saving ⟹ amortization **impossible** (proved, `share_kernel`);
- **nonlinear circuits:** = **Shitov subadditivity** ⟹ generically possible, explicit-`F_k` **open**.

So: **double-duty amortization ⟺ explicit tensor subadditivity.** This is the final form of the wall.

---

## Part IV — Restricted classes: where Freshness is a THEOREM

`…RestrictedFreshness` freezes the classes where the amortization mechanism is absent:
- **Formula** (fan-out ≤ 1): a gate feeds one place → `coneInter = 0` (`formula_freshness`).
- **Linear** (XOR): rank–nullity (`share_kernel_left_dim_bound`).
- **Monotone** (no negation): can only *mask*, never *cancel* foreign content → `beneficialInter = 0`
  (`no_cancellation_freshness`).

In each, `restricted_freshness_forces_superlinear` runs the amplification unconditionally — consistent with
the known monotone (Razborov) and formula (Andreev/KRW) super-polynomial bounds. **Negation is the enabler
of amortization; monotone is its universal soft spot.**

---

## Part V — The KRW pivot: same barrier, more tractable world

Formulas have fan-out ≤ 1, so the sharing wall does not apply; the difficulty moves to **formula depth =
Karchmer–Wigderson communication complexity**, and the composition question is KRW,
`CC(KW_{f ⋄ g}) ≈ CC(KW_f) + CC(KW_g)` (whose truth gives `P ⊄ NC¹`). Framework in `…KRW`:
`krw_amplifies` (per-level increment `Δ` ⟹ depth `d·Δ`) and `krw_beats_log_depth` (increment beating the
log block size ⟹ super-log depth).

**The general KRW increment IS the amortization** (`…KRWGeneral`):
`CC(KW_{f ⋄ g}) = CC(KW_f) + CC(KW_g) − amort`, and `amort = 0` ⟹ full increment
(`krw_increment_from_no_amortization`). Provable core: the iterated universal relation is super-log — but
*for a relation* (`universal_relation_superlog`); the best general *function* bound is Håstad's
`(3−o(1)) log n` (`hastad_general_depth`).

**Strong→standard reduction = non-monotone amortization** (`…KRWStrongStandard`). Strong composition is
standard "forced to behave like a direct-sum problem" — `amort = 0` by construction — and *in the monotone
setting strong = standard* (arXiv 2306.00615). So the gap is a purely non-monotone phenomenon, enabled by
negation, exactly as in the circuit route. The recent strong bound (XOR ∘ random function, arXiv 2410.10189)
would give `~3.04 log n` — beating Håstad after 25+ years — **if** the reduction holds
(`strong_beats_hastad_if_reduces`). The whole improvement is contingent on non-monotone amortization
being `0`.

---

## Part VI — The monotone stepping stone, to an explicit number

In the monotone world everything is provable. `…KRWMonotone` instantiates the framework with cited
monotone depth theorems (st-connectivity `Θ(log² N)` [Karchmer–Wigderson]; lifted functions
`Θ(q·log m)` [Raz–McKenzie / Göös–Pitassi–Watson]) to derive unconditional super-log monotone depth
(`connectivity_monotone_superlog`, `lifting_monotone_superlog`). `…KRWMonotoneExplicit` carries the cited
increment to an explicit number:

  `monotone_depth_log_squared` — monotone depth `≥ (log N)²`;
  `monotone_depth_2pow100` — at `N = 2^100`, monotone formula depth **`≥ 10000`**, exceeding `50·log N`;
  `monotone_depth_beats_ncone` — outside `NC¹`-depth `c·log N` for every `c ≤ 99`.

The depth *inputs* are cited (they rest on communication complexity, not formalized); the explicit numeric
depth the framework extracts is machine-checked.

---

## The unified picture

| | Circuit world (direct sum) | Communication world (KRW) |
|---|---|---|
| **Obstruction** | double-duty amortization of mixed gates | `amort` in `CC(KW_{f⋄g}) = CC_f + CC_g − amort` |
| **Enabler** | negation (cancellation) | negation (strong ≠ standard) |
| **Monotone** | Freshness proved (`no_cancellation_freshness`) | strong = standard, KRW proved (lifting) |
| **General** | = explicit tensor subadditivity (Shitov) — open | = KRW conjecture = `P ⊄ NC¹` — open |
| **Best unconditional** | forced disjointness verified to `cbudget ≤ 4` | monotone `(log N)²`; general `(3−o(1)) log n` |

One obstruction, two lenses. It is a *theorem* in the monotone case in both worlds and *open* in the general
case in both. The circuit route reached a dead wall (Shitov, non-explicit); the communication route reached a
*named, moving frontier* (strong→standard, `3.04 log n`). That is the reason the KRW pivot was worth making.

---

## What is proved, cited, conditional, open

- **Proved (machine-checked):** all reductions and amplifications; the restricted-class Freshness theorems
  (formula/linear/monotone); the framework arithmetic; the explicit numeric monotone depth (`≥ 10000` at
  `N = 2^100`); the SAT forced-disjointness data (`cbudget ≤ 4`).
- **Cited (not formalized — need communication complexity, absent from Mathlib):** the monotone KRW / KW /
  lifting depth theorems whose numeric output the framework consumes.
- **Conditional:** super-linear circuit LB (on `CE_share ≤ cN`); the `3.04 log n` improvement (on the
  strong→standard reduction).
- **Open (= the frontier):** general amortization = explicit tensor subadditivity (circuit) = KRW increment
  = `P ⊄ NC¹` (communication).

---

## File index (`PallLean/Paper93/DeepMath/PathB/ComputationalDepthNFrame…`)

*Circuit route:* `ConeAmplify`, `CrossBranch`, `CrossBranchDichotomy`, `ConeIntersection`, `ShareChargeBound`,
`FreshLinear`, `RigidAdditiveMixer`, `MixerTargetSpec`, `HybridSubstitution`, `BridgeObstruction`,
`FreshnessLemma`, `RestrictedFreshness`.
*Barriers:* `MeasureBarrier`, `InfoSizeGap`, `Submodular`, `ShareKernel`, `InfoBoundaryTest`.
*KRW route:* `KRW`, `KRWMonotone`, `KRWGeneral`, `KRWStrongStandard`, `KRWMonotoneExplicit`.
*Companion docs:* `NFRAME_BARRIER_MAP.md`, `PROBE_PORT_FAMILY.md`. *Experiments:* SAT exact-synthesis scripts
(scratchpad, pysat + Cadical).

*Sources:* Håstad `(3−o(1)) log n`; Karchmer–Wigderson (connectivity); Raz–McKenzie / Göös–Pitassi–Watson
(lifting); Shitov (Acta Math 222, 2019); [KRW via lifting (arXiv:2007.02740)](https://arxiv.org/abs/2007.02740);
[Strong composition, FOCS 2023 (arXiv:2306.00615)](https://arxiv.org/html/2306.00615);
[Strong composition of XOR and a random function (arXiv:2410.10189)](https://arxiv.org/abs/2410.10189).

*Nothing in this document is `P ≠ NP`, `P ⊄ NC¹`, or `NEXP ⊄ ACC⁰`.*
