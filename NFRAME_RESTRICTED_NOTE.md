# Amortization, Negation, and the Monotone Soft Spot: Restricted-Class Lower Bounds and a Barrier Map

*Paper-style note of the machine-checked, unconditional results. Branch `razborov-recoverRho-wip`; all
theorems build with `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`, no `sorry`. This note states
only what is **proved** or **cited-and-instantiated**; the conditional/open parts of the program are in
`NFRAME_WRITEUP.md` and `KRW_IC_ATTACK_SHEET.md`.*

---

## Abstract

We isolate a single obstruction — **amortization** — that governs two classically distinct lower-bound
questions: the direct sum for circuit cone-excess (a super-linear circuit lower bound) and KRW composition
for formula depth (`P` vs `NC¹`). We prove that in both worlds the obstruction is *enabled by negation* and
*dissolves in the monotone case*. Concretely, we give machine-checked theorems that (i) the amortization is
absent, hence lower bounds hold **unconditionally**, in the formula, linear, and monotone circuit models
(a "Freshness Lemma"), and (ii) the KRW composition amplification is unconditional in the monotone model,
which we instantiate — via cited depth theorems — to an explicit numeric monotone formula-depth lower bound.
We accompany these with a barrier map showing that every technique reaching into the general (non-monotone)
case terminates at the same amortization obstruction, and that the circuit-side and communication-side
barriers are the *same object* (`MeasureBarrier` / counting reach the "floor"; both are blind to the
"amortization increment"). Nothing here is a proof of `P ≠ NP`, `P ⊄ NC¹`, or `NEXP ⊄ ACC⁰`.

---

## 1. The framework

Recursive expander-mixer family `F_{k+1} = Mix_G(F_k(x_L), F_k(x_R))`; cone-excess `coneExcess`; ledger
`2K + coneExcess ≤ length + 1`; mixer fresh charge `cN`. The horizontal cross-branch direct sum reduces
(machine-checked) to `CE_share ≤ cN`, where `CE_share` = the count of **mixed gates** (depending on both
recursive blocks). Each mixed gate carries foreign content that must cancel; the direct sum closes iff that
cancellation is **fresh** (non-reusable), i.e. cannot be **amortized**.

**Theorem (deficit = mixed gates; restriction pillar).** `…FreshnessLemma · deficit_is_mixed`,
`foreign_inputs_no_speedup`: `2·cbudget ≤ total + #mixed`, and `b`-inputs never reduce `cbudget` of an
`a`-only output. *Proved.*

---

## 2. Main results — Freshness is a theorem in restricted classes

The double-duty amortization mechanism reduces (via the `√m`-carrier analysis) to *explicit tensor
subadditivity*: impossible for linear circuits (rank–nullity), Shitov-open for nonlinear. In the classes
where the mechanism is *structurally absent*, the lower bound is unconditional.

**Theorem 1 (Restricted Freshness).** `…RestrictedFreshness`. In each of
- **formulas** (fan-out ≤ 1): `coneInter = 0` (`formula_freshness`);
- **linear (XOR) circuits**: rank–nullity (`ShareKernel · share_kernel_left_dim_bound`);
- **monotone circuits** (no negation): `beneficialInter = 0` (`no_cancellation_freshness`, masking-not-
  cancellation),

the direct sum holds, and `restricted_freshness_forces_superlinear` runs the amplification unconditionally.
*Proved.* Consistent with the known monotone (Razborov) and formula (Andreev/KRW) super-polynomial bounds.

**Empirical corroboration.** SAT-based exact synthesis (full binary basis, `pysat`+Cadical): the real
4-input W-coupling mixer and 10 other functions have `cbudget(F⊕F) = 2·cbudget(F)` exactly — forced
disjointness — at every reachable scale (`cbudget ≤ 4`). *Machine-verified data.*

---

## 3. Main results — monotone KRW to an explicit number

Formula depth `= CC(KW)`; KRW composition `CC(KW_{f⋄g}) ≈ CC(KW_f)+CC(KW_g)`. In the monotone model
strong = standard composition (Meir, FOCS 2023) and monotone KRW holds via query-to-communication lifting.

**Theorem 2 (KRW amplification).** `…KRW · krw_amplifies`, `krw_beats_log_depth`: a per-level increment
`Δ` gives depth `d·Δ`, super-logarithmic once `Δ` beats the log block size. *Proved.*

**Theorem 3 (explicit monotone depth).** `…KRWMonotoneExplicit`. Feeding the cited monotone increment
(Karchmer–Wigderson connectivity `Θ(log² N)`; monotone KRW via lifting) through Theorem 2:
`monotone_depth_log_squared` gives depth `≥ (log N)²`; `monotone_depth_2pow100` gives, at `N = 2^100`,
monotone formula depth **`≥ 10000`**, exceeding `NC¹`-depth `c·log N` for every `c ≤ 99`. *Framework proved;
depth input cited.*

---

## 4. The barrier map (why the general case is exactly one obstruction)

**Theorem 4 (both exits terminate at amortization).** For the general circuit direct sum, every technique
dies at the same place (`…MeasureBarrier`, `…InfoSizeGap`, `…BridgeObstruction`, `…InfoBoundaryTest`):
restriction measures cap at `N`; rank/info/spectral hit the info-vs-size gap; tensor rigidity meets
Valiant/Strassen–Shitov and the tensor is *not* the wall (`bridge_is_load_bearing`); information- and
work-boundary charges are blind (`info_bounded_charge_blind`, `thermo_work_blind` via Bennett). *Proved /
grounded.*

**The unified barrier.** Circuit and communication sides are the same object:

| | Circuit | KRW |
|---|---|---|
| bulk technique | restriction / gate-elim | counting / random-object rigidity |
| reaches (floor) | `~N` | `~n` |
| blind to (increment) | `+cN log N` | `+log m` |
| provable when | independence forced (monotone) | independence forced (strong comp) |
| open when | fixed object (general) | fixed-known-`g` (standard) |

The increment *is* the amortization; bulk techniques reach the floor and are provably blind to it.

---

## 5. Scope

**Unconditional & machine-checked:** Theorems 1–4, the framework reductions, the SAT data, the explicit
monotone number. **Cited (not formalized — need communication complexity, absent from Mathlib):** the
monotone KW/lifting depth theorems whose numeric output Theorem 3 consumes. **Conditional:** super-linear
circuit LB (on `CE_share ≤ cN`). **Open:** general amortization = explicit tensor subadditivity (circuit) =
KRW increment = `P ⊄ NC¹` (communication) = *"a typical fixed known `g` admits no exploitable outer↔inner
correlation."*

**This note contains no proof of `P ≠ NP`, `P ⊄ NC¹`, or `NEXP ⊄ ACC⁰`.** Its contributions are: the
amortization/negation unification, the machine-checked restricted-class lower bounds, the explicit monotone
number, and the barrier map identifying the circuit and communication obstructions as one.

*Files: `…ComputationalDepthNFrame{ConeAmplify,CrossBranch,ConeIntersection,FreshLinear,ShareKernel,
FreshnessLemma,RestrictedFreshness,MeasureBarrier,InfoSizeGap,BridgeObstruction,InfoBoundaryTest,KRW,
KRWMonotone,KRWMonotoneExplicit,KRWGeneral,KRWStrongStandard}`. Sources: Håstad; Karchmer–Wigderson;
Raz–McKenzie / Göös–Pitassi–Watson; Shitov; GMWW; Dinur–Meir; Meir (arXiv:2306.00615, 2410.10189).*
