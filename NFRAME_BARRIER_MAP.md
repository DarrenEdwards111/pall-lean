# N-Frame Super-Linear: Conditional Theorem + Barrier Map

**Status.** Every reduction below is machine-checked in Lean 4 (`#print axioms` ⊆
`[propext, Classical.choice, Quot.sound]`, no `sorry`), on branch `razborov-recoverRho-wip`.
This document states, as one conditional theorem, exactly what the N-frame program establishes, and
maps precisely where the single remaining inequality sits and why no current technique reaches it.

**Scope (honest).** This is a *conditional* super-linear lower bound plus a *barrier map*. It reduces
an explicit-function circuit lower bound to a single inequality and proves that inequality is the
general super-linear circuit lower bound itself. It is **not** a proof of super-linear circuit lower
bounds, and **nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.**

---

## 0. The object

The recursive expander-mixer family `{F_k}`, on `N = Θ(2^k)` inputs:

```
    F_0(x)      = base function on constant-size cells
    F_{k+1}(x)  = Mix_G( F_k(x_L), F_k(x_R) )      on disjoint blocks x_L, x_R
```

`Mix_G` is an **injective multi-output** mixer built from a `d`-regular **Ramanujan** graph `G`.
Complexity is measured by `coneExcess = Σ_wires (readers − 1)` (total excess fan-out), tied to circuit
length by the ledger `2·K + coneExcess ≤ length + 1` (`K` = essential variables). Write
`CE(F_k) := coneExcess` of a minimal circuit and `cN := Θ(N/d)` the mixer's fresh charge
(`fresh_cut_rank_linear`, `ComputationalDepthNFrameFreshLinear.lean` — corrects the earlier `N/d²`).

---

## 1. The Conditional Theorem

> **Theorem (machine-checked reduction).**
> If the **cross-branch direct sum** holds at every scale —
> ```
>         CE_share(F_k) ≤ cN            (equivalently  coneInter ≤ cN)
> ```
> — then `CE(F_k) = Ω(N log N)`, i.e. `cbudget(F_k)` is **super-linear**.

`CE_share` = the count of gates that depend on *both* blocks below the mixer (cross-cone /
cancellation-sharing gates); `coneInter = |cone(F_k(x_L)) ∩ cone(F_k(x_R))|` is the same quantity in
cone form. The implication is assembled from these frozen links:

| Link | File · theorem | Statement |
|---|---|---|
| **Deficit = sharing** | `…CrossBranch` · `single_scale_recurrence_deficit` | `2·CE(F_k) + fresh ≤ CE(F_{k+1}) + CE_share` — the gap from the ideal `2×` is *exactly* `CE_share`, nothing else |
| **Mixer charged fresh** | `…ConeIntersection` · `cone_intersection_deficit` | cone inclusion–exclusion puts the mixer on the `+` (fresh) side; deficit `= coneInter` |
| **Share absorbed ⇒ doubling+fresh** | `…CrossBranch` · `share_absorbed_gives_doubling`; `…RigidAdditiveMixer` · `cross_branch_from_additive_step` | `CE_share ≤ fresh − amp ⇒ 2·CE(F_k) + amp ≤ CE(F_{k+1})` |
| **Recursion unrolls** | `…ConeAmplify` · `coneExcess_amplify`, `amplify_exceeds_linear` | `2·T k + c·2^{k+1} ≤ T(k+1)` for all `k` ⟹ `c·k·2^k ≤ T k`, i.e. `Ω(N log N)` |
| **Vertical accumulation** | (annulus, proved) `…ConeAmplify` · `cut_rank_linear_bound` | each level's `+cN` is certified by a cut of size `≤` level, never violating `log|Y| ≤ N` |
| **Fresh is `Θ(N)`** | `…FreshLinear` · `fresh_cut_rank_linear` | `d·N ≤ 4·crossing ∧ crossing ≤ 2d²·matching ⇒ N ≤ 8d·matching` |

So the entire tower reduces to the one inequality. The reduction is **tight** at both ends:

- **Sufficiency** — `…RigidAdditiveMixer` · `additive_mixer_forces_superlinear`,
  `…MixerTargetSpec` · `MixerTargetSpec.forces_superlinear`,
  `…HybridSubstitution` · `hybrid_forces_superlinear`.
- **Necessity / tightness** — dropping the inequality provably breaks it:
  `…RigidAdditiveMixer` · `non_additive_mixer_breaks_cross_branch`;
  a constant per-share *ratio* is insufficient (`…ShareChargeBound` · `half_charge_does_not_close`,
  `ratio_band_survives`) — only the *absolute* `CE_share ≤ cN` closes it
  (`absolute_savings_bound_closes`); the open content is confined to one bounded regime
  (`…CrossBranchDichotomy` · `cross_branch_2x_outside_middle`, `cross_branch_gap_is_middle`).

---

## 2. The Reduction Theorem — the inequality *is* the wall

> **Theorem.** `CE_share(F_k) ≤ cN` at every scale ⟺ the general **super-linear circuit lower bound**
> for the explicit family `F_k`. It is not a sub-problem; it is the problem.

Direction (⇒) is Part 1. Direction (⇐): `CE_share ≤ cN` is an *upper* bound on cross-copy sharing,
hence a *lower* bound on the 2-copy circuit (`2·cbudget − cN`); unrolled, that is `cbudget(F_k)`
super-linear. No weaker-looking sufficient condition is known. Every reformulation of the residual —
`savings ≤ cN`, `coneInter ≤ cN`, `CE_share ≤ cN`, rank-additivity of the mixer — is the *same* quantity
in different units, because they all measure the sharing between two disjoint-input copies of `F_k`
(the direct-sum-for-circuits / Uhlig mass-production question).

---

## 3. Barrier Map — both exits terminate at the wall

```
                        CE_share(F_k) ≤ cN
                     (= super-linear circuit LB)
                    /                          \
        EXIT 0: PROVE IT                 EXIT 1: REFUTE IT
        (bound the sharing)              (mass-produce 2 copies)
              |                                  |
   ┌──────────┴───────────┐                      |
   measures / rank / info / spectral /      construct a circuit with
   tensor / substitution / gate-elim        CE_share > cN
   each dies at:                            fails at:
   ─ O(1)-Lipschitz  → DRAG CEILING         ─ disjoint inputs → no reusable
       (caps at N)                             variable-disjoint gate
   ─ ω(1)-Lipschitz  → CIRCULAR (= cbudget) ─ bilinear mixer → cancellation
   ─ rank/info/spectral → INFO-VS-SIZE GAP     costs MORE than it saves
   ─ tensor rigidity → Valiant / Strassen–  ─ injective mixer → NO small-range
       Shitov; and the BRIDGE is load-         bottleneck → Uhlig table blocked
       bearing (info-vs-size in rank costume)
   ─ gate-elimination → DRAG CEILING again
              \                                  /
               ────────────  WALL  ────────────
        super-linear circuit LB: neither provable nor
        refutable with current techniques
```

### Exit 0 — proving the bound. Each technique's death is machine-checked or grounded:

- **Restriction measures** cap at `N` — `MeasureBarrier.lean` · `restriction_lipschitz_linear`,
  `lipschitz_cap_tight` (`O(1)`-restriction-Lipschitz ⇒ `≤ N`); the drag ceiling. `ω(1)`-Lipschitz
  measures exist only as function-complexity measures = `cbudget` (circular).
- **Rank / info / spectral** bound *bits*, not *gates* — the **info-vs-size gap**,
  `InfoSizeGap.lean` · `coneExcess_not_bounded_by_info` (a hard-but-low-information shared
  subcomputation is few bits yet many gates). Linear/algebraic sharing *is* bounded
  (`ShareKernel.lean` · `share_kernel_left_dim_bound`, rank–nullity), which is exactly why only the
  *nonlinear* sharing survives.
- **Tensor rigidity + additivity** — reducing the mixer to a rigid, direct-sum-additive tensor lands
  on two named open problems (`…RigidAdditiveMixer` · `flattening_additivity_incompatible_with_coupling`:
  the clean `R=fr` additivity route forces *decoupling*, incompatible with the coupling that forces the
  charge — Valiant on one horn, Strassen/Shitov on the other). And critically, the tensor is **not the
  wall**: an explicit tensor (`identity ⊕ n W-gadgets`) meets *every* rank condition
  (`…BridgeObstruction` · `rank_spec_satisfiable`, `coupled_substitution_tight_exists`), yet the direct
  sum still fails, because the load-bearing hypothesis is the **bridge** `CE_share ≤ 2R − R2`
  (`bridge_is_load_bearing`) — the info-vs-size gap in rank costume.
- **Substitution method** — the unique direct-sum-*additive* rank tool, so additivity is free
  (`…HybridSubstitution`); but it reduces to substitution *near-tightness* on an expander tensor
  (`substitution_tightness_necessary`), which is open, and — via the bridge above — even a perfect
  tensor does not close the *circuit* bound.
- **Gate elimination** — the only tool that counts gates directly — caps at `~3.01n` (linear); on
  `F_k` each variable-restriction kills `O(1)` gates and the recursion does not amplify. This *is* the
  drag ceiling (`O(1)`-per-step ⇔ `O(1)`-Lipschitz), already frozen.

### Exit 1 — refuting the bound (mass production). Fails **structurally**, tracking actual gates:

- `k=1`: `cbudget(F_1)=4`; two disjoint copies `= 8 = 2×`, `CE_share = 0` (products variable-disjoint).
- **Cancellation** costs *more* — recovering `{a₁a₃, b₁b₃}` via `(a₁+b₁)(a₃+b₃)` needs 4 products vs 2.
- **Uhlig table** (the only technique beating direct sum) requires a small-range bottleneck; the
  **injective** mixer makes `F_k(x)` determine `x`, so there is none.
- Recursion (`k≥2`): sharing does not emerge — the three firewall properties (disjoint inputs /
  bilinear mixers / injective mixers) are *exactly* the three that block the three mass-production
  mechanisms.
- **But:** this is *failure to refute*, not *proof of resistance* — a clever Boolean circuit not
  respecting the polynomial structure is not excluded, and excluding it *is* the lower bound.

---

## 4. What a working certificate would have to be

A gate-sharing certificate that closes `CE_share ≤ cN` must be **all four** at once — and no known
object is:

1. **gate-valued** — bounds a gate count, not information/rank (else info-vs-size gap);
2. **not per-step-bounded** — not `O(1)`-restriction-Lipschitz (else drag ceiling, `≤ N`);
3. **non-natural** — not (constructive ∧ large), else Razborov–Rudich breaks PRGs;
4. **structure-specific** — exploits `F_k`'s recursion, not a generic property.

Conditions 1–2 are frozen walls of this project; 3–4 are the natural-proofs / general-circuit barriers.

---

## 5. Verdict

The N-frame route is **fully mapped**. The internal reductions are machine-checked and reduce an
explicit-function super-linear circuit lower bound to a single inequality; that inequality is *proven
to be* the general super-linear circuit lower bound; and both directions of attack — prove and refute —
terminate at the field-wide wall, for reasons each named precisely above (drag ceiling, info-vs-size
gap, Valiant/Strassen–Shitov, Uhlig-bottleneck-vs-injectivity). This is a complete conditional result
and barrier map. It is **not** a path to super-linear lower bounds — hence not to `P ≠ NP` — with
current techniques, and it does not claim to be. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

*File index (all `PallLean/Paper93/DeepMath/PathB/`, prefix `ComputationalDepthNFrame` unless noted):*
`ConeAmplify`, `CrossBranch`, `CrossBranchDichotomy`, `ConeIntersection`, `ShareChargeBound`,
`FreshLinear`, `RigidAdditiveMixer`, `MixerTargetSpec`, `HybridSubstitution`, `BridgeObstruction`;
barriers `MeasureBarrier`, `InfoSizeGap`, `GlobalNecessity`, `ShareKernel`, `DragCeiling`.
