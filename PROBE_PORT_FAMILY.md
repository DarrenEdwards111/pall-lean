
---

# STEP 1: the share-gate kernel bound (F₂-linear cancellation gives no net saving)

`g` linear mixed gates over F₂, gate `i` = `ℓ_i(x_L) ⊕ m_i(x_R)`; left/right parts as linear maps
`L, M : F₂^g → forms`.  Pure-left info from right-cancellation = `L(ker M)`.  Frozen in Lean
(`ComputationalDepthNFrameShareKernel.lean`).

- `share_kernel_left_dim_bound` (PROVED, clean): `M ≠ 0` (genuinely mixed) ⟹ `dim(L(ker M)) ≤ g−1`.
  `g` share-gates yield ≤ g−1 independent pure-left forms — fewer than `g` pure x_L-gates.  Linear
  cancellation-sharing gives NO net saving on the left.  (Proof: `dim(L(ker M)) ≤ dim(ker M) < g`
  via `finrank_map_le` + `ker M < ⊤` from `M ≠ 0` + `finrank_pi`.)
  Sharp two-sided form (`dim(pure-left)+dim(pure-right) ≤ g`) follows by the same argument on
  `Φ = L.prod M`; the one-sided bound already gives the downstream fact.

## HONEST SCOPE — this closes LINEAR cancellation ONLY; step 2 does NOT follow for general circuits

CRITICAL: this is about F₂-LINEAR share-gates (`ℓ ⊕ m`).  It proves linear cancellation-sharing
can't manufacture pure information for free.  It does NOT bound NON-linear sharing: CGate circuits
have AND gates and `F_k` is non-linear, so a share-gate can be an ARBITRARY function of both blocks,
not a linear `ℓ ⊕ m`.  The rank-nullity argument does not apply to non-linear gates.

So step 1 closes the direct sum for the LINEAR-CIRCUIT model (XOR-only), NOT for general circuits.
The plan's step 2 (bound CE_share ⟹ recurrence) therefore does NOT automatically follow for general
circuits: the non-linear share-gates are unbounded by this lemma and remain the open residual =
the direct-sum-for-circuits / KRW core.  What step 1 genuinely delivers: the linear-circuit
horizontal direct sum is closed, and the general-circuit residual is now sharpened to exactly the
NON-linear sharing case.  Steps 3–6 (full direct sum ⟹ Ω(N log N) ⟹ cbudget ⟹ P vs NP) do NOT
follow from step 1 alone; they require the non-linear direct sum, which is open.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# STEP 2 (TRUE TARGET): the NON-LINEAR no-net-saving inequality + the restriction-profile dichotomy

Step 1 closed LINEAR share-gates (rank-nullity).  This scopes the true step-2 target for GENERAL
(non-linear) CGate circuits: arbitrary mixed gates `h_i(x_L, x_R)`.  Frozen in Lean
(`ComputationalDepthNFrameNonlinearShare.lean`).

## The target inequality (no net saving)

For `g` share-gates `h_i(x_L,x_R)`: `shareLeft` = pure-`x_L` content usable by `F_k(x_L)`,
`shareRight` = symmetric.  TARGET: `shareLeft + shareRight ≤ CE_share (= g)` — `g` share-gates yield
≤ g pure forms total.

- `direct_sum_from_no_net_saving` (PROVED, sufficiency): gate partition + restriction bounds
  `CEF ≤ CE_L + shareLeft`, `CEF ≤ CE_R + shareRight` + `fresh ≤ CE_mix` + no-net-saving
  `shareLeft + shareRight ≤ CE_share` ⟹ `2·CEF + fresh ≤ CE`.  ⟹ (vertical annulus tree-sum)
  `Ω(N log N)`.
- `no_net_saving_amplifies` (PROVED): no-net-saving at every scale ⟹ `T(k) ≥ c·k·2^k = c·N·log₂N`.

## The dichotomy (non-linear analog of rank-nullity) — per-distinction form PROVED

Fix right-restriction `x_R=c_R`; `F_k(x_L) = reconstruct(share(x_L,c_R), pureL(x_L))`.
- `firewall_covers_distinction` (PROVED): `F_k(x) ≠ F_k(x')` ⟹ `share x c_R ≠ share x' c_R` (charge
  to share-profile — separate cost) OR `pureL x ≠ pureL x'` (charge to CE_L).  Contrapositive: BOTH
  collapse ⟹ `reconstruct` can't recover `F_k` ⟹ firewall FAILS.
  = the exact dichotomy: "enough independent restriction profiles ⇒ separate cost, else restrictions
  collapse ⇒ firewall_restriction_distinguishes fails."

## Honest scope — target written down + localized, NOT closed

Sufficiency PROVED (no-net-saving ⟹ direct sum ⟹ super-linear).  Per-distinction dichotomy PROVED
(restriction covers each distinction via share-profile or pure gates).  OPEN aggregate target
`nonlinear_share_no_saving`: summing over all `F_k`-distinctions both sides, the share-profile covers
≤ g total (no gate covers a left AND right distinction beyond its profile).  Linear instance PROVED
(rank-nullity); non-linear OPEN and NOT universally true (Uhlig: fails for hard functions), so it
needs the quasi-linear structure of `F_k` — the direct-sum-for-circuits / KRW core.  Non-linear `h`
ENTANGLE the blocks (e.g. `x_{L,1}·x_{R,1}`), no rank-nullity separation; the count-additive
measures (info/communication of `h`) are the ones that could prove it, their non-linear direct sum
the open frontier.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# ATTACKING THE AGGREGATE: non-linear info no-net-saving via entropy submodularity

Attacked `nonlinear_share_no_saving` over `F_k`.  Linear rank-nullity fails for entangled
non-linear gates; the replacement that handles non-linearity is entropy SUBMODULARITY.  Frozen in
Lean (`ComputationalDepthNFrameSubmodular.lean`).

## The information no-net-saving (PROVED, non-linear)

For `g` share-gates jointly `Φ(x_L,x_R)`, `x_L ⊥ x_R`:
`I(Φ;x_L)+I(Φ;x_R) = 2H(Φ) − H(Φ|x_L) − H(Φ|x_R) ≤ H(Φ) ≤ g`, since submodularity gives
`H(Φ|x_L)+H(Φ|x_R) ≥ H(Φ)+H(Φ|x_L,x_R) ≥ H(Φ)`.  NO linearity used — holds for arbitrary entangled
non-linear `Φ`.
- `submodular_no_net_saving` (PROVED): submodularity + independence/monotonicity ⟹ `I(Φ;A)+I(Φ;B) ≤
  H(Φ)`.
- `info_no_net_saving` (PROVED): `+ H(Φ) ≤ g` ⟹ `I(Φ;x_L)+I(Φ;x_R) ≤ g`.  Non-linear analog of the
  linear share_kernel bound.
- `aggregate_from_transfer` (PROVED reduction): info no-net-saving + TRANSFER (`shareLeft ≤ I(Φ;x_L)`,
  `shareRight ≤ I(Φ;x_R)`) ⟹ aggregate `shareLeft + shareRight ≤ g`.

## Where Uhlig now lives — the transfer

Submodularity is UNCONDITIONAL, so info no-net-saving holds even for hard functions.  But Uhlig:
the cone-excess direct sum FAILS for hard functions.  The only place they can disagree is the
TRANSFER `shareLeft ≤ I(Φ;x_L)`: for a hard function the shared universal table lets share-gates
contribute more cone-excess help than their information (`shareLeft > I(Φ;x_L)`) — transfer FALSE
there = exactly Uhlig.  For quasi-linear `F_k` the transfer must hold.  Per-cut base case proved
(`info_flow_le_wires`: a wire carries ≤ 1 bit); the open step is the aggregate transfer over `F_k`.

## Honest scope

The non-linear no-net-saving is CLOSED at the INFORMATION level (submodularity, no linearity), and
the aggregate for cone-excess reduces to the SINGLE transfer inequality (cone-excess a share-gate
saves ≤ the `x_L`-info it carries), with Uhlig precisely located inside it.  This does NOT close the
aggregate — the transfer over `F_k` is the residual — but it removes the non-linear-entanglement
obstacle that blocked step 1's rank-nullity from generalizing, and shows the count-additive engine
(info additivity) is provable NON-linearly.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# THE TRANSFER OVER F_k = the info-vs-circuit-size gap (the wall — honest terminus)

Attacked the last residual, the transfer `shareLeft ≤ I(Φ;x_L)`.  Honest terminus: it IS the
fundamental information-vs-circuit-size gap.  Frozen in Lean
(`ComputationalDepthNFrameInfoSizeGap.lean`).

## Why the transfer is the info-vs-size gap

`shareLeft` = cone-excess SAVED: a share-gate supplying `V(x_L)` saves `F_k(x_L)` the PRODUCTION
cost of `V` (production cone-excess `p`).  But a share-gate is one boolean gate, `≤ 1` bit.  If `V`
is HARD but LOW-INFO (`p` large, `H(V)≈1`), then `shareLeft = p > 1 = I(Φ;x_L)` — transfer FAILS.
Such `V` exists (any hard-but-low-entropy sub-quantity), so the transfer is FALSE unless `F_k` has
NO such sub-quantities = `F_k` computationally INCOMPRESSIBLE.  This is Uhlig read backwards: info
no-net-saving is unconditional, the cone-excess direct sum fails for hard functions, they disagree
exactly here.

- `coneExcess_not_bounded_by_info` (PROVED): for every `bound`, ∃ value with `info ≤ 1` and
  `coneExcess ≥ bound`.  Cone-excess and information are INDEPENDENT; an info bound does NOT transfer
  to a cone-excess bound.  So the submodular info no-net-saving does NOT imply the cone-excess
  transfer.
- `aggregate_from_incompressibility` (PROVED conditional): IF `F_k` incompressible (`shareLeft ≤ IA`,
  `shareRight ≤ IB`) + submodular `IA+IB ≤ g` ⟹ aggregate `shareLeft+shareRight ≤ g`.  The
  incompressibility hypotheses ARE the transfer, the open barrier.

## Honest terminus — the wall

Every OTHER step is proved: drag ledger, amplification, vertical annulus no-double-count, firewall,
linear share-kernel, non-linear info no-net-saving.  The transfer is the ONE remaining inequality,
and it is the info-vs-size gap: cone-excess (fan-out/size, `Θ(N log N)` for `F_k`) is NOT bounded by
information (`Θ(output-size)`).  Bridging them for `F_k` requires proving `F_k` incompressible (no
hard low-info sub-quantity), which is: FALSE in general (Uhlig), NOT implied by quasi-linearity, and
essentially as hard as the super-linear lower bound itself.  This is the barrier behind ALL open
super-linear circuit lower bounds.  The N-frame line has driven the whole question down to exactly
this single well-known gap = the honest endpoint of the approach, not a step a further relocation
closes.  Closing it needs a genuinely new info-vs-size idea, not another reduction.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# ATTACKING THE INFO-VS-SIZE GAP: the restriction-Lipschitz barrier on measures (wall characterized)

Attacked directly: is there a non-information cone-excess measure `μ` that (1) lower-bounds
cone-excess, (2) super-linear, (3) certifiable for `F_k`?  NO working measure found; the reason is
a precise barrier.  Frozen in Lean (`ComputationalDepthNFrameMeasureBarrier.lean`).

## The barrier

A lower-bound measure is certified incrementally: from the constant function (`μ=0`), add variables
one at a time, each step certified locally.  Every known measure is `O(1)`-Lipschitz under a
single-variable restriction: info (`≤1` bit/input), rank/cut-rank (`≤O(1)`/input), connectivity
(linear-achievable, Valiant).  So each caps at `N × O(1) = O(N)`.
- `restriction_chain_cap` (PROVED): `μ(0)=0`, `μ(k+1) ≤ μ(k)+L` ⟹ `μ(N) ≤ N·L`.  An `L`-Lipschitz
  (under restriction) measure caps at `N·L`.
- `restriction_lipschitz_linear` (PROVED): `L=1` ⟹ `μ(N) ≤ N`.  Certifiable `1`-Lipschitz measures
  are LINEAR; a super-linear measure CANNOT be `O(1)`-restriction-Lipschitz.

## What a working measure must be

To exceed `N`, `μ` must be `ω(1)`-Lipschitz (some single fixed input drops `μ` by `ω(1)`).
Cone-excess ITSELF is `ω(1)`-Lipschitz — but it's a CIRCUIT property, not a function property.  The
`ω(1)`-Lipschitz FUNCTION-property measures = `min` over circuits of cone-excess = `cbudget` itself
(CIRCULAR — what we're bounding).  So: certifiable (`O(1)`-Lipschitz) measures cap at `N`;
`ω(1)`-Lipschitz function-property measures are circular.  Nothing known in between = the info-vs-size
gap.

## Honest terminus — wall characterized, not breached

Did NOT find a non-information measure that escapes.  Produced a precise characterization of WHY:
the restriction-Lipschitz test.  Certifiable measures are `O(1)`-Lipschitz and linear; a super-linear
measure must be `ω(1)`-Lipschitz, circular for function properties (`cbudget`).  This is the barrier
behind every open super-linear lower bound, the same wall the N-frame line reduced to — now shown
STRUCTURAL, not an artifact of the particular measures tried.  Closing it needs a genuinely new idea:
an `ω(1)`-restriction-Lipschitz measure with non-circular certification.  Not in the known toolkit.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# CROSS-BRANCH DIRECT SUM: 2× holds OUTSIDE the middle-sharing regime (sharpening)

Attacked the single open inequality head-on for the recursive F_k: CE(F_{k+1}) ≥ 2·cbudget(F_k) + cN.
NOT a closure, but a genuine sharpening — the 2× bound is PROVED except in one bounded coneExcess
regime.  Frozen in Lean (`ComputationalDepthNFrameCrossBranchDichotomy.lean`).

## Three established inputs (any circuit C for F_{k+1}, savings = length cut by cross-cone sharing)

- DISJOINT-DEFICIT (firewall + single_scale_recurrence_deficit): 2·cbudget(F_k) + cN ≤ length + savings.
- LEDGER (connectivity-fanout): 2·|ESS| + coneExcess ≤ length + 1.
- PER-SHARE ACCOUNTING: a cross-cone shared gate serves both cones ⟹ fan-out ≥ 2 (coneExcess ≥ 1)
  while cutting ≤ 1 gate ⟹ savings ≤ coneExcess.

## The dichotomy

- `cross_branch_2x_outside_middle` (PROVED): if coneExcess ≤ cN (low sharing) OR 2·cbudget(F_k) ≤
  2·|ESS| + coneExcess (high coneExcess), then 2·cbudget(F_k) ≤ length + 1 — the full 2×.
  Low: savings ≤ coneExcess ≤ cN ⟹ disjoint-deficit gives 2cbudget ≤ length. High: ledger alone.
  Adversary squeezed at BOTH ends.
- `cross_branch_gap_is_middle` (PROVED): if 2× FAILS (length+1 < 2cbudget), then cN < coneExcess AND
  2|ESS| + coneExcess < 2cbudget. The entire open content is confined to that band.

## Remaining open set = the middle regime

2× open ONLY for cN < coneExcess < 2·cbudget(F_k) − 2|ESS| (MODERATE sharing, savings ≈ coneExcess,
trade length for coneExcess toward 1×).  Closing = ruling out this band = proving the per-share
accounting is strictly better there: each cross-cone share adds ≥ 2 coneExcess (savings ≤
coneExcess/2), which for the expander mixer would follow if a share helping both sides must
reconstruct Ω(1) fresh boundary crossings PER SIDE.  That per-share ≥2 bound is the residual — NOT
proved.

Localizes the cross-branch to one bounded regime + names the exact per-share inequality that finishes
it.  Does NOT close it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# CORRECTION: the per-share RATIO bound does NOT close the cross-branch; the ABSOLUTE bound does

Pressure-tested the proposed finishing target ramanujan_share_gate_double_charge (savings ≤
coneExcess/2). Result: a constant per-share RATIO bound provably does NOT close the middle regime.
Frozen in Lean (`ComputationalDepthNFrameShareChargeBound.lean`).

- `half_charge_does_not_close` (PROVED): witness (150,100,102,0,51,1) satisfies disjoint-deficit
  (2cbudget+cN ≤ length+savings), ledger (2ess+coneExcess ≤ length+1), AND per-share ≥2
  (2·savings ≤ coneExcess), YET length+1 < 2cbudget (2× FAILS). So savings ≤ coneExcess/2 is
  insufficient.
- `ratio_band_survives` (PROVED): for ANY constant c ≥ 1, witness (4c,2c+1,3c,0,3,1) satisfies all
  three inputs with c·savings ≤ coneExcess yet 2× fails. A constant ratio only shifts the low edge
  to coneExcess ≤ c·cN; the band c·cN < coneExcess < 2cbudget−2ess survives for large cbudget.
- `absolute_savings_bound_closes` (PROVED): savings ≤ cN ⟹ 2cbudget ≤ length (full 2×, no case
  split, disjoint-deficit alone).

## The corrected finishing target

Not a per-share ratio. The ABSOLUTE bound: total cross-cone sharing saving ≤ cN (the sibling reuse
cannot save more length than the mixer's fresh cN coupling capacity). Intuition: disjoint inputs ⟹
the only shared structure is F_k itself, and reuse must route through the mixer's cN-dimensional
coupling. That absolute bound IS the cross-branch direct sum in sharpest form = KRW-hard content,
NOT proved. Correction: aim at savings ≤ cN (a routing-capacity statement about the mixer), not per-
gate fan-out. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# CORRECTION: mixer fresh charge is Θ(N), not Θ(N/d²) — Q1 answered, fork collapses

The "fresh ≈ N/d² may be too small" tension was a factor-d miscalculation of the induced-matching
size. Corrected chain (ComputationalDepthNFrameFreshLinear.lean):
- Edge expansion: crossingEdges ≥ d·N/4 (a CONSTANT FRACTION of all d·N/2 edges — the d was dropped
  in the N/d² estimate).
- Greedy induced matching removes ≤ 2d² crossing edges per matched edge ⟹ crossingEdges ≤ 2d²·matching.
- `fresh_cut_rank_linear` (PROVED): d·N ≤ 4·crossingEdges ∧ crossingEdges ≤ 2·d·d·matching ⟹
  N ≤ 8·d·matching, i.e. matching ≥ N/(8d). For constant d, fresh cut-rank = Θ(N), c = 1/(8d).

## What this settles

Q1 (fresh Θ(N) with c~1?) = YES, already, by the ordinary Ramanujan mixer at constant d. The
three-way fork collapses: increase-fresh already done; stack-deficits (all-middle is self-consistent,
linear cbudget) = the direct sum. ONLY remaining question: bound savings ≤ cN = the cross-branch
direct sum / info-vs-size gap. Fresh Θ(N) is NECESSARY but NOT SUFFICIENT — savings is decoupled
(sharing happens BELOW the mixer, on disjoint inputs, can exceed cN via a hard-low-info share). Fixes
the record + reduces the fork to one question; does NOT close the direct sum. Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

# REPAIR: cone-intersection deficit fixes the mixer double-counting

The two-sided-restriction attack double-counted the mixer (under x_R=const a mixer gate becomes a
single-var fn of F_k(x_L), so it's active, can't be excluded). Repair via CONES not restriction:
F_k(x_L) is the mixer's INPUT, computed BELOW the mixer, so cone(F_k(x_L)) excludes the mixer by
construction. Frozen in Lean (`ComputationalDepthNFrameConeIntersection.lean`).

- `cone_intersection_deficit` (PROVED): coneL,coneR ≥ cbudget(F_k) (firewall), coneUnion + mixer ≤
  total (cones disjoint from mixer), coneL+coneR = coneUnion+coneInter (incl-excl) ⟹
  2·cbudget(F_k) + mixer ≤ total + coneInter, i.e. total ≥ 2·cbudget + mixer − coneInter. Mixer now on
  the + (fresh) side; deficit = EXACTLY coneInter (gates in BOTH cones).
- `direct_sum_from_cone_inter_le_mixer` (PROVED): coneInter ≤ mixer ⟹ 2·cbudget(F_k) ≤ total (full 2×).

## What this repairs

Plain restriction gave total ≥ 2cbudget − cross (mixer SUBTRACTED, wrong side). Cone argument gives
total ≥ 2cbudget + mixer − coneInter (mixer ADDED, correct side) — a genuine +2·mixer correction. The
deficit is now the CONE INTERSECTION (gates feeding BOTH F_k computations), not all cross-gates —
exactly the boundary-neutral cancellation shares; the mixer's Ω(cN) boundary-carrying gates correctly
excluded (they're above the cones). Direct sum closes iff coneInter ≤ mixer (= cN): gates feeding both
sub-computations ≤ mixer fresh count. That residual (coneInter ≤ cN) is the cross-branch direct sum in
cleanest combinatorial form (a cone-intersection count, NO info-vs-size gap), NOT proved. Genuine
accounting repair isolating the deficit correctly; does NOT close the direct sum. Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.

---

## CAPSTONE REDUCTION: cross-branch direct sum ≡ explicit rigid additive mixer

`ComputationalDepthNFrameRigidAdditiveMixer.lean` (clean, `[propext, Quot.sound]`, 5 theorems). This
closes the horizontal arc by reducing the single open inequality to ONE named algebraic object, both
ways. It does NOT prove the inequality — it states precisely the brick that would.

### The chain (each link's home)

`F_{k+1}(x) = Mix_G(F_k(x_L), F_k(x_R))`, disjoint blocks. `T k = CE(F_k)`; `fresh k` = mixer's gross
forced cone-excess; `CE_share k` = cross-copy sharing (gates on BOTH blocks below the mixer); `ρ, ρ₂` =
mixer's incompressible rank for one / two copies.

1. **DEFICIT** (frozen, `NFrameCrossBranch.single_scale_recurrence_deficit`): the gap from the ideal
   `2×` recurrence is EXACTLY the sharing — `2·T k + fresh k ≤ T(k+1) + CE_share k`.
2. **BRIDGE** (new, `rank_additivity_bounds_share`): cross-copy sharing ≤ rank non-additivity deficit
   `2ρ − ρ₂`; so `ρ` additive up to the fresh slack ⟹ `CE_share + amp ≤ fresh`. This is the one new
   link — it converts "bound `CE_share`" into "the mixer's incompressible rank is direct-sum additive".
3. **AMPLIFY** (frozen, `NFrameConeAmplify.amplify_exceeds_linear`): per-level `2·T k + c·2^{k+1} ≤
   T(k+1)` unrolls to `T b ≥ b·2^b` — super-linear.

- **SUFFICIENCY (proved), `additive_mixer_forces_superlinear`**: DEFICIT + rank-additivity ⟹
  `b·2^b ≤ T b` for all `b`. An additive mixer closes the direct sum at every scale; the tower is
  super-linear.
- **NECESSITY (proved witness), `non_additive_mixer_breaks_cross_branch`**: with the deficit holding and
  the rank deficit exceeding the fresh slack (mixer NON-additive), the sharing exceeds the fresh and the
  doubling fails. Additivity is tight, not merely sufficient — a genuine iff at the accounting level.

### The dilemma the brick must break (rigidity ⊥ the clean additivity criterion)

The only clean PROVABLE additivity criterion allowing high rank is `R(T) = fr(T)` (tensor rank = a
flattening/matrix rank; flattening rank is additive under direct sum). But `R = fr` forces
mode-splitting = DECOUPLING, while the fresh charge needs COUPLING = a rigid gap `R − fr ≥ fresh`.

- **`flattening_additivity_incompatible_with_coupling` (proved)**: `fr + fresh ≤ R` (rigidity) and
  `R ≤ fr` (the `R=fr` criterion) with `fresh ≥ 1` ⟹ `False`. The clean flattening route to additivity
  cannot coexist with the coupling. This refutes THAT route — it does NOT prove no additive coupled
  mixer exists (Shitov's non-additivity counterexamples are non-explicit / asymptotic, so a bespoke
  rigid-additive family is not ruled out; it is the corner the positive additivity theory cannot reach).

### Honest scope

Reduction complete and machine-checked BOTH ways: an explicit mixer with rigid, direct-sum-additive
incompressible rank ⟹ cross-branch direct sum ⟹ `Θ(N log N)` cone-excess (sufficiency); a non-additive
mixer ⟹ breaks it (necessity). NOT proved, = the entire open content: the EXISTENCE of such a mixer.
Rigidity alone is an open explicit lower bound (implies arithmetic circuit LBs); additivity in the rigid
regime is Shitov's zone; the clean flattening criterion is coupling-incompatible. So the cross-branch
direct sum is now converted into the well-posed algebra target — **construct an explicit tensor that is
both rigid (`R − fr ≥ fresh`) and provably rank-additive under iterated direct sums** — with the barrier
named on both horns (explicit tensor rigidity ∧ Strassen additivity). Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.

---

## HYBRID MIXER via the SUBSTITUTION METHOD — reduced to substitution tightness

`ComputationalDepthNFrameHybridSubstitution.lean` (clean `[propext, Quot.sound]`, no sorry). The
candidate triage killed 4 families; the block-coupled hybrid (additive-certified local blocks + expander
coupling) is the sole survivor. This file resolves what it needs by routing the mixer's rank through the
SUBSTITUTION METHOD.

### Why substitution is the right tool
`MixerTargetSpec` asks for rank BOTH rigid (`R − fr ≥ fresh`) AND additive (`R2 ≥ 2R − fresh`). The
substitution method (Pan, Hopcroft–Kerr, Bläser; Bürgisser–Clausen–Shokrollahi) is the unique general
tensor-rank lower-bound tool that is DIRECT-SUM ADDITIVE by construction ("preserves direct sum"), so
`LB(T^{⊕m}) ≥ m·LB(T)`. Hence `R2 ≥ 2·LB` for free — additivity is supplied by the PROOF TECHNIQUE, not
a fragile tensor property. That is why the hybrid is not dead where the others are.

### The reduction (LB = substitution bound, R = true rank, fr = flattening)
- RIGIDITY needs `fr + fresh ≤ LB` (substitution beats flattening — Bläser-type bounds do).
- ADDITIVITY needs `2R ≤ R2 + fresh`; with `R2 ≥ 2LB` this holds iff the RESIDUAL `R − LB ≤ fresh/2`
  (substitution NEARLY TIGHT).

The residual `R − LB` is the crux, both: (a) the only place non-additivity can hide (substitution-certified
rank is additive, so sharing lives in what substitution misses); (b) un-certifiable as additive by the one
additive tool. So `additivity ⟺ substitution tightness on the mixer` (up to `fresh/2`). Literature is
explicit that substitution is NOT tight in general (Landsberg–Teitler; real-tensor bounds). Whether an
explicit EXPANDER tensor admits a bound both STRONG (`LB − fr ≥ fresh`) and NEARLY TIGHT (`R − LB ≤ fresh/2`)
is the open sub-question — NOT settled either way.

### Theorems
- `substitution_gives_spec_fields` (proved): strong + valid + additive-subst + near-tight ⟹ spec rigidity
  and additivity.
- `specFromSubstitution` (builder): such a family instantiates `MixerTargetSpec`.
- `hybrid_forces_superlinear` (proved): substitution family + frozen deficit + bridge ⟹ `b·2^b ≤ T b`.
- `substitution_tightness_necessary` (witness): strong + additive-subst but NOT tight ⟹ additivity FAILS.
  Tightness is the crux, not optional.

### Verdict
Does NOT construct a mixer. Reduces the hybrid — the last live candidate — to ONE named property:
substitution near-tightness on an explicit strong-bound expander tensor. Genuine refinement of "find an
additive tensor" (now: "find a substitution-tight strong expander tensor"), with the residual `R − LB`
named as the sole home of non-additivity. Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
