import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsRealizationSplit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0YBTSocketStrength

/-!
# Probing the realization socket — it adds no new separation-strength obstacle; the route has ONE deep gate

Entry 292 showed the YBT socket is not separation-strength (existence proved; quasipoly size = true Beigel–Tarui).
This file probes the *realization* socket (Williams link 2).  It was already split into S1–S4
(`…ACC0WilliamsRealizationSplit`); the probe completes the picture and proves the one link that was only *gestured at*.

**The realization socket factors (recalled, proved there):**

```
S1 EncodingSocket      [routine]      S2 CostBridgeSocket   [routine; arith proved: cell_count_savings]
S3 UniformitySocket    [standard]     S4 TimeHierarchySocket [separation-strength; ↔ NEXP⊄ACC⁰ self-audited]
```

**The missing link, now proved.**  `proved_speedup_is_trivial_savings` noted the *currently proved* cell bound
(`steps < 2^n`) is only the `k = 0` (factor-`>1`) savings, and that the super-polynomial `k = n^ε` the cost bridge needs
is "supplied by the quasipolynomial exact form" — but that composition was only described.  `cost_bridge_unlocked_by_
quasipoly_ybt` **proves it**: a quasipolynomial cell bound (`cells ≤ (D+1)·n^D + 1`, the content of the YBT *size*
socket) fitting `≤ 2^{n−k}` delivers the genuine `2^k` super-poly savings.  So the realization cost bridge bites
*exactly* when the YBT quasipoly-size wall (entry 292) is crossed — the two routine/true-classical walls compose, with
no new separation-strength content between them.

**The synthesis — one deep gate.**  `williams_route_single_separation_gate`: the realization S4 socket and the
downstream Williams socket are the *same* shape — `(established hypothesis → NEXP⊄ACC⁰)` — and each is `↔ NEXP⊄ACC⁰`
once its antecedent holds.  So across the whole route (YBT + realization + Williams), the **only** separation-strength
content is the single nondeterministic-time-hierarchy / Williams algorithmic gate; everything else is proved,
true-classical (YBT size), or routine (encoding, uniformity).

## What is proved (clean axioms, no `sorry`)

* **`cost_bridge_unlocked_by_quasipoly_ybt`** (PROVED, the missing link) — quasipoly cell bound ⇒ super-poly `2^k`
  savings: the YBT size socket unlocks the realization cost bridge.
* **`realization_separation_strength_is_S4`** (re-export) — the realization socket's sole separation-strength piece is
  S4, `↔ NEXP⊄ACC⁰`.
* **`williams_route_single_separation_gate`** (PROVED) — S4 and the Williams socket are the same gate: both
  `↔ NEXP⊄ACC⁰` once their antecedents hold.
* **`williams_route_socket_classification`** (PROVED bundle) — the full-route map: YBT form exists unconditionally
  (292); the cost bridge is unlocked by quasipoly YBT size; the realization socket reduces to S4; S4 and Williams are
  each `↔` the separation.

## Honest scope

The realization socket adds **no** new separation-strength obstacle: its routine parts are grounded, its cost bridge is
unlocked by the (true-classical) YBT quasipoly size, and its only deep piece S4 is the *same* nondeterministic-time-
hierarchy gate as the Williams socket.  So the entire Williams route has one irreducible separation-strength gate.
This is the anatomy capstone of the algorithmic side; it is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP` — that single gate is
exactly the open content, self-audited as equivalent to the separation.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WilliamsSocketMap

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit

/-- **The missing link, proved: quasipoly YBT size unlocks the realization cost bridge.**  A quasipolynomial cell bound
`cells ≤ (D+1)·n^D + 1` (the content of the YBT *size* socket, entry 292) that fits `≤ 2^{n−k}` delivers the genuine
`2^k` savings the cost bridge S2 needs.  For `D` polylog this is `k = n − polylog = Ω(n)` — the super-polynomial savings
`proved_speedup_is_trivial_savings` only gestured at.  So the realization cost bridge bites *exactly* when the YBT
quasipoly-size wall is crossed; the two non-deep walls compose with no separation-strength content between them. -/
theorem cost_bridge_unlocked_by_quasipoly_ybt {n D k cells : ℕ}
    (hquasipoly : cells ≤ (D + 1) * n ^ D + 1) (hk : k ≤ n)
    (hfit : (D + 1) * n ^ D + 1 ≤ 2 ^ (n - k)) :
    2 ^ k * cells ≤ 2 ^ n :=
  cell_count_savings hk (le_trans hquasipoly hfit)

/-- **The realization socket's sole separation-strength piece is S4 (re-export self-audit).**  Once a uniform
`ACC⁰`-SAT speedup is established, the time-hierarchy sub-socket is *logically equivalent* to `NEXP ⊄ ACC⁰`; S1–S3 carry
none of the difficulty. -/
theorem realization_separation_strength_is_S4 {Uniform NEXPnotACC0 : Prop} (hu : Uniform) :
    TimeHierarchySocket Uniform NEXPnotACC0 ↔ NEXPnotACC0 :=
  timeHierarchy_socket_iff_separation Uniform NEXPnotACC0 hu

/-- **One deep gate (PROVED).**  The realization S4 socket and the downstream Williams socket are the *same* shape —
`(established hypothesis → NEXP⊄ACC⁰)` — and each is `↔ NEXP⊄ACC⁰` once its antecedent holds.  So the route does not
have two separate deep gates; it has one (the nondeterministic-time-hierarchy / Williams algorithmic argument). -/
theorem williams_route_single_separation_gate
    {Uniform UniformACC0SatSpeedup NEXPnotACC0 : Prop} (hu : Uniform) (hu2 : UniformACC0SatSpeedup) :
    (TimeHierarchySocket Uniform NEXPnotACC0 ↔ NEXPnotACC0)
    ∧ ((UniformACC0SatSpeedup → NEXPnotACC0) ↔ NEXPnotACC0) :=
  ⟨timeHierarchy_socket_iff_separation Uniform NEXPnotACC0 hu,
   williams_socket_iff_separation hu2⟩

/-- **The full-route socket classification (PROVED bundle).**  Across YBT + realization + Williams:
(a) the exact `SYM∘AND` form exists *unconditionally* (entry 292, `acc0circuit_hasSymAndForm`);
(b) the YBT socket is a quasipoly *size* bound that **unlocks** the realization cost bridge into super-poly savings
(`cost_bridge_unlocked_by_quasipoly_ybt`);
(c) the realization socket factors so that, given the routine sub-sockets, it reduces to the single time-hierarchy
socket S4 (`routine_reduce_to_timeHierarchy`);
(d) S4 is `↔ NEXP⊄ACC⁰` once a uniform speedup holds (`timeHierarchy_socket_iff_separation`).
So the only separation-strength content of the entire algorithmic route is the one time-hierarchy gate. -/
theorem williams_route_socket_classification
    {n : ℕ} {EncodedAlg TimeBounded Uniform NEXPnotACC0 : Prop} (hu : Uniform)
    (s1 : EncodingSocket EncodedAlg) (s2 : CostBridgeSocket EncodedAlg TimeBounded)
    (s3 : UniformitySocket TimeBounded Uniform) :
    (∀ C : ACC0CircuitModel.ACC0Circuit n,
        ACC0YBTExactCompose.HasSymAndForm (fun x => ACC0CircuitModel.eval C x)
          (ACC0YBTExactCompose.symAndSize C))
    ∧ (∀ {D k cells : ℕ}, cells ≤ (D + 1) * n ^ D + 1 → k ≤ n →
          (D + 1) * n ^ D + 1 ≤ 2 ^ (n - k) → 2 ^ k * cells ≤ 2 ^ n)
    ∧ (TimeHierarchySocket Uniform NEXPnotACC0 → UniformWilliamsRealizationSocket NEXPnotACC0)
    ∧ (TimeHierarchySocket Uniform NEXPnotACC0 ↔ NEXPnotACC0) :=
  ⟨ACC0YBTExactCompose.acc0circuit_hasSymAndForm,
   fun hq hk hfit => cost_bridge_unlocked_by_quasipoly_ybt hq hk hfit,
   routine_reduce_to_timeHierarchy EncodedAlg TimeBounded Uniform NEXPnotACC0 s1 s2 s3,
   timeHierarchy_socket_iff_separation Uniform NEXPnotACC0 hu⟩

/-!
**The probe's result.**  The realization socket adds **no** new separation-strength obstacle.  Its routine parts (S1
encoding, S3 uniformity) are standard; its cost bridge S2 has a proved arithmetic core (`cell_count_savings`) that is
**unlocked** by the quasipoly YBT size (`cost_bridge_unlocked_by_quasipoly_ybt`, the link entry-292's true-classical
size wall feeds); and its only deep piece S4 is the *same* nondeterministic-time-hierarchy gate as the downstream
Williams socket (`williams_route_single_separation_gate`).  So the entire algorithmic route (YBT + realization +
Williams) has **one** irreducible separation-strength gate — the time-hierarchy / Williams algorithmic argument — with
everything else proved, true-classical (YBT size), or routine.  That single gate is `↔ NEXP ⊄ ACC⁰`, the honest open
content.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0WilliamsSocketMap

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsSocketMap.cost_bridge_unlocked_by_quasipoly_ybt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsSocketMap.realization_separation_strength_is_S4
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsSocketMap.williams_route_single_separation_gate
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsSocketMap.williams_route_socket_classification
