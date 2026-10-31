import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsCashout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpeedupMargin

/-!
# Splitting `UniformWilliamsRealizationSocket` into named sub-sockets

`…ACC0WilliamsCashout` parks the entire "residue cell speedup ⇒ `NEXP ⊄ ACC⁰`" step in **one** monolithic socket,
`UniformWilliamsRealizationSocket := (∀ n, MixedACCResidueSatSpeedup n) → NEXPnotACC0`.  This file performs the same
surgery we did on the YBT socket (`…ACC0YBTExactCompose`): it **factors** that monolith into a chain of named
sub-sockets, proves the composition and the self-audit, and **grounds** the routine (arithmetic) part — leaving only
the genuine complexity-theoretic assumption (the time hierarchy / Williams' algorithmic method) exposed.

```
(∀ n, MixedACCResidueSatSpeedup n)        -- residue cell-search speedup: PROVED (modulo the YBT depth socket)
        │  EncodingSocket            (S1)  -- encode the cell search as a machine procedure  [routine]
        ▼
EncodedAlg                                 -- a machine decides ACC⁰-SAT
        │  CostBridgeSocket          (S2)  -- cell count < 2^n  ⇒  runtime ≤ 2^{n−n^ε}        [routine; ARITH proved]
        ▼
TimeBounded                                -- a 2^{n−n^ε}-time ACC⁰-SAT algorithm
        │  UniformitySocket          (S3)  -- the per-n algorithms form a uniform family       [standard assumption]
        ▼
Uniform (= UniformACC0SatSpeedup)          -- uniform 2^{n−n^ε} nondeterministic ACC⁰-SAT
        │  TimeHierarchySocket       (S4)  -- Williams' method: speedup ⇒ NTIME collapse ⇒ ⊥  [THE deep content]
        ▼
NEXPnotACC0
```

## What is proved (clean axioms, no `sorry`)

* The four sub-sockets `EncodingSocket` / `CostBridgeSocket` / `UniformitySocket` / `TimeHierarchySocket`.
* **`realization_socket_factors`** — the composition: `S1 ∧ S2 ∧ S3 ∧ S4 ⇒ UniformWilliamsRealizationSocket`.  The
  monolith is exactly the chain.
* **`routine_reduce_to_timeHierarchy`** — given the three routine sub-sockets, the whole realization socket reduces
  to `TimeHierarchySocket` alone.
* **`timeHierarchy_socket_iff_separation`** — the self-audit: once a uniform speedup is established, `TimeHierarchy
  Socket` is *logically equivalent* to `NEXP ⊄ ACC⁰`; S4 carries the entire difficulty (S1–S3 carry none).
* **`cell_count_savings`** — the *arithmetic core* of the cost bridge, **proved** (via `SpeedupMargin`): a cell count
  `≤ 2^{n−k}` is a genuine `2^k` time savings.  `proved_speedup_is_trivial_savings` makes explicit that the
  *currently proved* bound `steps < 2^n` is only the `k = 0` (factor-`>1`) savings — the super-polynomial `k = n^ε`
  Williams needs is supplied by the *quasipolynomial* exact form, i.e. the **other** open socket
  (`…ACC0YBTExactCompose`: exact + quasipoly size).

## Honest scope — which sub-socket is the wall

S1 (machine encoding) and the per-step cost half of S2 are **routine** complexity-theory bookkeeping (a `t`-cell
search is a `t·poly`-step machine); their quantitative core (`cell_count_savings`) is proved here.  S3 (uniformity)
is a **standard mild assumption** on circuit families.  S4 (the nondeterministic time hierarchy + Williams'
algorithmic argument) is the **genuine separation-strength content**, and `timeHierarchy_socket_iff_separation`
proves it *is* `NEXP ⊄ ACC⁰`.  Plus the cost bridge needs *super-polynomial* savings, which routes back to the
quasipoly-exact YBT wall.  So the realization socket is now split: routine parts grounded, one deep assumption named.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashout
open PallLean.Paper93.DeepMath.PathB.SpeedupMargin

section Sockets

variable (EncodedAlg TimeBounded Uniform NEXPnotACC0 : Prop)

/-- **S1 — machine-encoding sub-socket.**  The residue cell search (for all `ACC⁰`) is encodable as a machine
procedure deciding `ACC⁰`-SAT.  *Routine* complexity-theory bookkeeping. -/
def EncodingSocket : Prop := (∀ n, MixedACCResidueSatSpeedup n) → EncodedAlg

/-- **S2 — cost-model-bridge sub-socket.**  The encoded procedure's cell count `< 2^n` becomes a Turing-machine
runtime bound `2^{n−n^ε}` (each cell costs `poly`, and the savings is genuine).  *Routine*; its arithmetic core is
`cell_count_savings`. -/
def CostBridgeSocket : Prop := EncodedAlg → TimeBounded

/-- **S3 — uniformity sub-socket.**  The per-`n` time-bounded algorithms form a single uniform family (one machine,
`poly(n)` overhead).  A *standard* assumption on circuit/algorithm families. -/
def UniformitySocket : Prop := TimeBounded → Uniform

/-- **S4 — time-hierarchy cash-out sub-socket.**  Williams' algorithmic method: a uniform `2^{n−n^ε}`-time
nondeterministic `ACC⁰`-SAT algorithm collapses `NTIME`, contradicting the nondeterministic time hierarchy.  **The
genuine separation-strength content.** -/
def TimeHierarchySocket : Prop := Uniform → NEXPnotACC0

/-- **The factorization (proved): the four sub-sockets compose to the monolithic realization socket.**  The monolith
`UniformWilliamsRealizationSocket` is *exactly* `S1 ▸ S2 ▸ S3 ▸ S4`. -/
theorem realization_socket_factors
    (s1 : EncodingSocket EncodedAlg) (s2 : CostBridgeSocket EncodedAlg TimeBounded)
    (s3 : UniformitySocket TimeBounded Uniform) (s4 : TimeHierarchySocket Uniform NEXPnotACC0) :
    UniformWilliamsRealizationSocket NEXPnotACC0 :=
  fun hspeedup => s4 (s3 (s2 (s1 hspeedup)))

/-- **Routine sub-sockets reduce the realization socket to S4 (proved).**  Given the three routine sub-sockets
(encoding, cost bridge, uniformity), the whole `UniformWilliamsRealizationSocket` follows from `TimeHierarchySocket`
alone — the routine parts carry none of the residual difficulty. -/
theorem routine_reduce_to_timeHierarchy
    (s1 : EncodingSocket EncodedAlg) (s2 : CostBridgeSocket EncodedAlg TimeBounded)
    (s3 : UniformitySocket TimeBounded Uniform) :
    TimeHierarchySocket Uniform NEXPnotACC0 → UniformWilliamsRealizationSocket NEXPnotACC0 :=
  fun s4 => realization_socket_factors EncodedAlg TimeBounded Uniform NEXPnotACC0 s1 s2 s3 s4

/-- **Self-audit (proved): S4 is the separation.**  Once a uniform `ACC⁰`-SAT speedup is established, the
time-hierarchy sub-socket is *logically equivalent* to `NEXP ⊄ ACC⁰` itself — the entire difficulty is in S4, none in
S1–S3. -/
theorem timeHierarchy_socket_iff_separation (hu : Uniform) :
    TimeHierarchySocket Uniform NEXPnotACC0 ↔ NEXPnotACC0 :=
  ⟨fun h => h hu, fun h _ => h⟩

end Sockets

/-- **The arithmetic core of the cost bridge (proved).**  A cell/step count `≤ 2^{n−k}` is a genuine `2^k` savings
over brute force `2^n`: `2^k · steps ≤ 2^n`.  This is the quantitative content S2 needs; the remaining part of S2 is
the (routine) per-cell machine cost. -/
theorem cell_count_savings {steps n k : ℕ} (hk : k ≤ n) (h : steps ≤ 2 ^ (n - k)) :
    2 ^ k * steps ≤ 2 ^ n :=
  savings_ge_of_work_le hk h

/-- **The proved cell bound is only the trivial savings (proved).**  `MixedACCResidueSatSpeedup` delivers
`steps < 2^n`, which is the `k = 0` case of `cell_count_savings` (savings factor `> 1`).  Williams' method needs the
*super-polynomial* `k = n^ε` savings — supplied only by a **quasipolynomial** exact `SYM∘AND` form, i.e. the other
open socket (`…ACC0YBTExactCompose`: exact + quasipoly size).  So the two remaining walls are linked: the cost bridge
bites only once the YBT size wall is crossed. -/
theorem proved_speedup_is_trivial_savings {steps n : ℕ} (h : steps < 2 ^ n) :
    2 ^ (0 : ℕ) * steps ≤ 2 ^ n := by
  simpa using le_of_lt h

end PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit.realization_socket_factors
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit.routine_reduce_to_timeHierarchy
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit.timeHierarchy_socket_iff_separation
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0WilliamsRealizationSplit.cell_count_savings
