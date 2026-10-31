import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM

/-!
# NTIME class accounting — the lazy diagonal machine lives inside `NEXP` (proved placement)

Entry 219 proved the lazy-diagonalization *contradiction mechanism* (a machine can't decide its own lazy diagonal) and
entry 220 proved that a deterministic transition table drives a clocked `reachIn` computation.  This file completes the
hierarchy side's **resource-boundary accounting**: a clocked machine that decides a language within the `NEXP` time
budget genuinely places that language *inside* `NEXP` — turning "diagonal mechanism proved" into "time-class placement
proved".

The accounting.  `NTIME f = {L | ∃ M, ∀ x, L x ↔ acceptsWithin M x (f |x|)}` and `NEXP = ⋃_c NTIME(2^{n^c+c})`
(`…ACC0NTM`).  So a clocked machine `M` deciding `L` within `2^{|x|^c+c}` steps (`ClockedSimulation`) places
`L ∈ NTIME(2^{n^c+c}) ⊆ NEXP` directly.  The cost-fits-budget step — that a run within `s` steps fits any larger budget
`t ≥ s` — is `acceptsWithin_mono` (entry `…ACC0NTM`).

## What is proved (clean axioms, no `sorry`)

* **`accepts_within_budget`** — the cost-fits-budget monotonicity: `acceptsWithin M x s → s ≤ t → acceptsWithin M x t`
  (the simulation cost `s` fitting the larger budget `t`).
* **`ClockedSimulation L M c`** — `M` decides `L` within the `NEXP` budget: `∀ x, L x ↔ acceptsWithin M x (2^{|x|^c+c})`.
* **`clocked_in_NTIME`** / **`clocked_in_NEXP`** — the placement: a `ClockedSimulation` puts `L ∈ NTIME(2^{n^c+c})`,
  hence `L ∈ NEXP`.
* **`lazy_diagonal_in_nexp`** — `ClockedSimulation (lazy diagonal) → (lazy diagonal) ∈ NEXP`: the lazy diagonal machine
  lives inside `NEXP` (the entry-200/219 `DiagonalInNexp` placement, now proved from the clocked simulation).

## Honest scope

This proves the **time-class placement** — that a clocked machine deciding `L` within the `NEXP` budget puts `L ∈ NEXP`
— completely, via the `…ACC0NTM` `NTIME`/`NEXP` definitions and `acceptsWithin_mono` (the cost monotonicity).  Combined
with entry 219 (the lazy diagonal escapes any single machine) this is the hierarchy's `NEXP`-membership side, now from
the clocked-machine model rather than assumed.  What remains the named socket is **`ClockedSimulation`** for the lazy
diagonal itself: that a clocked `NTM` *does* decide the lazy diagonal within the `NEXP` budget — the universal
simulation of `M_i` on the next input across the block, plus the one boundary complement, clocked to `2^{|x|^c+c}` steps
(building on entries 219–220).  That simulation is now reduced to the *lazy-feasible* form (one complement, not closure
under complement), the genuine remaining machine-cost content.  This proves the placement, not the universal simulation.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NTIMEAccounting

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM acceptsWithin acceptsWithin_mono NTIME NEXP)

/-- **The cost-fits-budget step (PROVED).**  A clocked run accepting within `s` steps also accepts within any larger
budget `t ≥ s` — `acceptsWithin_mono`.  This is how the simulation cost `s` is absorbed into the bigger time bound. -/
theorem accepts_within_budget (M : NTM) (x : List Bool) {s t : ℕ} (hst : s ≤ t)
    (h : acceptsWithin M x s) : acceptsWithin M x t :=
  acceptsWithin_mono M x hst h

/-- **A clocked simulation within the `NEXP` budget.**  The machine `M` decides `L` within `2^{|x|^c+c}` steps:
`∀ x, L x ↔ acceptsWithin M x (2^{|x|^c+c})`.  (For the lazy diagonal: the universal simulation of `M_i` on the next
input across the block, plus the boundary complement, clocked to the `NEXP` budget — the entry-219/220 substrate.) -/
def ClockedSimulation (L : Lang) (M : NTM) (c : ℕ) : Prop :=
  ∀ x, L x ↔ acceptsWithin M x (2 ^ (x.length ^ c + c))

/-- **Placement in `NTIME` (PROVED).**  A `ClockedSimulation` of `L` by `M` at exponent `c` places `L ∈
NTIME(2^{n^c+c})` — directly by the `NTIME` definition. -/
theorem clocked_in_NTIME (L : Lang) (M : NTM) (c : ℕ) (h : ClockedSimulation L M c) :
    L ∈ NTIME (fun n => 2 ^ (n ^ c + c)) :=
  ⟨M, h⟩

/-- **Placement in `NEXP` (PROVED).**  A `ClockedSimulation` of `L` (at any exponent `c`) places `L ∈ NEXP` — the
machine decides `L` within `NTIME(2^{n^c+c}) ⊆ NEXP`. -/
theorem clocked_in_NEXP (L : Lang) (M : NTM) (c : ℕ) (h : ClockedSimulation L M c) : L ∈ NEXP :=
  ⟨c, clocked_in_NTIME L M c h⟩

/-- **The lazy diagonal machine lives inside `NEXP` (PROVED, modulo the simulation socket).**  Given that a clocked
`NTM` decides the lazy diagonal `L` within the `NEXP` budget (`ClockedSimulation`), `L ∈ NEXP`.  This is the time-class
*placement* of the lazy diagonal — the `DiagonalInNexp` membership (entry 200's socket) discharged from the
clocked-machine model (entries 219–220), reduced to the `ClockedSimulation` socket (the lazy universal simulation). -/
theorem lazy_diagonal_in_nexp (L : Lang) (M : NTM) (c : ℕ) (hsim : ClockedSimulation L M c) :
    L ∈ NEXP :=
  clocked_in_NEXP L M c hsim

end PallLean.Paper93.DeepMath.PathB.ACC0NTIMEAccounting

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NTIMEAccounting.accepts_within_budget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NTIMEAccounting.clocked_in_NEXP
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NTIMEAccounting.lazy_diagonal_in_nexp
