import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DerandCollapse

/-!
# Derandomisation ⟹ PRG — the Nisan–Wigderson reconstruction contradiction (proved glue)

Entry 222 left **`DerandGivesPRG`** (`Derandomization → PRGExists`) as a named socket.  This file proves its genuine
logical core — the **Nisan–Wigderson reconstruction contradiction**.  The NW generator (built from a hard function `f`
and a low-intersection design — entries 191–196 of this arc proved the design, hybrid, Yao, and reconstruction pieces)
fools small circuits *because* a distinguisher would reconstruct a small circuit for `f`, contradicting `f`'s hardness.
So "PRG fools" is exactly "no distinguisher", and that follows from reconstruction + hardness by contraposition.

## What is proved (clean axioms, no `sorry`)

* **`NWReconstruction Distinguisher SmallCircuitForHardFn := Distinguisher → SmallCircuitForHardFn`** — the NW
  reconstruction (a distinguisher yields a small circuit for `f`; the entries 191–196 content, abstracted here).
* **`prgFools_of_hard`** (PROVED) — `NWReconstruction D S → ¬ S → ¬ D`: reconstruction plus hardness of `f` (no small
  circuit) gives "no distinguisher", i.e. the PRG fools.  This is `fun d => hard (recon d)` — the reconstruction
  contradiction.
* **`derandGivesPRG_via_nw`** (PROVED) — discharges the entry-222 `DerandGivesPRG` socket: a derandomisation that
  supplies the reconstruction and the hard function (`DerandGivesHardFn`) yields the PRG (`¬ Distinguisher`).

## Honest scope

This proves the **reconstruction contradiction** — that reconstruction (distinguisher ⟹ small circuit for `f`) and
hardness (`f` has no small circuit) compose to "PRG fools" (`prgFools_of_hard`) — and threads it into the entry-222
`DerandGivesPRG` socket.  What remains named sockets are the two genuine inputs: **`NWReconstruction`** (the NW analysis
— hybrid + Yao predict-from-distinguish + reconstruction, the entries 191–196 content at the protocol level) and the
**hard function** supplied by the derandomisation (`DerandGivesHardFn` — the Impagliazzo–Wigderson hardness-to-
randomness tradeoff: a derandomisation hypothesis yields a function hard for small circuits).  This proves the
composition logic, not the NW analysis or the hardness extraction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NWFromHardness

open PallLean.Paper93.DeepMath.PathB.ACC0DerandCollapse (DerandGivesPRG)

/-- **The NW reconstruction socket (entries 191–196).**  A distinguisher for the NW generator yields a small circuit
for the hard function `f` — `Distinguisher → SmallCircuitForHardFn`.  Stated, not proved here (the hybrid + Yao +
reconstruction analysis). -/
def NWReconstruction (Distinguisher SmallCircuitForHardFn : Prop) : Prop :=
  Distinguisher → SmallCircuitForHardFn

/-- **The reconstruction contradiction (PROVED).**  NW reconstruction (`Distinguisher → SmallCircuitForHardFn`) plus
the hardness of `f` (`¬ SmallCircuitForHardFn`) gives "no distinguisher" (`¬ Distinguisher`), i.e. the NW generator is a
PRG: `fun d => hard (recon d)`. -/
theorem prgFools_of_hard (Distinguisher SmallCircuitForHardFn : Prop)
    (recon : NWReconstruction Distinguisher SmallCircuitForHardFn)
    (hard : ¬ SmallCircuitForHardFn) :
    ¬ Distinguisher :=
  fun d => hard (recon d)

/-- **The hardness-extraction socket (Impagliazzo–Wigderson).**  A derandomisation hypothesis yields a function hard for
small circuits, together with the NW reconstruction for it — `Derandomization → (NWReconstruction D S ∧ ¬ S)`.  Stated,
not proved. -/
def DerandGivesHardFn (Derandomization Distinguisher SmallCircuitForHardFn : Prop) : Prop :=
  Derandomization → (NWReconstruction Distinguisher SmallCircuitForHardFn ∧ ¬ SmallCircuitForHardFn)

/-- **Discharges the entry-222 `DerandGivesPRG` socket (PROVED).**  A derandomisation supplying the reconstruction and
the hard function (`DerandGivesHardFn`) gives the PRG `¬ Distinguisher` (the NW generator fools), via the reconstruction
contradiction `prgFools_of_hard`. -/
theorem derandGivesPRG_via_nw (Derandomization Distinguisher SmallCircuitForHardFn : Prop)
    (derand_hard : DerandGivesHardFn Derandomization Distinguisher SmallCircuitForHardFn) :
    DerandGivesPRG Derandomization (¬ Distinguisher) := by
  intro hd
  obtain ⟨recon, hard⟩ := derand_hard hd
  exact prgFools_of_hard Distinguisher SmallCircuitForHardFn recon hard

end PallLean.Paper93.DeepMath.PathB.ACC0NWFromHardness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWFromHardness.prgFools_of_hard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWFromHardness.derandGivesPRG_via_nw
