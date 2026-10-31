import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RoutingMachineComposition

/-!
# Entry 330 — routing-machine wiring: state-offset preserves computation (proved)

Entry 329 proved that a sub-machine's run survives embedding its transition table in a larger one (`M ⊆ M'`).  But to
combine two phases into one routing table they must occupy **disjoint state ranges** — otherwise their rules collide.
This file proves the missing piece: **offsetting a machine's states by a constant `s` preserves its entire
computation**.  So phase 2 can be placed on states `[s, …)` (the `shiftMachine`), its verified run carried over verbatim
(on shifted configurations), and then embedded in the combined table `M₁ ++ shiftMachine s M₂` by entry-329
monotonicity.

**The offset.**  `shiftConfig s (state, head, tape) = (state + s, head, tape)`; `shiftTrans s` adds `s` to a rule's read-
and write-states; `shiftMachine s M = M.map (shiftTrans s)`.  Since `readSym`, `moveHead`, `writeAt` touch only the head
and tape (never the state), the step relation is preserved verbatim up to the state offset.

## What is proved (clean axioms, no `sorry`)

* **`shiftConfig`, `shiftTrans`, `shiftMachine`** — the state-offset on configs, rules, and tables.
* **`readSym_shiftConfig`** (PROVED) — `readSym (shiftConfig s c) = readSym c` (the read ignores the state).
* **`applyTrans_shiftTrans`** (PROVED) — `applyTrans (shiftConfig s c) (shiftTrans s t) = shiftConfig s (applyTrans c t)`
  (a step commutes with the offset).
* **`concreteStep_shift`** (PROVED) — a step of `M` becomes a step of `shiftMachine s M` between shifted configs.
* **`reachIn_shift`** (PROVED) — a whole `k`-step run is preserved under the offset.
* **`reachIn_in_combined`** (PROVED) — `M₂`'s run, offset by `s`, holds in the combined table `M₁ ++ shiftMachine s M₂`
  (via entry-329 monotonicity): phase 2 placed on disjoint states keeps its run inside the routing table.

## Honest scope

This proves the **state-disjoint embedding** for the routing table: a phase placed on offset states `[s, …)` keeps its
verified computation inside the combined table `M₁ ++ shiftMachine s M₂` (`reachIn_in_combined`).  With entry 329
(sub-table monotonicity) this is the assembly of *parallel* sub-tables on disjoint states.  What it does **not** yet do
is the **control-flow handoff** — redirecting phase 1's exit state to `s` (phase 2's shifted start) so the combined
machine *sequences* the phases — nor the **`f`-timing**.  Those, plus instantiating the phases with the actual
universal simulator (296–298) and bounded complement (299), are the remaining low-level engineering, **not built here
and not faked**.  This is the second verified brick of the routing-machine build (after entry 329).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineWiring

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig toNTM concreteStep readSym applyTrans)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)

/-- **State-offset on a configuration**: add `s` to the state, leaving head and tape untouched. -/
def shiftConfig (s : ℕ) (c : CConfig) : CConfig := (c.1 + s, c.2.1, c.2.2)

/-- **State-offset on a transition rule**: add `s` to both the read-state and the write-state (head-move and symbols
untouched). -/
def shiftTrans (s : ℕ) (t : TMTrans) : TMTrans :=
  ((t.1.1 + s, t.1.2), (t.2.1 + s, t.2.2.1, t.2.2.2))

/-- **State-offset on a machine**: offset every rule's states. -/
def shiftMachine (s : ℕ) (M : TMachine) : TMachine := M.map (shiftTrans s)

/-- **The read ignores the state offset (PROVED).** -/
theorem readSym_shiftConfig (s : ℕ) (c : CConfig) :
    readSym (shiftConfig s c) = readSym c := rfl

/-- **A step commutes with the state offset (PROVED).**  Applying the shifted rule to the shifted config gives the
shifted result — heads/tapes are untouched, states move by `s`. -/
theorem applyTrans_shiftTrans (s : ℕ) (c : CConfig) (t : TMTrans) :
    applyTrans (shiftConfig s c) (shiftTrans s t) = shiftConfig s (applyTrans c t) := rfl

/-- **A step survives the offset (PROVED).**  A step of `M` from `c` to `d` is a step of `shiftMachine s M` from
`shiftConfig s c` to `shiftConfig s d`. -/
theorem concreteStep_shift (s : ℕ) {M : TMachine} {c d : CConfig}
    (hs : concreteStep M c d) : concreteStep (shiftMachine s M) (shiftConfig s c) (shiftConfig s d) := by
  obtain ⟨t, ht, h1, h2⟩ := hs
  refine ⟨shiftTrans s t, List.mem_map.mpr ⟨t, ht, rfl⟩, ?_, ?_⟩
  · rw [readSym_shiftConfig]
    show (t.1.1 + s, t.1.2) = (c.1 + s, readSym c)
    rw [congrArg Prod.fst h1, congrArg Prod.snd h1]
  · rw [applyTrans_shiftTrans, h2]

/-- **A whole run survives the offset (PROVED).**  Every `k`-step run of `toNTM M` is a `k`-step run of
`toNTM (shiftMachine s M)` between the shifted configs. -/
theorem reachIn_shift (s : ℕ) {M : TMachine} :
    ∀ (k : ℕ) (c d : CConfig), reachIn (toNTM M) k c d →
      reachIn (toNTM (shiftMachine s M)) k (shiftConfig s c) (shiftConfig s d) := by
  intro k
  induction k with
  | zero => intro c d hr; exact congrArg (shiftConfig s) hr
  | succ k ih =>
      intro c d hr
      obtain ⟨e, hstep, hrest⟩ := hr
      exact ⟨shiftConfig s e, concreteStep_shift s hstep, ih e d hrest⟩

/-- **Phase 2 placed on disjoint states keeps its run in the combined table (PROVED).**  `M₂`'s run, offset by `s`,
holds in the combined routing table `M₁ ++ shiftMachine s M₂` — `reachIn_shift` puts it in `shiftMachine s M₂`, then
entry-329 monotonicity (`List.subset_append_right`) lifts it to the union. -/
theorem reachIn_in_combined (s : ℕ) (M₁ M₂ : TMachine) (k : ℕ) (c d : CConfig)
    (hr : reachIn (toNTM M₂) k c d) :
    reachIn (toNTM (M₁ ++ shiftMachine s M₂)) k (shiftConfig s c) (shiftConfig s d) :=
  ACC0RoutingMachineComposition.reachIn_mono (List.subset_append_right M₁ (shiftMachine s M₂))
    k _ _ (reachIn_shift s k c d hr)

/-!
**State-disjoint embedding, proved.**  Offsetting a machine's states preserves its read (`readSym_shiftConfig`), its
step (`applyTrans_shiftTrans`, `concreteStep_shift`), and its whole run (`reachIn_shift`); so a phase placed on states
`[s, …)` keeps its verified computation inside the combined routing table `M₁ ++ shiftMachine s M₂`
(`reachIn_in_combined`).  With entry 329 this assembles parallel sub-tables on disjoint states.  Remaining for the full
routing machine: the control-flow handoff (redirect phase 1's exit to phase 2's shifted start) and the `f`-timing,
instantiated with the universal simulator (296–298) and bounded complement (299) — the remaining low-level engineering,
not faked.  Second verified brick.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineWiring

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineWiring.readSym_shiftConfig
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineWiring.applyTrans_shiftTrans
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineWiring.concreteStep_shift
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineWiring.reachIn_shift
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineWiring.reachIn_in_combined
