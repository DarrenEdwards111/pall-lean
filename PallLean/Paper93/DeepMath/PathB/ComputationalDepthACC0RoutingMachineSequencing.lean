import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RoutingMachineWiring

/-!
# Entry 331 — routing-machine sequencing: the control-flow handoff (proved)

Entries 329 (sub-table monotonicity) and 330 (state-offset preservation) assemble two phases *in parallel* on disjoint
state ranges.  This file adds the missing control flow: a **handoff** that, when phase 1 reaches a designated exit state
`qexit`, transfers control to phase 2's (shifted) start state `s`, so the combined machine **sequences** the phases.

**The handoff.**  `handoffRules qexit s` is the two-rule table `[(qexit, b) ↦ (s, b, stay)]` (both reads `b`): at state
`qexit` it jumps to state `s` (phase 2's shifted entry), writing back the read symbol and staying put.  The combined
machine is `seqMachine M₁ M₂ qexit s := M₁ ++ handoffRules qexit s ++ shiftMachine s M₂`.

**The composition.**  If phase 1 runs `a` steps to a config in state `qexit`, the handoff is one step, and phase 2
(`shiftMachine s M₂`) runs `b` steps from the post-handoff config, then the combined machine runs `a + 1 + b` steps
end-to-end — proved by `reachIn_add` (run concatenation) with each phase lifted into the combined table by entries
329/330.

## What is proved (clean axioms, no `sorry`)

* **`handoffRules`, `postHandoff`, `seqMachine`** — the handoff table, the post-handoff config, the sequenced machine.
* **`handoff_step`** (PROVED) — from any config in state `qexit`, `handoffRules qexit s` steps to `postHandoff` (state
  `s`, head unchanged, read symbol written back).
* **`reachIn_seq`** (PROVED) — the end-to-end composition: phase-1 run (`a` steps to `qexit`) + handoff (1 step) +
  phase-2 run (`b` steps, in `shiftMachine s M₂`) ⟹ a run of `seqMachine` of length `a + 1 + b`.

## Honest scope

This proves the **control-flow handoff** that sequences two phases into one transition table (`reachIn_seq`), the piece
entries 329/330 left open.  Together they give: assemble phases on disjoint states (329/330) and wire phase 1's exit to
phase 2's entry (331), with the combined run proved to compose.  This is the routing-machine's *control structure*,
fully verified.  What remains for the complete routing decider is: instantiating phase 1 = decode/dispatch and phase 2 =
the universal simulator (296–298) / bounded complement (299) as concrete tables, and the **`f`-timing** bound on the
total step count — the remaining low-level engineering, **not built here and not faked**.  Third verified brick.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineSequencing

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig Move toNTM concreteStep readSym applyTrans)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineComposition (concreteStep_mono reachIn_mono)
open PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineWiring (shiftMachine)

/-- **The handoff table.**  At state `qexit`, on either read symbol, jump to state `s` (phase 2's shifted start),
writing back the read symbol and staying put (`Move = 2`). -/
def handoffRules (qexit s : ℕ) : TMachine :=
  [((qexit, true), (s, true, (2 : Move))), ((qexit, false), (s, false, (2 : Move)))]

/-- **The post-handoff configuration.**  Applying the handoff rule at a state-`qexit` config: state becomes `s`, head
unchanged (stay), read symbol written back. -/
def postHandoff (qexit s : ℕ) (c : CConfig) : CConfig :=
  applyTrans c ((qexit, readSym c), (s, readSym c, (2 : Move)))

/-- **The sequenced machine.**  Phase 1, the handoff, then phase 2 on shifted states `[s, …)`. -/
def seqMachine (M₁ M₂ : TMachine) (qexit s : ℕ) : TMachine :=
  M₁ ++ handoffRules qexit s ++ shiftMachine s M₂

/-- **The handoff fires from the exit state (PROVED).**  At any config `c` in state `qexit`, `handoffRules qexit s`
steps to `postHandoff qexit s c` (state `s`). -/
theorem handoff_step (qexit s : ℕ) (c : CConfig) (hq : c.1 = qexit) :
    concreteStep (handoffRules qexit s) c (postHandoff qexit s c) := by
  refine ⟨((qexit, readSym c), (s, readSym c, (2 : Move))), ?_, ?_, rfl⟩
  · cases readSym c <;> simp [handoffRules]
  · rw [hq]

/-- **The sequenced run composes (PROVED).**  Phase 1 (`a` steps of `M₁` to a state-`qexit` config `c_mid`), the handoff
(1 step), and phase 2 (`b` steps of `shiftMachine s M₂` from `postHandoff`) concatenate into a run of `seqMachine` of
length `a + 1 + b`.  Each phase is lifted into the combined table by sub-table monotonicity (329); the run is
concatenated by `reachIn_add`. -/
theorem reachIn_seq (M₁ M₂ : TMachine) (qexit s a b : ℕ) (c c_mid c_final : CConfig)
    (h1 : reachIn (toNTM M₁) a c c_mid)
    (hq : c_mid.1 = qexit)
    (h2 : reachIn (toNTM (shiftMachine s M₂)) b (postHandoff qexit s c_mid) c_final) :
    reachIn (toNTM (seqMachine M₁ M₂ qexit s)) (a + 1 + b) c c_final := by
  have subM1 : M₁ ⊆ seqMachine M₁ M₂ qexit s :=
    (List.subset_append_left M₁ (handoffRules qexit s)).trans
      (List.subset_append_left _ (shiftMachine s M₂))
  have subH : handoffRules qexit s ⊆ seqMachine M₁ M₂ qexit s :=
    (List.subset_append_right M₁ (handoffRules qexit s)).trans
      (List.subset_append_left _ (shiftMachine s M₂))
  have subSh : shiftMachine s M₂ ⊆ seqMachine M₁ M₂ qexit s :=
    List.subset_append_right (M₁ ++ handoffRules qexit s) (shiftMachine s M₂)
  have hp1 := reachIn_mono subM1 a c c_mid h1
  have hh : concreteStep (seqMachine M₁ M₂ qexit s) c_mid (postHandoff qexit s c_mid) :=
    concreteStep_mono subH (handoff_step qexit s c_mid hq)
  have hp2 := reachIn_mono subSh b (postHandoff qexit s c_mid) c_final h2
  refine (reachIn_add (toNTM (seqMachine M₁ M₂ qexit s)) (a + 1) b c c_final).mpr
    ⟨postHandoff qexit s c_mid, ?_, hp2⟩
  refine (reachIn_add (toNTM (seqMachine M₁ M₂ qexit s)) a 1 c (postHandoff qexit s c_mid)).mpr
    ⟨c_mid, hp1, ?_⟩
  exact ⟨postHandoff qexit s c_mid, hh, rfl⟩

/-!
**The control-flow handoff, proved.**  `handoff_step` fires from the exit state, and `reachIn_seq` concatenates phase 1,
the handoff, and phase 2 into one run of the sequenced machine — phases lifted by 329/330, run composed by `reachIn_add`.
With 329/330 the routing machine's *control structure* is verified: parallel disjoint-state assembly plus exit→entry
sequencing.  Remaining for the complete decider: instantiate the phases with the universal simulator (296–298) and
bounded complement (299), and the `f`-timing bound — the remaining low-level engineering, not faked.  Third verified
brick.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineSequencing

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineSequencing.handoff_step
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RoutingMachineSequencing.reachIn_seq
