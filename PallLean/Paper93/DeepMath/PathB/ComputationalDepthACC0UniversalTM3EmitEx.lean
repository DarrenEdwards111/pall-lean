import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Emit

/-!
# Entry 456 — universal-TM-table build: the existence-cost emission lifting `universalSimEx_of_emits3` (proved)

The honest reformulation that removes the **fixed-`cost` obstruction** of `EmitsEncodedStep3` (entry 400).  That spec
demanded a *single* `cost` realising every encoded step — impossible for a real universal machine, whose per-step
transition count grows with the encoded sizes (scans, navigation).  The fix: an **existence-cost** emission obligation —
each encoded step is realised in *some* number of transitions — which lifts to the full simulation reaching the encoded
final config in *some* number of transitions (the genuine meaning of "U simulates M"; the exact step count is the sum of
the per-step counts, which we existentially quantify).

This is the spec the actual construction can discharge: every apply phase built (entries 404–455) provides exactly an
`∃ N, reachIn N …` run, so an assembled `U` would meet `EmitsEncodedStepEx3`, not the fixed-cost `EmitsEncodedStep3`.

## What is proved (clean axioms, no `sorry`)

* **`EmitsEncodedStepEx3 U φ`** — `∀ Mbits cbits next, encodedStep Mbits cbits = some next → ∃ N, reachIn (toNTM3 U) N (φ
  Mbits cbits) (φ Mbits next)`.
* **`universalSimEx_of_emits3`** (PROVED) — `EmitsEncodedStepEx3 U φ` ⟹ for any `M` and `simIter M k c0 = some cf`, `∃ N,
  reachIn (toNTM3 U) N (φ (encodeMachineBits M) (encodeConfig c0)) (φ (encodeMachineBits M) (encodeConfig cf))` — the whole
  `k`-step simulation is realised, by induction on `k` composing per-step emissions with `reachIn_add`.

## Honest scope

This re-establishes the **final lifting under an obstruction-free spec**: the universal-TM construction is reduced to one
*achievable* obligation — build a concrete `Sym3` `U` (with layout `φ`) and prove `EmitsEncodedStepEx3 U φ` (each encoded
lookup-and-apply is realised in some number of transitions, using the phases of entries 404–455).  That single
transition-table obligation is the genuine remaining low-level construction, **not built here and not faked** — but
everything it feeds (the full simulation run) is proved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitEx

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (TMachine3 CConfig3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop (simIter)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply (encodeConfig)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncodedRun (encodedStep encodedStep_correct)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine)

/-- **The existence-cost per-macro-step emission obligation.**  Each encoded step is realised in *some* number of
transitions of `toNTM3 U` — no fixed `cost`. -/
def EmitsEncodedStepEx3 (U : TMachine3) (φ : List Bool → List Bool → CConfig3) : Prop :=
  ∀ (Mbits cbits next : List Bool), encodedStep Mbits cbits = some next →
    ∃ N, reachIn (toNTM3 U) N (φ Mbits cbits) (φ Mbits next)

/-- **Existence-cost emission lifts to the full simulation (PROVED).**  If `U` realises each encoded step in some number of
transitions, then a whole `k`-step simulation `simIter M k c0 = some cf` is realised by `toNTM3 U` in some number of
transitions between the encoded configurations.  By induction on `k`: each `simIter` step is an `encodedStep`
(`encodedStep_correct`), realised by emission, composed by `reachIn_add`. -/
theorem universalSimEx_of_emits3 (U : TMachine3) (φ : List Bool → List Bool → CConfig3)
    (hemit : EmitsEncodedStepEx3 U φ) (M : TMachine) :
    ∀ (k : ℕ) (c0 cf : ACC0ConcreteNTM.CConfig), simIter M k c0 = some cf →
      ∃ N, reachIn (toNTM3 U) N
        (φ (encodeMachineBits M) (encodeConfig c0)) (φ (encodeMachineBits M) (encodeConfig cf)) := by
  intro k
  induction k with
  | zero =>
      intro c0 cf h
      simp only [simIter, Option.some.injEq] at h
      subst h
      exact ⟨0, rfl⟩
  | succ k ih =>
      intro c0 cf h
      rw [simIter, Option.bind_eq_some_iff] at h
      obtain ⟨c1, hc1, hrest⟩ := h
      have hes : encodedStep (encodeMachineBits M) (encodeConfig c0) = some (encodeConfig c1) := by
        rw [encodedStep_correct, hc1]; rfl
      obtain ⟨N1, step1⟩ := hemit (encodeMachineBits M) (encodeConfig c0) (encodeConfig c1) hes
      obtain ⟨N2, step2⟩ := ih c1 cf hrest
      exact ⟨N1 + N2, (reachIn_add (toNTM3 U) N1 N2 _ _).mpr ⟨_, step1, step2⟩⟩

/-!
**The existence-cost emission lifting, proved.**  `universalSimEx_of_emits3` re-establishes the final lifting under a spec
the construction can actually meet: the per-macro-step obligation `EmitsEncodedStepEx3` (each step realised in *some* number
of transitions) suffices to realise the entire `simIter` simulation.  So the remaining construction is one *achievable*
obligation — the concrete `Sym3` `U` + layout `φ` + `EmitsEncodedStepEx3` proof, assembling the scanners, the marker match
(entries 404–455), and the apply — each phase already an `∃ N, reachIn N …` run.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitEx

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitEx.universalSimEx_of_emits3
