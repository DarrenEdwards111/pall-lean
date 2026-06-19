import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMEncodedRun

/-!
# Entry 342 — universal-TM-table build, brick 9: emission ⇒ full universal simulation (proved)

Brick 8 (entry 341) proved the entire deterministic simulation runs correctly on the scannable bit-encoding
(`encodedRun = simIter` up to encoding).  The lone residual is realising one encoded step as `TMachine` transitions.
This file proves the **final lifting**: if a concrete `TMachine` `U` *emits* each encoded step in `cost` transitions
(the per-macro-step obligation `EmitsEncodedStep`), then `U`'s run realises the **entire** `simIter` simulation, with a
`× cost` blowup.  So the universal-TM construction is reduced to exactly that single per-step emission obligation, with
everything above it — the whole simulation run — proved.

**The emission obligation.**  `EmitsEncodedStep U φ cost` says: whenever the encoded step `encodedStep Mbits cbits =
some next` succeeds, `U` runs in `cost` transitions from the `U`-configuration holding `(Mbits, cbits)` (via the layout
`φ`) to the one holding `(Mbits, next)`.  Given it, `universalSim_of_emits` lifts a whole `k`-step simulation `simIter M
k c0 = some cf` to `reachIn (toNTM U) (k * cost) (φ … (encodeConfig c0)) (φ … (encodeConfig cf))`.

## What is proved (clean axioms, no `sorry`)

* **`EmitsEncodedStep`** — the per-macro-step obligation: `U` realises one encoded step in `cost` transitions.
* **`universalSim_of_emits`** (PROVED) — emission + the brick-8 `encodedStep_correct` ⟹ `U` realises the full `simIter`
  simulation (`reachIn (toNTM U) (k*cost) …`), by induction on `k` composing per-step emissions with `reachIn_add`.

## Honest scope

This proves the **final lifting** — the per-macro-step emission obligation `EmitsEncodedStep` suffices to realise the
entire universal simulation on `U` (mirroring the entry-333 bridge, specialised to the verified encoded run).  So the
*whole* universal-TM construction is now reduced to exactly **one** named, irreducible obligation: build a concrete `U`
(with layout `φ`) and prove `EmitsEncodedStep U φ cost` — i.e. that `U`'s transitions realise *one* encoded
lookup-and-apply over the tape (the `walkRight`-driven scans of bricks 1/5 wired into a transition table).  That single
transition-table obligation is the genuine remaining low-level construction, **not built here and not faked** — but
everything it feeds into (the full simulation run, and acceptance via brick 4 + the entry-333 bridge) is proved.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEmit

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup (applyLookup)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop (simIter)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply (encodeConfig)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncodedRun (encodedStep encodedStep_correct)

/-- **The per-macro-step emission obligation.**  `U`, via the tape layout `φ : (machine-bits) → (config-bits) →
U-config`, realises one encoded step in `cost` transitions: a successful `encodedStep Mbits cbits = some next` is a
`cost`-step run of `toNTM U` from `φ Mbits cbits` to `φ Mbits next`. -/
def EmitsEncodedStep (U : TMachine) (φ : List Bool → List Bool → CConfig) (cost : ℕ) : Prop :=
  ∀ (Mbits cbits next : List Bool), encodedStep Mbits cbits = some next →
    reachIn (toNTM U) cost (φ Mbits cbits) (φ Mbits next)

/-- **Emission lifts to the full simulation (PROVED).**  If `U` emits each encoded step in `cost` transitions, then a
whole `k`-step simulation `simIter M k c0 = some cf` is a `k * cost`-step run of `U` between the `U`-configurations
holding the encoded `c0` and `cf`.  By induction on `k`: each `simIter` step is an `encodedStep` (`encodedStep_correct`,
brick 8), each `encodedStep` is `cost` `U`-steps (emission), composed by `reachIn_add`. -/
theorem universalSim_of_emits (U : TMachine) (φ : List Bool → List Bool → CConfig) (cost : ℕ)
    (hemit : EmitsEncodedStep U φ cost) (M : TMachine) :
    ∀ (k : ℕ) (c0 cf : CConfig), simIter M k c0 = some cf →
      reachIn (toNTM U) (k * cost)
        (φ (encodeMachineBits M) (encodeConfig c0)) (φ (encodeMachineBits M) (encodeConfig cf)) := by
  intro k
  induction k with
  | zero =>
      intro c0 cf h
      simp only [simIter, Option.some.injEq] at h
      subst h
      rw [Nat.zero_mul]
      rfl
  | succ k ih =>
      intro c0 cf h
      rw [simIter, Option.bind_eq_some_iff] at h
      obtain ⟨c1, hc1, hrest⟩ := h
      have hes : encodedStep (encodeMachineBits M) (encodeConfig c0) = some (encodeConfig c1) := by
        rw [encodedStep_correct, hc1]; rfl
      have step1 := hemit (encodeMachineBits M) (encodeConfig c0) (encodeConfig c1) hes
      have step2 := ih c1 cf hrest
      have hcomp := (reachIn_add (toNTM U) cost (k * cost) _ _).mpr ⟨_, step1, step2⟩
      rwa [show (k + 1) * cost = cost + k * cost from by ring]

/-!
**Brick 9, built.**  `universalSim_of_emits` proves the per-macro-step emission obligation `EmitsEncodedStep` suffices to
realise the entire `simIter` simulation on a concrete `U` (with `× cost` blowup) — the final lifting, mirroring the
entry-333 bridge.  So the whole universal-TM construction is reduced to **one** irreducible obligation: build a concrete
`U` and prove `EmitsEncodedStep U φ cost` (that `U`'s transitions realise one encoded lookup-and-apply over the tape).
That single transition-table obligation is the genuine remaining low-level construction, not faked; everything it feeds
(the full run, acceptance via brick 4 + the entry-333 bridge) is proved.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEmit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEmit.universalSim_of_emits
