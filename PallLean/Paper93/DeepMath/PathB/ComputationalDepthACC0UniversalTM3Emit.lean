import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMEmit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Sym

/-!
# Entry 400 — universal-TM-table build: the `Sym3` emission lifting `universalSim_of_emits3` (proved)

Entry 342 proved the **final lifting** for the Bool tape model: a per-macro-step emission obligation `EmitsEncodedStep U
φ cost` suffices to realise the *entire* `simIter` simulation on a concrete machine `U`.  The marker route puts the
universal machine `U` on the 3-symbol tape (`toNTM3`) — so this brick re-establishes that lifting over `toNTM3`.

The key observation: the whole abstract simulation layer — `encodedStep`, `simIter`, `encodeConfig`,
`encodeMachineBits`, and the correctness `encodedStep_correct` — is **symbol-agnostic**: those are pure functions on
*bit-lists*, unchanged by the tape alphabet.  Only the machine `U`, its tape layout `φ : List Bool → List Bool →
CConfig3`, and the run relation `reachIn (toNTM3 U)` are `Sym3`-specific.  So `universalSim_of_emits3` is a direct port
of entry 342 with `toNTM → toNTM3`, reusing the entire Bool abstract simulation correctness verbatim.

## What is proved (clean axioms, no `sorry`)

* **`EmitsEncodedStep3 U φ cost`** — the per-macro-step obligation over the 3-symbol machine: a successful `encodedStep
  Mbits cbits = some next` is a `cost`-step run of `toNTM3 U` from `φ Mbits cbits` to `φ Mbits next`.
* **`universalSim_of_emits3`** (PROVED) — emission + the (reused) `encodedStep_correct` ⟹ `toNTM3 U` realises the full
  `simIter` simulation (`reachIn (toNTM3 U) (k*cost) …`), by induction on `k` composing per-step emissions with
  `reachIn_add`.

## Honest scope

This re-establishes the **final lifting** over the marker tape: the whole `Sym3` universal-TM construction is reduced to
exactly **one** obligation — build the concrete `Sym3` machine `U` (with layout `φ`) and prove `EmitsEncodedStep3 U φ
cost` (that `U`'s transitions realise one encoded lookup-and-apply over the marker tape, using the scanners of entries
395–398 and the marker match of entry 399 onward).  That single transition-table obligation is the genuine remaining
low-level construction, **not built here and not faked** — but everything it feeds (the full simulation run) is proved.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Emit

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (TMachine3 CConfig3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop (simIter)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply (encodeConfig)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncodedRun (encodedStep encodedStep_correct)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine)

/-- **The per-macro-step emission obligation over the 3-symbol machine.**  `U` (a `Sym3` machine), via the tape layout
`φ : (machine-bits) → (config-bits) → CConfig3`, realises one encoded step in `cost` transitions: a successful
`encodedStep Mbits cbits = some next` is a `cost`-step run of `toNTM3 U` from `φ Mbits cbits` to `φ Mbits next`. -/
def EmitsEncodedStep3 (U : TMachine3) (φ : List Bool → List Bool → CConfig3) (cost : ℕ) : Prop :=
  ∀ (Mbits cbits next : List Bool), encodedStep Mbits cbits = some next →
    reachIn (toNTM3 U) cost (φ Mbits cbits) (φ Mbits next)

/-- **Emission lifts to the full simulation over the 3-symbol machine (PROVED).**  If `U` emits each encoded step in
`cost` transitions, then a whole `k`-step simulation `simIter M k c0 = some cf` is a `k * cost`-step run of `toNTM3 U`
between the configurations holding the encoded `c0` and `cf`.  By induction on `k`: each `simIter` step is an
`encodedStep` (`encodedStep_correct`, reused from the Bool layer), each `encodedStep` is `cost` `U`-steps (emission),
composed by `reachIn_add`. -/
theorem universalSim_of_emits3 (U : TMachine3) (φ : List Bool → List Bool → CConfig3) (cost : ℕ)
    (hemit : EmitsEncodedStep3 U φ cost) (M : TMachine) :
    ∀ (k : ℕ) (c0 cf : ACC0ConcreteNTM.CConfig), simIter M k c0 = some cf →
      reachIn (toNTM3 U) (k * cost)
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
      have hcomp := (reachIn_add (toNTM3 U) cost (k * cost) _ _).mpr ⟨_, step1, step2⟩
      rwa [show (k + 1) * cost = cost + k * cost from by ring]

/-!
**The `Sym3` emission lifting, proved.**  `universalSim_of_emits3` re-establishes that the per-macro-step obligation
`EmitsEncodedStep3` suffices to realise the entire `simIter` simulation on a concrete marker-tape machine `U` — the whole
abstract simulation correctness reused verbatim from the Bool layer.  So the remaining construction is reduced to one
obligation: the concrete `Sym3` `U` + layout `φ` + `EmitsEncodedStep3` proof, assembling the scanners and the marker
match.  Next: continue the marker match composites (single-bit compare, key compare, the match loop) — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Emit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Emit.universalSim_of_emits3
