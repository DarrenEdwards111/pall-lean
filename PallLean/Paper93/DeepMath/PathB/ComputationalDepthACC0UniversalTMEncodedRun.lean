import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMBitApply

/-!
# Entry 341 — universal-TM-table build, brick 8: the encoded simulation run, correct (proved)

Bricks 6–7 (entries 339–340) gave the two halves of one simulation step on the scannable encoding — bit-level lookup
and bit-level apply, each proved equal to its abstract counterpart.  Brick 8 **composes them into one encoded step**,
proves it equals the abstract `applyLookup`, and **iterates it** into the full encoded run, proving the entire
deterministic simulation runs correctly on encoded bit-tapes: `encodedRun = simIter` up to encoding.

**The encoded step and run.**  `encodedStep Mbits cbits` decodes the config from `cbits`, looks up the matching rule in
the encoded table `Mbits`, and applies it — all on bit-tapes: `encodedStep Mbits cbits := (bitLookup Mbits (decodeConfig
cbits).1).map (bitApply cbits)`.  `encodedRun` iterates it `k` times.  The correctness theorems pin them to the
config/rule engine: `encodedStep (encodeMachineBits M) (encodeConfig c) = (applyLookup M c).map encodeConfig`, and
`encodedRun (encodeMachineBits M) k (encodeConfig c) = (simIter M k c).map encodeConfig`.

## What is proved (clean axioms, no `sorry`)

* **`decodeConfig_encodeConfig_fst`** — `(decodeConfig (encodeConfig c)).1 = c`.
* **`encodedStep`** + **`encodedStep_correct`** (PROVED) — one encoded step equals `(applyLookup M c).map encodeConfig`:
  one simulation step on the encoded tape is exactly the abstract step, re-encoded.
* **`encodedRun`** + **`encodedRun_correct`** (PROVED) — `encodedRun (encodeMachineBits M) k (encodeConfig c) =
  (simIter M k c).map encodeConfig`: the entire `k`-step deterministic simulation runs correctly on encoded bit-tapes.

## Honest scope

This is the **culmination at the encoding level**: the full universal simulation (`simIter`, brick 4) runs correctly
entirely on the scannable bit-encoding (`encodedRun_correct`) — config encoding, lookup, apply, and the whole loop all
verified equal to the abstract engine.  The **one remaining residual** is purely the *function → transition* gap:
realising `encodedStep` (a function on bit-lists) as the transitions of one concrete `TMachine` `U` (the
`walkRight`-driven scans of bricks 1/5 wired into a transition table), which then gives `Realizes physU U φ cost` via the
entry-333 bridge (plus the `f`-timing).  That transition-table realisation is the genuine remaining low-level
construction, **not built here and not faked** — but everything it must compute is now verified correct.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncodedRun

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig TMTrans applyTrans)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup (lookup applyLookup)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop (simIter)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitLookup (bitLookup bitLookup_encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply
  (encodeConfig decodeConfig decodeConfig_encodeConfig bitApply bitApply_encodeConfig)

/-- **Decoding an encoded config recovers it (PROVED).** -/
theorem decodeConfig_encodeConfig_fst (c : CConfig) : (decodeConfig (encodeConfig c)).1 = c := by
  rw [← List.append_nil (encodeConfig c), decodeConfig_encodeConfig]

/-- **One encoded simulation step.**  Decode the config from `cbits`, look up the matching rule in the encoded table
`Mbits`, apply it — all on bit-tapes. -/
def encodedStep (Mbits cbits : List Bool) : Option (List Bool) :=
  (bitLookup Mbits (decodeConfig cbits).1).map (bitApply cbits)

/-- **The encoded step is the abstract step (PROVED).**  `encodedStep (encodeMachineBits M) (encodeConfig c) =
(applyLookup M c).map encodeConfig`: one step on the encoded tape equals the abstract `applyLookup`, re-encoded. -/
theorem encodedStep_correct (M : TMachine) (c : CConfig) :
    encodedStep (encodeMachineBits M) (encodeConfig c) = (applyLookup M c).map encodeConfig := by
  unfold encodedStep applyLookup
  rw [decodeConfig_encodeConfig_fst, bitLookup_encodeMachineBits, Option.map_map]
  congr 1
  funext t
  exact bitApply_encodeConfig c t

/-- **The encoded simulation run.**  Iterate `encodedStep` `k` times on bit-tapes. -/
def encodedRun (Mbits : List Bool) : ℕ → List Bool → Option (List Bool)
  | 0, cbits => some cbits
  | k + 1, cbits => (encodedStep Mbits cbits).bind (encodedRun Mbits k)

/-- **The encoded run is the abstract simulation (PROVED).**  `encodedRun (encodeMachineBits M) k (encodeConfig c) =
(simIter M k c).map encodeConfig`: the entire `k`-step deterministic simulation runs correctly on encoded bit-tapes. -/
theorem encodedRun_correct (M : TMachine) :
    ∀ (k : ℕ) (c : CConfig),
      encodedRun (encodeMachineBits M) k (encodeConfig c) = (simIter M k c).map encodeConfig := by
  intro k
  induction k with
  | zero => intro c; simp [encodedRun, simIter]
  | succ k ih =>
      intro c
      simp only [encodedRun, simIter]
      rw [encodedStep_correct]
      cases happ : applyLookup M c with
      | none => simp
      | some c' => simpa using ih c'

/-!
**Brick 8, at the encoding level.**  The full universal simulation runs correctly on the scannable bit-encoding:
`encodedStep_correct` (one step) composes bricks 6–7, and `encodedRun_correct` proves the whole loop equals `simIter`
(brick 4) up to encoding.  So everything the universal machine must compute is verified correct *on bit-tapes*.  The lone
remaining residual is realising `encodedStep` as the transitions of a concrete `TMachine` `U` (the `walkRight`-driven
scans of bricks 1/5), giving `Realizes physU U φ cost` via the entry-333 bridge (+ `f`-timing) — the genuine remaining
low-level construction, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncodedRun

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncodedRun.encodedStep_correct
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEncodedRun.encodedRun_correct
