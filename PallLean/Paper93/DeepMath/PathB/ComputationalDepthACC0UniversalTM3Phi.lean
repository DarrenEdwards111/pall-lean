import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3FullLayout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SimTapeLayout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMBitApply
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScannable

/-!
# Entry 465 — universal-TM-table build: the bit-decoding layout `layoutPhi3` (proved)

The layout `φ : List Bool → List Bool → CConfig3` for `EmitsEncodedStepEx3` (entry 456): decode the encoded config `cbits`
(via `decodeConfig`, the same decoder `encodedStep` uses) and the encoded machine `Mbits` (via `decodeMachineBits`), and
build the stitched tape `fullTape3` (entry 461) — home marker, config key (the config's state and current symbol), rule
table (the decoded machine's keys), and simulated tape (the config's tape with the head marker, `simTapeRegion`).  The
control state starts at `initState` with the head at the config home `c = 1`.

## What is proved (clean axioms, no `sorry`)

* **`layoutPhi3 initState Mbits cbits`** — the decoded `CConfig3` layout.
* **`layoutPhi3_wellformed`** (PROVED) — the control state is `initState`, the head is at `1`, and the home marker is at
  cell `0`.
* **`layoutPhi3_config`** (PROVED) — the config-key invariants (home marker, state field, separator, cache) hold on the
  decoded tape.

## Honest scope

This defines `φ` (the bit-decoding layout) with its well-formedness / config invariants.  It does **not** yet define the
global `U`, nor prove `EmitsEncodedStepEx3 U layoutPhi3` (the end-to-end run, the large but obstruction-free remaining
assembly, per entry 456).  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Phi

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 CConfig3)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans readSym)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply (decodeConfig)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (decodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SimTapeLayout (simTapeRegion)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullLayout (fullTape3 fullTape3_config)

/-- **The bit-decoding layout.**  Decode `cbits`/`Mbits` and build the stitched tape; control at `initState`, head at the
config home `1`. -/
def layoutPhi3 (initState : ℕ) (Mbits cbits : List Bool) : CConfig3 :=
  (initState, 1,
    fullTape3 ((decodeConfig cbits).1).1 (readSym (decodeConfig cbits).1)
      (((decodeMachineBits Mbits).getD ([], [])).1.map (·.1))
      (simTapeRegion ((decodeConfig cbits).1).2.2 ((decodeConfig cbits).1).2.1))

/-- **The layout is well-formed (PROVED).**  Control `= initState`, head `= 1`, home marker at `0`. -/
theorem layoutPhi3_wellformed (initState : ℕ) (Mbits cbits : List Bool) :
    (layoutPhi3 initState Mbits cbits).1 = initState
    ∧ (layoutPhi3 initState Mbits cbits).2.1 = 1
    ∧ (layoutPhi3 initState Mbits cbits).2.2.getD 0 Sym3.O = Sym3.M :=
  ⟨rfl, rfl, (fullTape3_config _ _ _ _).1⟩

/-- **The config-key invariants on the decoded tape (PROVED).** -/
theorem layoutPhi3_config (initState : ℕ) (Mbits cbits : List Bool) :
    (layoutPhi3 initState Mbits cbits).2.2.getD 0 Sym3.O = Sym3.M
    ∧ (∀ i, i < ((decodeConfig cbits).1).1 →
        (layoutPhi3 initState Mbits cbits).2.2.getD (1 + i) Sym3.O = Sym3.I)
    ∧ (layoutPhi3 initState Mbits cbits).2.2.getD (1 + ((decodeConfig cbits).1).1) Sym3.O = Sym3.O
    ∧ (layoutPhi3 initState Mbits cbits).2.2.getD (1 + ((decodeConfig cbits).1).1 + 1) Sym3.O
        = boolToSym3 (readSym (decodeConfig cbits).1) :=
  fullTape3_config _ _ _ _

/-!
**The bit-decoding layout, proved.**  `layoutPhi3` decodes the encoded machine and config into the stitched tape, with the
config-key invariants holding — the concrete `φ` that `EmitsEncodedStepEx3` needs.  Next: assemble the global `U` and prove
`EmitsEncodedStepEx3 U layoutPhi3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Phi

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Phi.layoutPhi3_wellformed
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Phi.layoutPhi3_config
