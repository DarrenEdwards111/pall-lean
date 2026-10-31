import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TapeEncoding
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PhysicalStep

/-!
# The universal decode brick — recover `(machine, config)` from the tape, then step

Next brick of the physical universal machine.  `U`'s tape holds `encodeSim M c = encodeTape ⟨M⟩ c` (the encoded machine
code and simulated configuration).  The **decode step** recovers the full simulation state `(M, c)` from that tape, so
the universal machine can then apply `M`'s transition (the atomic step `reachIn_one`).  This file composes the tape
encoding (`…ACC0TapeEncoding`) with the machine enumeration (`machineEquiv`) and proves the decode **round-trip**, then
connects it to the atomic step.

## What is proved (clean axioms, no `sorry`)

* **`encodeSim` / `decodeSim`** — the full simulation-state tape layout and its decoder (tape → `(machine, config)`).
* **`decodeSim_encodeSim`** — the decode round-trip: `decodeSim (encodeSim M c) = some (M, c)` (recover the machine and
  its configuration from the tape).
* **`decoded_machine_steps`** — decode then step: the tape decodes to `(M, c)`, and the decoded machine reaches any
  `d` with `concreteStep M c d` in one step.

## Honest scope

The decode *function* and its round-trip are proved — the contract the physical decode sub-machine meets — and they
are wired to the atomic step.  Realising the decode as `U`-transitions that scan and parse the `encodeTape` layout is
the socket; the universal `U` that loops *decode → step → re-encode* over its own tape in `B` steps remains the large
construction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig concreteStep toNTM machineEquiv)
open PallLean.Paper93.DeepMath.PathB.ACC0TapeEncoding (encodeTape decodeTape decodeTape_encodeTape)

/-- The full simulation-state tape layout: encode the machine *code* `⟨M⟩` and the simulated configuration `c`. -/
noncomputable def encodeSim (M : TMachine) (c : CConfig) : List Bool :=
  encodeTape (machineEquiv M) c

/-- The decoder: parse the tape to `(code, config)`, then decode the code to its machine. -/
noncomputable def decodeSim (bs : List Bool) : Option (TMachine × CConfig) :=
  (decodeTape bs).map (fun p => (machineEquiv.symm p.1, p.2))

/-- **The decode round-trip (proved): recover `(M, c)` from the tape.**  `decodeSim (encodeSim M c) = some (M, c)`. -/
theorem decodeSim_encodeSim (M : TMachine) (c : CConfig) :
    decodeSim (encodeSim M c) = some (M, c) := by
  simp only [decodeSim, encodeSim, decodeTape_encodeTape, Option.map_some, Equiv.symm_apply_apply]

/-- **Decode then step (proved): the universal machine recovers `(M, c)` and the decoded machine steps.**  The tape
decodes to `(M, c)`, and the decoded machine reaches any `d` with `concreteStep M c d` in one step (`reachIn_one`). -/
theorem decoded_machine_steps (M : TMachine) (c d : CConfig) (h : concreteStep M c d) :
    decodeSim (encodeSim M c) = some (M, c) ∧ reachIn (toNTM M) 1 c d :=
  ⟨decodeSim_encodeSim M c, (ACC0PhysicalStep.reachIn_one M c d).mpr h⟩

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode.decodeSim_encodeSim
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode.decoded_machine_steps
