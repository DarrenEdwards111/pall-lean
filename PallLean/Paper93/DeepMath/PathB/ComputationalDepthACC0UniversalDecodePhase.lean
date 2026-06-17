import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalDecode

/-!
# The universal decode phase — recover `(M, c)` from the tape, faithfully and unambiguously

Third of entry 182's four per-phase realizations (after rewrite, entry 183, and lookup, entry 184).  The **decode
phase** parses the universal machine's tape `encodeSim M c` and recovers the simulated state `(M, c)`.  Unlike the
rewrite/lookup phases, decode touches the tape *layout* (the `encodeTape` encoding).  Using the proved tape-encoding
contracts (`…ACC0TapeEncoding`: `decodeTape_encodeTape`, `encodeTape_inj`) and the decode round-trip
(`…ACC0UniversalDecode`), this file proves the decode phase: the decode recovers `(M, c)` exactly (round-trip), the
recovery is **unambiguous** (the encoding is injective — no two simulation states share a tape), and the recovered
machine can then take its step.

## What is proved (clean axioms, no `sorry`)

* **`encodeSim_inj`** — the simulation-tape encoding is injective: `encodeSim M c = encodeSim M' c' → M = M' ∧ c = c'`
  (via `encodeTape_inj` + `machineEquiv.injective`).
* **`decode_phase`** — the decode phase realized: for a step `concreteStep M c d`, (a) `decodeSim (encodeSim M c) =
  some (M, c)` (round-trip recovery), (b) `reachIn (toNTM M) 1 c d` (the decoded machine steps), and (c) the recovery is
  unambiguous (`∀ M' c', encodeSim M c = encodeSim M' c' → M = M' ∧ c = c'`).

## Honest scope

This proves the decode phase's **correctness contract**: the recovery is faithful (round-trip) and unambiguous
(injective), and it connects to the simulated machine's step.  Together with the rewrite (entry 183) and lookup (entry
184) phases, three of the four entry-182 phases now have proved correctness/realization.  What it does **not** do is
realise the parse as the universal machine `U` *scanning* the `encodeTape` bit-layout with its own transitions and a
per-symbol step count — that tape-walking realisation (the `bDecode` step count over the layout) is the remaining step.
Classical Turing-machine construction, not an open problem; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecodePhase

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig concreteStep toNTM machineEquiv)
open PallLean.Paper93.DeepMath.PathB.ACC0TapeEncoding (encodeTape encodeTape_inj)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecode
  (encodeSim decodeSim decodeSim_encodeSim decoded_machine_steps)

/-- **The simulation-tape encoding is injective (proved): same tape ⇒ same machine and configuration.**  `encodeSim M c
= encodeTape (machineEquiv M) c`, so `encodeTape_inj` gives equal codes and configs, and `machineEquiv.injective`
recovers the machine — the encoded tape determines `(M, c)` uniquely, so the decode is unambiguous. -/
theorem encodeSim_inj {M M' : TMachine} {c c' : CConfig}
    (h : encodeSim M c = encodeSim M' c') : M = M' ∧ c = c' := by
  have hpair := encodeTape_inj (show encodeTape (machineEquiv M) c = encodeTape (machineEquiv M') c' from h)
  exact ⟨machineEquiv.injective hpair.1, hpair.2⟩

/-- **The decode phase realized (proved): faithful, unambiguous, and enabling the step.**  For a step `concreteStep M c
d`: (a) the tape decodes to `(M, c)` (round-trip, `decodeSim_encodeSim`); (b) the decoded machine reaches `d` in one
physical step (`decoded_machine_steps`); (c) the recovery is unambiguous — any tape equal to `encodeSim M c` came from
the same `(M, c)` (`encodeSim_inj`).  This discharges the decode phase of entry 182 as a faithful, invertible recovery
wired to the simulated step. -/
theorem decode_phase (M : TMachine) (c d : CConfig) (h : concreteStep M c d) :
    decodeSim (encodeSim M c) = some (M, c)
      ∧ reachIn (toNTM M) 1 c d
      ∧ (∀ M' c', encodeSim M c = encodeSim M' c' → M = M' ∧ c = c') :=
  ⟨(decoded_machine_steps M c d h).1, (decoded_machine_steps M c d h).2,
   fun _ _ he => encodeSim_inj he⟩

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecodePhase

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecodePhase.encodeSim_inj
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalDecodePhase.decode_phase
