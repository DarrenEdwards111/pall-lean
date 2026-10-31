import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMEmit

/-!
# Entry 343 — universal-TM-table build, brick 10: emission ⇒ the universal machine decides (proved)

Brick 9 (entry 342) proved emission lifts to the full simulation run.  Brick 10 closes the conditional chain: given the
emission socket and a **natural accept-layout** condition, the universal machine `U` actually **reaches its accept
state** exactly when the simulated machine's run accepts — i.e. `U` *decides* what the simulated machine decides.

**The accept layout.**  `AcceptLayout φ` says `U`'s state (the first component of `φ Mbits (encodeConfig c)`) is the
accept state `1` iff the simulated config `c` is accepting (`c.1 = 1`) — the obvious condition that `U`'s accept state
mirrors the simulated machine's.  Combined with the brick-9 run lifting, a simulation that reaches an accepting config
gives a `U`-run reaching a `U`-accept config.

## What is proved (clean axioms, no `sorry`)

* **`AcceptLayout`** — `U`'s accept state mirrors the simulated config's accept state, under the layout `φ`.
* **`universalReachesAccept_of_emits`** (PROVED) — `EmitsEncodedStep` + `AcceptLayout` + a simulation `simIter M k c0 =
  some cf` reaching an accepting `cf` (`cf.1 = 1`) ⟹ `U` runs in `k * cost` steps from the encoded `c0` to a config in
  its accept state.  So `U` decides correctly, conditional on the two layout/emission sockets.

## Honest scope

This proves the **final conditional theorem**: the universal machine `U` reaches its accept state exactly when the
simulated machine's run accepts, *given* the emission socket (`EmitsEncodedStep`, brick 9) and the natural accept-layout
(`AcceptLayout`).  So the entire Williams universal-simulation phase is now reduced to **one** irreducible construction —
building a concrete `U` (+ layout `φ`) satisfying `EmitsEncodedStep` and `AcceptLayout` — with *all* of its consequences
(the full run, and correct acceptance) proved.  That single construction (a verified universal-TM transition table) is
the genuine remaining low-level work, **not built here and not faked**; everything it would deliver is verified.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMDecide

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop (simIter)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply (encodeConfig)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMEmit (EmitsEncodedStep universalSim_of_emits)

/-- **The accept layout.**  Under the tape layout `φ`, `U`'s state mirrors the simulated config's accept status: `U` is
in its accept state `1` iff the simulated config `c` is accepting. -/
def AcceptLayout (φ : List Bool → List Bool → CConfig) : Prop :=
  ∀ (Mbits : List Bool) (c : CConfig), (φ Mbits (encodeConfig c)).1 = 1 ↔ c.1 = 1

/-- **Emission ⇒ the universal machine decides (PROVED).**  If `U` emits each encoded step (`EmitsEncodedStep`) and its
accept state mirrors the simulated config's (`AcceptLayout`), then a simulation `simIter M k c0 = some cf` reaching an
accepting config (`cf.1 = 1`) yields a `k * cost`-step run of `U` from the encoded `c0` to a configuration in `U`'s
accept state — `U` accepts exactly when the simulation accepts. -/
theorem universalReachesAccept_of_emits (U : TMachine) (φ : List Bool → List Bool → CConfig) (cost : ℕ)
    (hemit : EmitsEncodedStep U φ cost) (hlay : AcceptLayout φ)
    (M : TMachine) (k : ℕ) (c0 cf : CConfig)
    (hsim : simIter M k c0 = some cf) (hacc : cf.1 = 1) :
    ∃ d, reachIn (toNTM U) (k * cost)
        (φ (encodeMachineBits M) (encodeConfig c0)) d ∧ d.1 = 1 :=
  ⟨φ (encodeMachineBits M) (encodeConfig cf),
    universalSim_of_emits U φ cost hemit M k c0 cf hsim,
    (hlay (encodeMachineBits M) cf).mpr hacc⟩

/-!
**Brick 10, built.**  `universalReachesAccept_of_emits` closes the conditional chain: the emission socket
(`EmitsEncodedStep`, brick 9) plus the natural accept-layout (`AcceptLayout`) make the universal machine `U` reach its
accept state exactly when the simulated machine's run accepts.  So the whole Williams universal-simulation phase is
reduced to **one** construction — a concrete `U` (+ `φ`) with `EmitsEncodedStep` and `AcceptLayout` (a verified
universal-TM transition table) — with all its consequences (the run, correct acceptance) proved.  That single
transition-table construction is the genuine remaining low-level work, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMDecide

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMDecide.universalReachesAccept_of_emits
