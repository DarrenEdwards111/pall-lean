import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonHybrid
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonYao
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonHardness
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NWFromHardness

/-!
# `HardFunction → PRGExists` — the NW reconstruction assembled end-to-end (proved glue)

Workstream A, step 3 (final residue).  Entry 222 (`…ACC0NWFromHardness`) proved the **reconstruction contradiction**
glue (`prgFools_of_hard` : `NWReconstruction D S → ¬ S → ¬ D`), reducing `HardFunction → PRGExists` to the abstract
`NWReconstruction` socket (`Distinguisher → SmallCircuitForHardFn`).  Entries 190–196 separately proved the *concrete*
sub-pieces — the hybrid telescoping (`hybrid_advantage`), the Yao predict-from-distinguish identity
(`yaoPredictor_discharge`), the reconstruction poly-size accounting (`reconstruction_socket_discharge`), and the
hardness/circuit collision (`hardnessExcludesCircuit_discharge`) — but each discharged its *own* socket in isolation;
they were never chained, and the chain does not close on types alone (the Yao step outputs a *probability-level*
predictor, the reconstruction step consumes a *predictor-computes* hypothesis and outputs a `size ≤ bound` claim, while
the hardness step consumes a *concrete* `Circ`).

This file **assembles them end-to-end**, instantiating the three abstract sockets of `nw_hybrid_no_distinguisher` with
the concrete proved dischargers and threading the two genuinely model-dependent **bridges** that reconcile the levels:

```
GlobalAdvantage  ─[hybrid_advantage, PROVED]─►  AdjacentAdvantage
                 ─[yaoPredictor_discharge, PROVED]─►  YaoNextBitPredictor (probability level)
                 ─[bridgeYao = YaoCircuitEfficiency]─►  ComputesF (predictor as a circuit)
                 ─[reconstruction_socket_discharge, PROVED, + design]─►  SmallCircuitForFAt (size ≤ bound)
                 ─[bridgeRecon = ReconstructionCorrectness]─►  HasCircuitOfSize fbool s (a concrete small Circ)
```

The result `nwReconstruction_assembled` **discharges the entry-222 `NWReconstruction` socket** from the proved
sub-pieces, and `hardFn_to_prgExists_assembled` then chains the reconstruction contradiction to give
`HardFunction → PRGExists` (`HardFor fbool s → ¬ GlobalAdvantage f m ε`) — the final caveat-1 implication, assembled.

## What is proved (clean axioms, no `sorry`)

* **`reconstruction_rebridge`** — pre/post-composing the reconstruction socket to convert its predictor-input and
  circuit-output Props (the type-level glue that lets the Yao output feed the reconstruction input and the
  reconstruction output feed the hardness input).
* **`nwReconstruction_assembled`** — discharges `NWFromHardness.NWReconstruction (GlobalAdvantage f m ε)
  (HasCircuitOfSize fbool s)` by chaining `hybrid_advantage` → `yaoPredictor_discharge` → `bridgeYao` →
  `reconstruction_socket_discharge` (with the design) → `bridgeRecon`.
* **`hardFn_to_prgExists_assembled`** — `HardFor fbool s → ¬ GlobalAdvantage f m ε`, i.e. `HardFunction → PRGExists`,
  via `prgFools_of_hard` applied to the assembled reconstruction.

## Honest scope

This proves the **end-to-end assembly** of the NW reconstruction: every *combinatorial/analytic* step is now a proved
theorem in the chain (hybrid telescoping, Yao identity, poly-size accounting, hardness collision), and the remaining
inputs are exactly two **named model-dependent bridges** — `bridgeYao` (the probability-level Yao predictor is realised
as a circuit: the residual `YaoCircuitEfficiency` socket) and `bridgeRecon` (the reconstructed predictor-plus-tables is
a concrete `Circ` of size `≤ s` computing `f`: the residual `ReconstructionCorrectness` socket) — together with the
**irreducible hardness** of the witness function (`HardFor fbool s`, which is the circuit lower bound itself, supplied
by `NoEasyWitnessHardFn`) and the **proved low-intersection design** (`hdesign`).  So `HardFunction → PRGExists` is no
longer a monolithic residue: its analytic core is assembled, leaving the two circuit-realisation bridges and the
hardness assumption.  This is the honest content of the NW/IW hardness-to-pseudorandomness tradeoff at this level — not
the circuit-model realisation of the predictor, and emphatically **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionAssembly

open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid
  (GlobalAdvantage AdjacentAdvantage YaoPredictor Reconstruction hybrid_advantage)
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYao (YaoNextBitPredictor yaoPredictor_discharge)
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconstruction
  (ReconNextBit ReconDesign SmallCircuitForFAt reconstruction_socket_discharge)
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHardness (HardFor HasCircuitOfSize)
open PallLean.Paper93.DeepMath.PathB.ACC0NWFromHardness (NWReconstruction prgFools_of_hard)

/-- **Type-level glue for the reconstruction socket (PROVED).**  `Reconstruction P D C` is `P → D → C`; pre-composing
the predictor input with `pre : P' → P` and post-composing the circuit output with `post : C → C'` yields
`Reconstruction P' D C'`.  This is what lets the *probability-level* Yao output feed the reconstruction's
*predictor-computes* input, and the reconstruction's *size-bound* output feed the hardness step's *concrete-circuit*
input. -/
theorem reconstruction_rebridge (P P' D C C' : Prop)
    (recon : Reconstruction P D C) (pre : P' → P) (post : C → C') :
    Reconstruction P' D C' :=
  fun hp' hd => post (recon (pre hp') hd)

/-- **The NW reconstruction discharged end-to-end (PROVED).**  Chaining the proved sub-pieces — `hybrid_advantage`
(global ⇒ adjacent advantage), `yaoPredictor_discharge` (adjacent advantage ⇒ probability-level next-bit predictor),
the `bridgeYao` realisation (predictor ⇒ `ComputesF`, the residual `YaoCircuitEfficiency` socket),
`reconstruction_socket_discharge` (predictor + low-intersection design ⇒ a `size ≤ bound` circuit), and the
`bridgeRecon` realisation (that circuit ⇒ a concrete `Circ` of size `≤ s` computing `f`, the residual
`ReconstructionCorrectness` socket) — discharges the entry-222 `NWReconstruction` socket:
`GlobalAdvantage f m ε → HasCircuitOfSize fbool s`. -/
theorem nwReconstruction_assembled
    {n : ℕ} (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (predictorSize numOther k s : ℕ) (r : Fin numOther → ℕ)
    (ComputesF : Prop) (fbool : (Fin n → Bool) → Bool)
    (bridgeYao : YaoNextBitPredictor f m ε → ComputesF)
    (bridgeRecon : SmallCircuitForFAt ComputesF
        (predictorSize + ∑ j, Fintype.card (Fin (r j) → Bool))
        (predictorSize + numOther * 2 ^ k) → HasCircuitOfSize fbool s)
    (hdesign : ReconDesign numOther k r) :
    NWReconstruction (GlobalAdvantage f m ε) (HasCircuitOfSize fbool s) := by
  -- pre/post-compose the proved reconstruction socket with the two bridges, matching the Yao output and hardness input.
  have recon' :
      Reconstruction (YaoNextBitPredictor f m ε) (ReconDesign numOther k r) (HasCircuitOfSize fbool s) :=
    reconstruction_rebridge (ReconNextBit predictorSize ComputesF) (YaoNextBitPredictor f m ε)
      (ReconDesign numOther k r)
      (SmallCircuitForFAt ComputesF (predictorSize + ∑ j, Fintype.card (Fin (r j) → Bool))
        (predictorSize + numOther * 2 ^ k))
      (HasCircuitOfSize fbool s)
      (reconstruction_socket_discharge predictorSize numOther k r ComputesF)
      bridgeYao bridgeRecon
  -- chain: GlobalAdvantage ⇒ AdjacentAdvantage ⇒ YaoNextBitPredictor ⇒ HasCircuitOfSize.
  intro hglob
  exact recon' (yaoPredictor_discharge f m ε (hybrid_advantage f m ε hε hglob)) hdesign

/-- **`HardFunction → PRGExists`, assembled (PROVED).**  The reconstruction contradiction of entry 222
(`prgFools_of_hard`) applied to the assembled `NWReconstruction`: the hardness of the witness function
(`HardFor fbool s = ¬ HasCircuitOfSize fbool s`) plus the reconstruction (`GlobalAdvantage ⇒ HasCircuitOfSize`) gives
`¬ GlobalAdvantage f m ε` — i.e. no distinguisher, the NW generator fools, `PRGExists`.  This is the final caveat-1
implication, assembled end-to-end from the proved sub-pieces and the two named circuit-realisation bridges. -/
theorem hardFn_to_prgExists_assembled
    {n : ℕ} (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (predictorSize numOther k s : ℕ) (r : Fin numOther → ℕ)
    (ComputesF : Prop) (fbool : (Fin n → Bool) → Bool)
    (bridgeYao : YaoNextBitPredictor f m ε → ComputesF)
    (bridgeRecon : SmallCircuitForFAt ComputesF
        (predictorSize + ∑ j, Fintype.card (Fin (r j) → Bool))
        (predictorSize + numOther * 2 ^ k) → HasCircuitOfSize fbool s)
    (hdesign : ReconDesign numOther k r) :
    HardFor fbool s → ¬ GlobalAdvantage f m ε :=
  fun hHard =>
    prgFools_of_hard (GlobalAdvantage f m ε) (HasCircuitOfSize fbool s)
      (nwReconstruction_assembled f m ε hε predictorSize numOther k s r ComputesF fbool
        bridgeYao bridgeRecon hdesign)
      hHard

/-!
**The NW reconstruction, assembled end-to-end.**  `HardFunction → PRGExists` is no longer a monolithic residue: the
hybrid telescoping, Yao identity, reconstruction poly-size, and hardness collision are proved theorems chained through
`nw_hybrid_no_distinguisher`'s sockets (`nwReconstruction_assembled`), and the reconstruction contradiction (222)
delivers `HardFor fbool s → ¬ GlobalAdvantage f m ε` (`hardFn_to_prgExists_assembled`).  What remains are the two
named model-dependent circuit-realisation bridges (`bridgeYao` = `YaoCircuitEfficiency`, `bridgeRecon` =
`ReconstructionCorrectness`), the irreducible hardness of the witness (`HardFor fbool s`, the circuit lower bound), and
the proved low-intersection design.  The analytic core of the NW/IW hardness-to-pseudorandomness tradeoff is assembled.
Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionAssembly

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionAssembly.reconstruction_rebridge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionAssembly.nwReconstruction_assembled
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionAssembly.hardFn_to_prgExists_assembled
