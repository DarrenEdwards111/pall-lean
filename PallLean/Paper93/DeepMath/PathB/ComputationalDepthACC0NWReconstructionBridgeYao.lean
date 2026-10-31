import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NWReconstructionAssembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonYaoCircuit

/-!
# Entry 321 — discharging `bridgeYao` in the NW reconstruction assembly (proved)

Entry 316 assembled the NW reconstruction end-to-end (`HardFunction → PRGExists`) modulo **two** named model-dependent
bridges: `bridgeYao` (the probability-level Yao predictor is realised as a circuit) and `bridgeRecon` (the reconstructed
predictor-plus-tables is a concrete small `Circ` computing `f`).  This file **discharges `bridgeYao`** by instantiating
the assembly's abstract `ComputesF` at the *concrete* small predictor circuit of entry 194
(`…ACC0NisanWigdersonYaoCircuit`) and supplying the bridge from the proved `yaoCircuitEfficiency_discharge`.

**The discharge.**  `bridgeYao : YaoNextBitPredictor f m ε → ComputesF` is exactly a `YaoCircuitEfficiency`
(`YaoNextBit → SmallPredictorCircuit`).  Entry 194 built the explicit predictor circuit `predictor D gidx :=
(x gidx) ⊕ ¬D` over a gate-level `Circ` syntax and proved (`yaoCircuitEfficiency_discharge`) that it is a small circuit
(`SmallPredictor D gidx`: size `≤ size D + 3`, computing the guess-and-correct rule).  Instantiating
`ComputesF := SmallPredictor D gidx`, `bridgeYao` is `yaoCircuitEfficiency_discharge D gidx (YaoNextBitPredictor f m ε)`
— **no longer a hypothesis**.

## What is proved (clean axioms, no `sorry`)

* **`bridgeYao_discharged`** — `YaoNextBitPredictor f m ε → SmallPredictor D gidx`: the probability-level Yao predictor
  yields the concrete small predictor circuit (size `≤ size D + 3`), via `yaoCircuitEfficiency_discharge`.
* **`nwReconstruction_bridgeYao_discharged`** — entry 316's `nwReconstruction_assembled` with `bridgeYao` supplied:
  `NWReconstruction (GlobalAdvantage f m ε) (HasCircuitOfSize fbool s)` from the design and **only `bridgeRecon`**.
* **`hardFn_to_prgExists_bridgeYao_discharged`** — entry 316's `HardFunction → PRGExists`
  (`HardFor fbool s → ¬ GlobalAdvantage f m ε`) with `bridgeYao` discharged — only `bridgeRecon` and the irreducible
  hardness remain.

## Honest scope

This removes one of the two model-dependent bridges of entry 316: the Yao predictor-circuit realisation is now a *proved*
gate-level fact (entry 194's `Circ`/`SmallPredictor`), instantiated into the assembly.  `SmallPredictor D gidx` captures
the size overhead (`+3`, `D` referenced once) and the guess-and-correct *semantics*; it does **not** formalise `ACC⁰`
*membership* of the distinguisher `D` (its depth / gate-type constraints) — that is outside this gate-count bridge.  After
this, `HardFunction → PRGExists` rests on the single remaining bridge `bridgeRecon` (entry 322's target) plus the
irreducible hardness of the witness and the proved low-intersection design.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionBridgeYao

open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHybrid (GlobalAdvantage)
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYao (YaoNextBitPredictor)
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonYaoCircuit (SmallPredictor yaoCircuitEfficiency_discharge)
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonReconstruction (SmallCircuitForFAt ReconDesign)
open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHardness (HardFor HasCircuitOfSize)
open PallLean.Paper93.DeepMath.PathB.ACC0NWFromHardness (NWReconstruction)

/-- **`bridgeYao` discharged (PROVED).**  The probability-level Yao next-bit predictor yields the concrete small
predictor circuit `SmallPredictor D gidx` (size `≤ size D + 3`, computing the guess-and-correct rule) — exactly the
`YaoCircuitEfficiency` socket, proved by `yaoCircuitEfficiency_discharge` (entry 194).  This is the bridge
`bridgeYao : YaoNextBitPredictor f m ε → ComputesF` of entry 316, at `ComputesF := SmallPredictor D gidx`. -/
theorem bridgeYao_discharged {Nc : ℕ} (D : ACC0NisanWigdersonYaoCircuit.Circ Nc) (gidx : Fin Nc)
    (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) :
    YaoNextBitPredictor f m ε → SmallPredictor D gidx :=
  yaoCircuitEfficiency_discharge D gidx (YaoNextBitPredictor f m ε)

/-- **The NW reconstruction with `bridgeYao` discharged (PROVED).**  Entry 316's `nwReconstruction_assembled` at
`ComputesF := SmallPredictor D gidx`, with `bridgeYao` supplied by `bridgeYao_discharged` — so the only remaining bridge
is `bridgeRecon`.  Yields `NWReconstruction (GlobalAdvantage f m ε) (HasCircuitOfSize fbool s)`. -/
theorem nwReconstruction_bridgeYao_discharged
    {n : ℕ} (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (predictorSize numOther k s : ℕ) (r : Fin numOther → ℕ)
    {Nc : ℕ} (D : ACC0NisanWigdersonYaoCircuit.Circ Nc) (gidx : Fin Nc)
    (fbool : (Fin n → Bool) → Bool)
    (bridgeRecon : SmallCircuitForFAt (SmallPredictor D gidx)
        (predictorSize + ∑ j, Fintype.card (Fin (r j) → Bool))
        (predictorSize + numOther * 2 ^ k) → HasCircuitOfSize fbool s)
    (hdesign : ReconDesign numOther k r) :
    NWReconstruction (GlobalAdvantage f m ε) (HasCircuitOfSize fbool s) :=
  ACC0NWReconstructionAssembly.nwReconstruction_assembled f m ε hε predictorSize numOther k s r
    (SmallPredictor D gidx) fbool (bridgeYao_discharged D gidx f m ε) bridgeRecon hdesign

/-- **`HardFunction → PRGExists` with `bridgeYao` discharged (PROVED).**  Entry 316's `hardFn_to_prgExists_assembled`
at `ComputesF := SmallPredictor D gidx`, `bridgeYao` supplied — `HardFor fbool s → ¬ GlobalAdvantage f m ε` now rests on
only `bridgeRecon` plus the irreducible hardness and the proved design. -/
theorem hardFn_to_prgExists_bridgeYao_discharged
    {n : ℕ} (f : ℕ → ℝ) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (predictorSize numOther k s : ℕ) (r : Fin numOther → ℕ)
    {Nc : ℕ} (D : ACC0NisanWigdersonYaoCircuit.Circ Nc) (gidx : Fin Nc)
    (fbool : (Fin n → Bool) → Bool)
    (bridgeRecon : SmallCircuitForFAt (SmallPredictor D gidx)
        (predictorSize + ∑ j, Fintype.card (Fin (r j) → Bool))
        (predictorSize + numOther * 2 ^ k) → HasCircuitOfSize fbool s)
    (hdesign : ReconDesign numOther k r) :
    HardFor fbool s → ¬ GlobalAdvantage f m ε :=
  ACC0NWReconstructionAssembly.hardFn_to_prgExists_assembled f m ε hε predictorSize numOther k s r
    (SmallPredictor D gidx) fbool (bridgeYao_discharged D gidx f m ε) bridgeRecon hdesign

/-!
**`bridgeYao`, discharged.**  The Yao predictor-circuit realisation — the upstream of the two model-dependent bridges of
entry 316 — is now a *proved* gate-level fact (`bridgeYao_discharged`, from entry 194's explicit `Circ`/`SmallPredictor`),
instantiated into the NW reconstruction assembly (`nwReconstruction_bridgeYao_discharged`,
`hardFn_to_prgExists_bridgeYao_discharged`).  So `HardFunction → PRGExists` now rests on the single remaining bridge
`bridgeRecon` (entry 322), the irreducible hardness of the witness, and the proved low-intersection design.  The honest
caveat: `SmallPredictor` is a gate-count + semantics bridge, not a formalisation of `ACC⁰` membership of `D`.  Not faked,
not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionBridgeYao

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionBridgeYao.bridgeYao_discharged
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionBridgeYao.nwReconstruction_bridgeYao_discharged
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NWReconstructionBridgeYao.hardFn_to_prgExists_bridgeYao_discharged
