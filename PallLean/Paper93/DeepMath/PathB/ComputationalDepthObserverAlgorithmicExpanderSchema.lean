import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverAlgorithmicSchema

/-!
# Three engines wired: God-Move boundary → expander amplification → faster SAT → Williams

`ComputationalDepthObserverAlgorithmicSchema.lean` proved engine 1 (low boundary ⇒ sub-brute-force SAT via DP
over boundary states) and the Williams conditional.  This file wires **all three engines** into one
conditional schema, modular and explicit, per the `p vs np1` expander-amplifier intuition:

1. **Observer → algorithm** (engine 1, *proved* core): a low-boundary decomposition admits dynamic
   programming over its `2^B` boundary states, solving SAT faster than brute force
   (`ObserverAlgorithmic.dpSat_beats_bruteforce`).
2. **Expander amplification** (engine 2, *explicit hypothesis*): the Ramanujan/expander geometry spreads local
   constraints globally, so cheap decompositions cannot isolate the hard part — a low-boundary observer either
   collapses distinguishable continuations or pays boundary proportional to the expansion frontier.  Modelled
   as `ExpanderAmplifies → (a faithful low-boundary decomposition)`.
3. **Williams** (engine 3, *explicit hypothesis*): a nontrivial SAT algorithm for a class yields a lower
   bound — `FastSAT → (NEXP ⊄ C)` (Williams diagonalization), not reproved.

The wiring is `williams ∘ algorithm ∘ amplify`.  The only *proved* component is the algorithm engine; expander
and Williams are explicit hypotheses, isolating exactly the two deep/open inputs.

## Honest status

* Engine 1 (DP bound): **proved**.
* Engine 2 (expander amplification): **explicit hypothesis** — the `p vs np1` expander geometry; not reproved
  (the proved instances of "pay the frontier" are the `ForcingFamily` results §12, expander-Tseitin §8).
* Engine 3 (Williams): **explicit hypothesis** — the deep `#SAT`-algorithm-to-lower-bound theorem.
* `NEXP ⊄ ACC⁰` / `NP ⊄ ACC⁰`: **open**.  Nothing here closes them.  The value is a clean, modular conditional
  that names the two deep inputs and proves the algorithmic glue — the integration the intuition asked for,
  without overclaiming.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmicExpander

open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic

/-- **The three-engine schema (fully conditional).**  Wires engine 2 → engine 1 → engine 3:

* `amplify : ExpanderAmplifies → LowBoundaryDecomp` — expander geometry yields a faithful low-boundary
  decomposition (engine 2);
* `algorithm : LowBoundaryDecomp → FastSAT` — DP over boundary states (engine 1);
* `williams : FastSAT → LowerBound` — Williams diagonalization (engine 3);

given the expander hypothesis, the lower bound follows.  All three are explicit; only engine 1 is proved
elsewhere. -/
theorem expander_observer_williams_schema
    {ExpanderAmplifies LowBoundaryDecomp FastSAT LowerBound : Prop}
    (amplify : ExpanderAmplifies → LowBoundaryDecomp)
    (algorithm : LowBoundaryDecomp → FastSAT)
    (williams : FastSAT → LowerBound)
    (hExpander : ExpanderAmplifies) :
    LowerBound :=
  williams (algorithm (amplify hExpander))

/-- **The same with engine 1 discharged by the proved DP bound.**  The expander amplifier supplies a concrete
`LowBoundaryInstance`; engine 1 is the *proved* `LowBoundaryInstance.fast` (DP beats brute force); Williams
converts "DP beats brute force" into the lower bound.  So only **engine 2 (expander)** and **engine 3
(Williams)** remain as explicit hypotheses — engine 1 is no longer assumed. -/
theorem expander_williams_with_proved_algorithm
    {ExpanderAmplifies LowerBound : Prop}
    (amplify : ExpanderAmplifies → LowBoundaryInstance)
    (williams : ∀ I : LowBoundaryInstance,
      (dpSatTime I.stages I.boundary < bruteForceTime I.n) → LowerBound)
    (hExpander : ExpanderAmplifies) :
    LowerBound :=
  let I := amplify hExpander
  williams I I.fast

end PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmicExpander

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmicExpander.expander_observer_williams_schema
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmicExpander.expander_williams_with_proved_algorithm
