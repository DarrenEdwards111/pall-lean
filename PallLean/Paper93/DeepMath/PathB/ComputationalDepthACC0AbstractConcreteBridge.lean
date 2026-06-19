import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM

/-!
# Entry 333 — the abstract-NTM → concrete-TMachine bridge: simulation transfers acceptance (proved)

Entry 332 exposed the gap blocking real phase instantiation: the universal simulator (entries 296–298) is built as an
*abstract* `NTM` (arbitrary `Config`, relational `step`), but the routing-table assembly (329–332) runs on *concrete*
`TMachine`s (`CConfig`, finite transition lists).  This file proves the **general bridge**: if a concrete `TMachine`
*step-simulates* an abstract `NTM` — each abstract step realised by `cost` concrete steps, with inits and accept states
matched — then it **transfers acceptance** with a `× cost` time blowup.

This is the precise interface a concrete universal Turing machine plugs into: build the concrete table `M` and a
simulation `Realizes physU M φ cost`, and acceptance of the abstract universal NTM transfers to `M` automatically.

**The simulation.**  `Realizes A M φ cost` packages a config map `φ : A.Config → CConfig` with: each abstract step
`A.step c d` is a `cost`-step run of `toNTM M` from `φ c` to `φ d`; abstract accept configs map to concrete accept
(state `1`); and `φ (A.init x) = (toNTM M).init x`.

## What is proved (clean axioms, no `sorry`)

* **`Realizes`** — the step-simulation interface (step / accept / init compatibility).
* **`reachIn_realize`** (PROVED) — a `k`-step abstract run becomes a `k * cost`-step concrete run (`reachIn_add` block
  concatenation, induction on `k`).
* **`acceptsWithin_realize`** (PROVED) — `acceptsWithin A x t → acceptsWithin (toNTM M) x (t * cost)`: the bridge,
  acceptance transferred with a `× cost` time blowup.

## Honest scope

This proves the **general abstract→concrete bridge mechanism**: any concrete `TMachine` that step-simulates an abstract
`NTM` (the `Realizes` interface) transfers acceptance with controlled time blowup.  It reduces the routing-decider's
remaining gap (entry 332) to a single named construction: exhibiting `Realizes physU M φ cost` for a concrete `TMachine`
`M` — i.e. **building the universal Turing machine as an actual transition table** and proving it simulates the abstract
universal NTM (296–298).  That universal-TM table is a substantial classical construction, **not built here and not
faked**.  With this bridge proved, it is the lone remaining piece for the concrete universal-simulation phase (plus the
`f`-timing).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AbstractConcreteBridge

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn reachIn_add acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig toNTM)

/-- **The step-simulation interface.**  A concrete `TMachine` `M`, via the config map `φ`, simulates the abstract `NTM`
`A`: each abstract step is `cost` concrete steps, accept configs map to concrete accept (state `1`), and inits
correspond. -/
structure Realizes (A : NTM) (M : TMachine) (φ : A.Config → CConfig) (cost : ℕ) : Prop where
  step : ∀ c d, A.step c d → reachIn (toNTM M) cost (φ c) (φ d)
  accept : ∀ c, A.accept c → (φ c).1 = 1
  init : ∀ x, φ (A.init x) = (toNTM M).init x

/-- **A whole run is simulated with `× cost` blowup (PROVED).**  A `k`-step run of `A` becomes a `k * cost`-step run of
`toNTM M`, by concatenating the per-step `cost`-blocks (`reachIn_add`), induction on `k`. -/
theorem reachIn_realize {A : NTM} {M : TMachine} {φ : A.Config → CConfig} {cost : ℕ}
    (hstep : ∀ c d, A.step c d → reachIn (toNTM M) cost (φ c) (φ d)) :
    ∀ (k : ℕ) (c d : A.Config), reachIn A k c d → reachIn (toNTM M) (k * cost) (φ c) (φ d) := by
  intro k
  induction k with
  | zero => intro c d hr; rw [Nat.zero_mul]; exact congrArg φ hr
  | succ k ih =>
      intro c d hr
      obtain ⟨e, hs, hrest⟩ := hr
      have hcomp : reachIn (toNTM M) (cost + k * cost) (φ c) (φ d) :=
        (reachIn_add (toNTM M) cost (k * cost) (φ c) (φ d)).mpr ⟨φ e, hstep c e hs, ih e d hrest⟩
      rwa [show (k + 1) * cost = cost + k * cost from by ring]

/-- **The bridge: simulation transfers acceptance (PROVED).**  If `M` realizes `A` with per-step cost `cost`, then
`acceptsWithin A x t` gives `acceptsWithin (toNTM M) x (t * cost)` — the abstract universal NTM's acceptance carried to
the concrete `TMachine`, with a `× cost` time blowup. -/
theorem acceptsWithin_realize {A : NTM} {M : TMachine} {φ : A.Config → CConfig} {cost : ℕ}
    (h : Realizes A M φ cost) {x : List Bool} {t : ℕ} (ha : acceptsWithin A x t) :
    acceptsWithin (toNTM M) x (t * cost) := by
  obtain ⟨k, hk, c, hr, haccc⟩ := ha
  refine ⟨k * cost, by gcongr, φ c, ?_, h.accept c haccc⟩
  rw [← h.init x]
  exact reachIn_realize h.step k (A.init x) c hr

/-!
**The bridge, proved.**  `Realizes` packages a step-by-step simulation of an abstract `NTM` by a concrete `TMachine`;
`reachIn_realize` lifts whole runs with `× cost` blowup, and `acceptsWithin_realize` transfers acceptance.  So the
abstract universal simulator (296–298) reaches the concrete routing table *through this bridge* — the lone remaining
construction is a concrete universal Turing machine `M` with `Realizes physU M φ cost` (the universal-TM transition
table), not built here.  With the bridge proved, that table (plus the `f`-timing) is all that stands between the routing
decider and the concrete model.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0AbstractConcreteBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AbstractConcreteBridge.reachIn_realize
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AbstractConcreteBridge.acceptsWithin_realize
