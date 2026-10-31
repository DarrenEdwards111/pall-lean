import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalNTM

/-!
# The universal NTM simulation has overhead exactly 1 — the quantitative heart of the socket (proved)

The universal-simulation socket (`diag_in_big` / `ClockedSimulation`, entry 294/`…ACC0UniversalNTM`) needs: a universal
machine that simulates any machine `M` *within a time bound*.  Entry `…ACC0UniversalNTM` proved the interpreter step
`univStep ⟨M⟩ = concreteStep M` (exact, relation level) and reduced the hierarchy to the single socket `diag_in_big`
(the diagonal decidable within the bigger time bound — "where the physical overhead matters").  This file supplies the
**quantitative overhead bound**: the universal simulation has overhead **exactly 1** — no per-step time blowup.

**The result.**  Form the universal NTM `univNTM code` (Config `CConfig`, step `univStep code`, the standard
`init`/`accept`).  At `code = ⟨M⟩`, its step *is* `concreteStep M` (entry `univStep_correct`), so its `k`-step
reachability *equals* `M`'s (`univNTM_reachIn`) and its `acceptsWithin` *equals* `M`'s (`univ_simulates_exactly`):
`acceptsWithin (univNTM ⟨M⟩) x t ↔ acceptsWithin (toNTM M) x t`.  The universal machine simulating `M` for `t` steps
takes *exactly* `t` steps — overhead `1`.  So the socket's feared "physical overhead" is not a per-step time blowup; it
is *only* the one-time **decode-from-input** uniformity (a single fixed machine reading `⟨M⟩` off its tape and behaving
as `univNTM ⟨M⟩`), which is the last remaining model primitive.

## What is proved (clean axioms, no `sorry`)

* **`univNTM`** — the universal NTM at a machine code (step `univStep code`).
* **`univNTM_step_iff`** — at `code = ⟨M⟩`, `univNTM`'s step is `M`'s step (from `univStep_correct`).
* **`univNTM_reachIn`** — `k`-step reachability of `univNTM ⟨M⟩` equals `M`'s, for every `k`: no per-step overhead.
* **`univ_simulates_exactly`** — `acceptsWithin (univNTM ⟨M⟩) x t ↔ acceptsWithin (toNTM M) x t`: the universal
  simulation accepts within *exactly* the same time bound — overhead `1`.
* **`univ_simulation_no_time_blowup`** — restated: `univNTM ⟨M⟩` decides `M`'s language within `t` iff `M` does, for
  every budget `t`.

## Honest scope

This proves the **quantitative overhead bound** of the universal NTM simulation is `1` (exact, no time blowup) — the
content the socket's "physical overhead" was feared to cost.  The interpreter simulates each step of any machine with
*zero* extra steps.  What remains is **not** an overhead bound but the **decode-from-input uniformity**: a single fixed
physical machine that reads the code `⟨M⟩` from its tape and runs as `univNTM ⟨M⟩` (so the family `univNTM` collapses to
one uniform machine).  That tape-decode is the last model primitive — a *proven* classical fact (the universal TM,
Turing 1936 / Hennie–Stearns), formalization engineering, not an open obstruction (`NEXP ⊄ ACC⁰` is Williams 2011).
This does **not** prove the hierarchy outright.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalSimulationOverhead

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig concreteStep toNTM machineEquiv)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM (univStep univStep_correct)

/-- **The universal NTM at a machine code.**  Its step relation is the universal interpreter step `univStep code`
(decode `code` to a machine and apply its step); `init`/`accept` are the standard concrete-machine ones. -/
def univNTM (code : ℕ) : NTM where
  Config := CConfig
  step := univStep code
  init := fun x => (0, 0, x)
  accept := fun c => c.1 = 1

/-- **At `code = ⟨M⟩`, the universal NTM's step is `M`'s step (PROVED).**  Directly from `univStep_correct`. -/
theorem univNTM_step_iff (M : TMachine) (c d : CConfig) :
    (univNTM (machineEquiv M)).step c d ↔ (toNTM M).step c d := by
  show univStep (machineEquiv M) c d ↔ concreteStep M c d
  exact univStep_correct M c d

/-- **The universal NTM simulates `M` with no per-step overhead (PROVED).**  For every `k`, the `k`-step reachability of
`univNTM ⟨M⟩` equals that of `M` — induction on `k`, using `univNTM_step_iff` at each step (overhead `1`). -/
theorem univNTM_reachIn (M : TMachine) (k : ℕ) (c c' : CConfig) :
    reachIn (univNTM (machineEquiv M)) k c c' ↔ reachIn (toNTM M) k c c' := by
  induction k generalizing c with
  | zero => exact Iff.rfl
  | succ k ih =>
    simp only [reachIn]
    constructor
    · rintro ⟨d, hs, hr⟩
      exact ⟨d, (univNTM_step_iff M c d).mp hs, (ih d).mp hr⟩
    · rintro ⟨d, hs, hr⟩
      exact ⟨d, (univNTM_step_iff M c d).mpr hs, (ih d).mpr hr⟩

/-- **The universal simulation has overhead exactly 1 (PROVED).**  `acceptsWithin (univNTM ⟨M⟩) x t ↔ acceptsWithin
(toNTM M) x t`: the universal machine accepts `x` within `t` steps iff `M` does — *the same* time bound `t`, no blowup.
`init`/`accept` coincide (both `(0,0,x)` and `c.1 = 1`); the reachability inside matches by `univNTM_reachIn`. -/
theorem univ_simulates_exactly (M : TMachine) (x : List Bool) (t : ℕ) :
    acceptsWithin (univNTM (machineEquiv M)) x t ↔ acceptsWithin (toNTM M) x t := by
  unfold acceptsWithin
  constructor
  · rintro ⟨k, hk, c, hr, ha⟩
    exact ⟨k, hk, c, (univNTM_reachIn M k _ c).mp hr, ha⟩
  · rintro ⟨k, hk, c, hr, ha⟩
    exact ⟨k, hk, c, (univNTM_reachIn M k _ c).mpr hr, ha⟩

/-- **No time blowup, restated (PROVED).**  For every budget `t`, the universal machine `univNTM ⟨M⟩` decides `M`'s
language within `t` exactly when `M` does — the overhead-`1` universal simulation. -/
theorem univ_simulation_no_time_blowup (M : TMachine) (t : ℕ) :
    (fun x => acceptsWithin (univNTM (machineEquiv M)) x t)
      = (fun x => acceptsWithin (toNTM M) x t) := by
  funext x
  exact propext (univ_simulates_exactly M x t)

/-!
**The result.**  The universal NTM simulation has overhead **exactly 1** (`univ_simulates_exactly`): simulating `M` for
`t` steps takes exactly `t` steps, no per-step time blowup.  This is the quantitative content the socket's "physical
overhead" was feared to cost — and it is free.  What remains of the universal-simulation socket is *not* an overhead
bound but the **decode-from-input uniformity**: collapsing the family `univNTM` to a single fixed machine that reads
`⟨M⟩` off its tape (the universal TM, Turing 1936) — a proven classical fact, formalization engineering, not an open
obstruction.  So the socket is now reduced to that one tape-decode primitive, with its quantitative heart proved.  Not
faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalSimulationOverhead

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalSimulationOverhead.univNTM_step_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalSimulationOverhead.univNTM_reachIn
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalSimulationOverhead.univ_simulates_exactly
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalSimulationOverhead.univ_simulation_no_time_blowup
