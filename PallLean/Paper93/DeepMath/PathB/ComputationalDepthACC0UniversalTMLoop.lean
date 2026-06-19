import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMLookup

/-!
# Entry 337 — universal-TM-table build, brick 4: the simulation loop, sound (proved)

Brick 3 (entry 336) gave the verified single lookup-and-apply step (`applyLookup`, sound and complete w.r.t.
`concreteStep`).  Brick 4 iterates it into the **simulation loop** and proves the deterministic iteration is a genuine
run of the (nondeterministic) machine, with an accepting simulation yielding acceptance.

**The loop.**  `simIter M k c` runs the machine deterministically for `k` steps from `c` by repeatedly looking up and
applying the matching rule (returning `none` if no rule ever matches).  The key results: a successful `k`-step
simulation `simIter M k c = some d` is a `reachIn (toNTM M) k c d` (soundness — the deterministic execution is a valid
nondeterministic run), and an accepting simulation from the initial config gives `acceptsWithin`.

## What is proved (clean axioms, no `sorry`)

* **`simIter`** — the deterministic `k`-step simulation loop (iterate `applyLookup`).
* **`simIter_sound`** (PROVED) — `simIter M k c = some d → reachIn (toNTM M) k c d`: the simulation is a valid run.
* **`simIter_acceptsWithin`** (PROVED) — a `k`-step simulation from `(0,0,x)` reaching an accept state (`d.1 = 1`)
  gives `acceptsWithin (toNTM M) x k`.

## Honest scope

This proves the **simulation loop is sound**: iterating the verified lookup-and-apply step is a genuine run of the
machine, and an accepting simulation witnesses `acceptsWithin`.  Combined with bricks 1–3 this is the *logical* engine of
the universal machine's simulation cycle (traverse, look up, apply, repeat, detect accept), all verified at the
config/rule level.  What remains is the **bit-level realisation** — representing `simIter` as the run of one concrete
`TMachine` `U` over the encoded tape, and proving `Realizes physU U φ cost` (plus the `f`-timing).  That realisation is
the remaining low-level construction, built as verified bricks, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig toNTM concreteStep)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn acceptsWithin)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup (applyLookup applyLookup_sound)

/-- **The deterministic simulation loop.**  Run `M` for `k` steps from `c` by repeatedly looking up and applying the
matching rule; `none` if at some step no rule matches. -/
def simIter (M : TMachine) : ℕ → CConfig → Option CConfig
  | 0, c => some c
  | k + 1, c => (applyLookup M c).bind (simIter M k)

/-- **The simulation loop is a valid run (PROVED).**  A successful `k`-step simulation `simIter M k c = some d` is a
`reachIn (toNTM M) k c d` — the deterministic lookup-and-apply iteration is a genuine `k`-step run of the
nondeterministic machine.  By induction on `k`, each step via `applyLookup_sound` (brick 3). -/
theorem simIter_sound (M : TMachine) :
    ∀ (k : ℕ) (c d : CConfig), simIter M k c = some d → reachIn (toNTM M) k c d := by
  intro k
  induction k with
  | zero => intro c d h; simpa only [simIter, Option.some.injEq] using h
  | succ k ih =>
      intro c d h
      simp only [simIter, Option.bind_eq_some_iff] at h
      obtain ⟨c', hc', hd⟩ := h
      exact ⟨c', applyLookup_sound M c c' hc', ih c' d hd⟩

/-- **An accepting simulation witnesses acceptance (PROVED).**  If the `k`-step simulation from the initial config
`(0,0,x)` reaches an accept state (`d.1 = 1`), then `acceptsWithin (toNTM M) x k`. -/
theorem simIter_acceptsWithin (M : TMachine) (x : List Bool) (k : ℕ) (d : CConfig)
    (h : simIter M k (0, 0, x) = some d) (hacc : d.1 = 1) :
    acceptsWithin (toNTM M) x k :=
  ⟨k, le_refl k, d, simIter_sound M k (0, 0, x) d h, hacc⟩

/-!
**Brick 4, built.**  `simIter` is the deterministic simulation loop; `simIter_sound` proves it is a valid `reachIn` run
(each step the verified brick-3 lookup-and-apply), and `simIter_acceptsWithin` turns an accepting simulation into
`acceptsWithin`.  With bricks 1–3 this is the verified logical engine of the universal simulation cycle.  Remaining: the
bit-level realisation of `simIter` as one concrete `TMachine` `U` over the encoded tape, `Realizes physU U φ cost`, and
the `f`-timing — built as verified bricks, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop.simIter_sound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLoop.simIter_acceptsWithin
