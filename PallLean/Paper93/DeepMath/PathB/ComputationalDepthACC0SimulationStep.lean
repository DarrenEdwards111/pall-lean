import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM

/-!
# The single-step simulation lemma — overhead accumulates linearly; physical single step socketed

The physical universal machine `U` simulating a machine `M` must show: one step of `M` is realised by a bounded number
`B` of `U`'s own steps, on an encoded configuration.  This file formalises that **single-step simulation property** and
proves everything that follows from it — the multi-step accumulation (`k` `M`-steps `↦ k·B` `U`-steps) and the
overhead-acceptance bound (`M` accepts within `t` `↦ U` accepts within `t·B`) — reducing the physical universal machine
to exactly its single-step realisation.

The setup: an abstract universal machine `U : NTM`, an encoding `enc : CConfig → U.Config` of `M`-configurations into
`U`-configurations, a per-step overhead `B`, and the hypotheses a physical `U` would discharge:

* **single step** — `concreteStep M c d → reachIn U B (enc c) (enc d)` (one `M`-step = `B` `U`-steps),
* **init/accept** — `enc` carries `M`'s initial/accepting configurations to `U`'s.

## What is proved (clean axioms, no `sorry`)

* **`sim_multi`** — the accumulation: `reachIn (toNTM M) k c d → reachIn U (k·B) (enc c) (enc d)` (induction on `k`
  via `reachIn_add`).
* **`sim_acceptsWithin`** — the overhead bound: `acceptsWithin (toNTM M) x t → acceptsWithin U x (t·B)`.

## Honest scope

The accumulation and overhead bound are *proved*; they show the simulation overhead is **linear in the number of
steps** (`t·B`), which is what `diag_in_big` ultimately needs.  The **single-step hypothesis itself** — that a physical
`U` realises one `M`-step in `B` steps preserving an explicit tape encoding — is the remaining deep socket: it requires
*constructing* `U` as an actual transition table that decodes `M`'s rule, finds the simulated head, and rewrites the
simulated tape.  That construction is the next step.  This does **not** build the physical universal machine.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SimulationStep

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn acceptsWithin reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig concreteStep toNTM toNTM_step)

/-- **The multi-step accumulation (proved): `k` steps of `M` are realised by `k·B` steps of `U`.**  Given the
single-step simulation property (`hstep`: one `M`-step `= B` `U`-steps on encoded configs), reachability lifts: by
induction on `k`, splitting `(k+1)·B = B + k·B` with `reachIn_add`. -/
theorem sim_multi (M : TMachine) (U : NTM) (enc : CConfig → U.Config) (B : ℕ)
    (hstep : ∀ c d, concreteStep M c d → reachIn U B (enc c) (enc d)) :
    ∀ (k : ℕ) (c d : CConfig), reachIn (toNTM M) k c d → reachIn U (k * B) (enc c) (enc d) := by
  intro k
  induction k with
  | zero =>
      intro c d h
      simp only [reachIn] at h
      simp only [Nat.zero_mul, reachIn]
      exact congrArg enc h
  | succ k ih =>
      intro c d h
      simp only [reachIn] at h
      obtain ⟨e, hce, hed⟩ := h
      have h1 : reachIn U B (enc c) (enc e) := hstep c e ((toNTM_step M c e).mp hce)
      have h2 : reachIn U (k * B) (enc e) (enc d) := ih e d hed
      have hsplit : (k + 1) * B = B + k * B := by ring
      rw [hsplit, reachIn_add]
      exact ⟨enc e, h1, h2⟩

/-- **The overhead-acceptance bound (proved): `M` accepts within `t` ⇒ `U` accepts within `t·B`.**  The single-step
simulation, with the encoding carrying initial and accepting configurations, gives a simulation whose overhead is
linear in the step count. -/
theorem sim_acceptsWithin (M : TMachine) (U : NTM) (enc : CConfig → U.Config) (B : ℕ)
    (hstep : ∀ c d, concreteStep M c d → reachIn U B (enc c) (enc d))
    (hinit : ∀ x, enc ((toNTM M).init x) = U.init x)
    (haccept : ∀ c, (toNTM M).accept c → U.accept (enc c))
    (x : List Bool) (t : ℕ) :
    acceptsWithin (toNTM M) x t → acceptsWithin U x (t * B) := by
  rintro ⟨k, hk, c, hrc, hac⟩
  refine ⟨k * B, Nat.mul_le_mul_right B hk, enc c, ?_, haccept c hac⟩
  rw [← hinit x]
  exact sim_multi M U enc B hstep k ((toNTM M).init x) c hrc

end PallLean.Paper93.DeepMath.PathB.ACC0SimulationStep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SimulationStep.sim_multi
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SimulationStep.sim_acceptsWithin
