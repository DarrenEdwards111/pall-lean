import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM

/-!
# The head-location sub-machine — head-movement locality proved, physical navigation socketed

The second sub-machine of the physical universal machine locates the simulated head on the encoded tape.  The simulated
head position is *explicit* in the configuration (`c.2.1`), and the key property the physical navigation relies on is
**locality**: a single step moves the head by at most one cell.  Hence after `k` steps the simulated head stays within
`[0, head₀ + k]` — bounding the tape region the physical machine must traverse (and so the per-step navigation cost).

## What is proved (clean axioms, no `sorry`)

* **`moveHead_le_succ`** — `moveHead h m ≤ h + 1`: any move advances the head by at most one cell.
* **`step_head_le`** — one step moves the head by at most one: `concreteStep M c d → d.2.1 ≤ c.2.1 + 1`.
* **`reachIn_head_le`** — `k` steps move the head by at most `k`: `reachIn (toNTM M) k c d → d.2.1 ≤ c.2.1 + k`.
  The simulated head stays within `head₀ + k` after `k` steps — the bounded tape region.

## Honest scope

The head-movement *locality* — and hence the bounded tape region (`head₀ + k` after `k` steps) — is proved; this is
what makes the physical head-location traversal cost `O(k)` per step.  Realising the navigation as `U`-transitions that
move `U`'s head to the simulated cell on the `encodeTape` layout is the socket.  This does **not** build the physical
sub-machine.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0HeadLocation

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine CConfig moveHead applyTrans concreteStep toNTM toNTM_step)

/-- **Head movement is local (proved): `moveHead h m ≤ h + 1`.** -/
theorem moveHead_le_succ (h : ℕ) (m : Fin 3) : moveHead h m ≤ h + 1 := by
  unfold moveHead
  split_ifs <;> omega

/-- **One step moves the head by at most one (proved): `concreteStep M c d → d.2.1 ≤ c.2.1 + 1`.** -/
theorem step_head_le (M : TMachine) (c d : CConfig) (h : concreteStep M c d) :
    d.2.1 ≤ c.2.1 + 1 := by
  obtain ⟨t, _, _, hd⟩ := h
  rw [hd]
  simp only [applyTrans]
  exact moveHead_le_succ c.2.1 t.2.2.2

/-- **`k` steps move the head by at most `k` (proved): `reachIn (toNTM M) k c d → d.2.1 ≤ c.2.1 + k`.**  The simulated
head stays within `head₀ + k` after `k` steps — the bounded tape region the physical head-location sub-machine
traverses. -/
theorem reachIn_head_le (M : TMachine) :
    ∀ (k : ℕ) (c d : CConfig), reachIn (toNTM M) k c d → d.2.1 ≤ c.2.1 + k := by
  intro k
  induction k with
  | zero =>
      intro c d h
      simp only [reachIn] at h
      subst h
      simp
  | succ k ih =>
      intro c d h
      simp only [reachIn] at h
      obtain ⟨e, hce, hed⟩ := h
      have h1 : e.2.1 ≤ c.2.1 + 1 := step_head_le M c e ((toNTM_step M c e).mp hce)
      have h2 : d.2.1 ≤ e.2.1 + k := ih e d hed
      omega

end PallLean.Paper93.DeepMath.PathB.ACC0HeadLocation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0HeadLocation.moveHead_le_succ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0HeadLocation.step_head_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0HeadLocation.reachIn_head_le
