import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReplayPath

/-!
# Foundations for active-clause identification: fix-stability and the falsified-set characterization

Identifying the active clause `T_k` at the end-state `replayPath cs ρ s` is the genuine Håstad
research core.  This file proves the structural invariants any such identification must rest on, and
pins down precisely why the naive approach fails for general (shared-variable) clauses.

## Fix-stability (the replay only *adds* fixings)

Each replay step `falFix`es a *free* variable (the active literal lies on a free coordinate), so it
never overwrites an already-fixed value:

* `replayStep_fixed_stable` — `σ v = some b ⟹ replayStep cs σ v = some b`;
* `replayPath_fixed_stable` — fixings persist for the whole path;
* `replayPath_add` — `replayPath cs (replayPath cs ρ m) k = replayPath cs ρ (m+k)` (path
  composition).

This is the clean basis for monotonicity (a value, once fixed, stays) underneath
`termFalsified_replayPath_of` and any reconstruction.

## What the end-state reveals (the ⊆/⟸ direction)

* `termFalsified_of_active_lit_mem` — **any clause containing an active literal `ℓ_j` (`j < s`) is
  falsified at the end-state.**  Proved cleanly from `replayStep_falsifies` + monotonicity + path
  composition.

## The honest open core (the ⟹ direction and the sequence)

The converse — *which* falsified clause is the active clause `T_k` — is **not** discharged, and is
**not** faked.  Under "ρ falsifies no term", a clause is falsified at the end iff it *contains some
active literal* `ℓ_j` (the ⟹ direction needs that invariant).  With **shared variables/literals**
many non-active clauses contain an `ℓ_j` and so are falsified — the falsified set strictly
over-counts the active sequence `{T_0,…,T_{s-1}}`.  Recovering the *active* sequence therefore needs
Håstad's forward reconstruction (process clauses in order, undo by the advice), the genuine research
core.  For the **read-once** case (each variable in ≤ 1 clause) the over-counting collapses — a
falsified clause's false literal pins its unique clause — and the identification is clean; that
tractable special case rests directly on the lemmas here.  No identification of `T_k` from the
end-state is asserted in general.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Fix-stability, one step.**  A replay step fixes only a *free* variable, so it never changes an
already-fixed value. -/
theorem replayStep_fixed_stable {cs : List (Clause n)} {σ : Restriction n} {v : Fin n} {b : Bool}
    (h : σ v = some b) : replayStep cs σ v = some b := by
  rw [replayStep]
  cases ha : activeTermLit cs σ with
  | none => exact h
  | some ℓ =>
    have hfree : σ (litVar ℓ) = none := by
      have hf := activeTermLit_free ha
      rw [litFree_var] at hf
      exact Option.isNone_iff_eq_none.mp hf
    have hne : v ≠ litVar ℓ := by
      intro he; rw [he, hfree] at h; exact absurd h (by simp)
    show falFix σ ℓ v = some b
    rw [falFix_eq_outside σ ℓ hne]; exact h

/-- **Fix-stability along the path.**  Once a coordinate is fixed, it keeps its value forever. -/
theorem replayPath_fixed_stable {cs : List (Clause n)} {ρ : Restriction n} {v : Fin n} {b : Bool}
    (k : ℕ) : ∀ j, replayPath cs ρ k v = some b → replayPath cs ρ (k + j) v = some b := by
  intro j
  induction j with
  | zero => intro h; exact h
  | succ j ih =>
    intro h
    rw [show k + (j + 1) = (k + j) + 1 from by omega, replayPath]
    exact replayStep_fixed_stable (ih h)

/-- **Path composition.**  Running `k` more steps from `replayPath cs ρ m` is `replayPath cs ρ (m+k)`. -/
theorem replayPath_add (cs : List (Clause n)) (ρ : Restriction n) (m k : ℕ) :
    replayPath cs (replayPath cs ρ m) k = replayPath cs ρ (m + k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [replayPath, ih, Nat.add_succ, replayPath]

/-- **The end-state falsifies every clause containing an active literal.**  If at step `j < s` the
active literal is `ℓ` and `ℓ ∈ C`, then `C` is falsified at the end-state `replayPath cs ρ s`.  (The
⟸ direction of the falsified-set characterization — clean, no global invariant needed.) -/
theorem termFalsified_of_active_lit_mem {cs : List (Clause n)} {ρ : Restriction n} {j s : ℕ}
    {ℓ : Rung4Literal n} {C : Clause n} (hj : j < s)
    (h : activeTermLit cs (replayPath cs ρ j) = some ℓ) (hmem : ℓ ∈ C.lits) :
    termFalsified (replayPath cs ρ s) C = true := by
  have h1 : termFalsified (replayPath cs ρ (j + 1)) C = true := by
    rw [replayPath]; exact replayStep_falsifies h hmem
  have h2 := termFalsified_replayPath_of (cs := cs) (σ := replayPath cs ρ (j + 1)) (s - (j + 1)) h1
  rwa [replayPath_add, show (j + 1) + (s - (j + 1)) = s from by omega] at h2

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replayPath_fixed_stable
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.termFalsified_of_active_lit_mem
