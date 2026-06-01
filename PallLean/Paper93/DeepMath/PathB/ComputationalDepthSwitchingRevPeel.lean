import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDecodeStep

/-!
# The reverse-peel fold: peeling the path's variables recovers `ρ`

**STATUS: REAL.  THE FOLD MECHANICS / PREFIX INVARIANT FOR THE DECODER.**

Iterating the per-step inverse (`freeOn_actStep_recover`) gives the decoder's fold:
starting from the fully-fixed end state `actPath cs ρ s` and un-fixing the path's
selected variables in reverse order recovers `ρ` exactly.

* `revPeel τ vs`: un-fix each variable of `vs` in turn, starting from `τ`;
* `pathVarsRev cs ρ s`: the path's selected variables in reverse fixing order
  `[v_{s-1}, …, v_0]` (skipping stalled steps);
* `revPeel_pathVarsRev`: `revPeel (actPath cs ρ s) (pathVarsRev cs ρ s) = ρ`.

This is the "maintain `decodedState = σ_i`" prefix invariant: the fold is proved
correct against the per-step inverse.  The only remaining content is that the
`(2w)^s` label *determines* `pathVarsRev` (recompute the active clause at each
reverse step — stable within a clause, advancing at the length-1 boundary — and read
the clause-literal index off the label).  That index recovery is the isolated gate.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Un-fix each variable of `vs` in turn, starting from `τ`. -/
def revPeel (τ : Restriction n) (vs : List (Fin n)) : Restriction n :=
  vs.foldl (fun ρ v => freeOn ρ {v}) τ

@[simp] theorem revPeel_nil (τ : Restriction n) : revPeel τ [] = τ := rfl

theorem revPeel_cons (τ : Restriction n) (v : Fin n) (vs : List (Fin n)) :
    revPeel τ (v :: vs) = revPeel (freeOn τ {v}) vs := by
  simp [revPeel]

/-- The path's selected variables in reverse fixing order: `[v_{s-1}, …, v_0]`,
skipping any stalled step (where the path has no active literal). -/
def pathVarsRev (cs : List (Clause n)) (ρ : Restriction n) : ℕ → List (Fin n)
  | 0 => []
  | k + 1 =>
    match activeLit cs (actPath cs ρ k) with
    | none => pathVarsRev cs ρ k
    | some ℓ => litVar ℓ :: pathVarsRev cs ρ k

/-- **Prefix invariant / fold correctness.**  Peeling the path's variables in
reverse, starting from the end state, recovers `ρ`. -/
theorem revPeel_pathVarsRev (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    revPeel (actPath cs ρ s) (pathVarsRev cs ρ s) = ρ := by
  induction s with
  | zero => simp [pathVarsRev, actPath]
  | succ k ih =>
    have hpath : actPath cs ρ (k + 1) = actStep cs (actPath cs ρ k) := rfl
    cases h : activeLit cs (actPath cs ρ k) with
    | none =>
      have hpvr : pathVarsRev cs ρ (k + 1) = pathVarsRev cs ρ k := by
        simp only [pathVarsRev, h]
      have hstep : actStep cs (actPath cs ρ k) = actPath cs ρ k := by rw [actStep, h]
      rw [hpvr, hpath, hstep]; exact ih
    | some ℓ =>
      have hpvr : pathVarsRev cs ρ (k + 1) = litVar ℓ :: pathVarsRev cs ρ k := by
        simp only [pathVarsRev, h]
      have hrec : freeOn (actPath cs ρ (k + 1)) {litVar ℓ} = actPath cs ρ k := by
        rw [hpath]; exact freeOn_actStep_recover h
      rw [hpvr, revPeel_cons, hrec]; exact ih

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.revPeel_pathVarsRev
