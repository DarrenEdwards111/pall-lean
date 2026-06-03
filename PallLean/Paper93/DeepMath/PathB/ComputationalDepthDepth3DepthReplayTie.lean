import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReplayPath

/-!
# Tying `canonicalDT` depth to the canonical path length `s`

This file makes precise the relationship between the canonical decision tree `canonicalDT`
(the var-by-var stop-on-satisfied tree, whose depth is what the gate-2 refutation consumes) and the
**replay path** of the switching count (`replayStep`/`replayPath`, the canonical all-falsify path
the `(2w)^s` encoding lives on).

**The structural identity.**  `canonicalDT` queries `litVar ℓ` for `ℓ = (freeLits σ (activeTerm)).head?`
— which is exactly `activeTermLit cs σ`, the literal `replayStep` falsifies.  And
`falFix σ ℓ = fixVar σ (litVar ℓ) (falValue ℓ)`, so:

* `replayStep_eq_fixVar` — one replay step *is* the canonical tree's branch step (fixing the pivot
  to its falsifying value);
* `canonicalDT_branch` — at a non-satisfied, active node, `canonicalDT` branches on exactly that
  pivot.

So the replay path is literally the all-falsify branch of `canonicalDT`.

**The provable tie (lower bound).**  `canonicalDT_depth_ge_replay`: if the canonical falsify-process
runs `s` steps without early satisfaction (no `anyTermSat` along the way, an active term at each
step), then `(canonicalDT cs fuel ρ).depth ≥ s`.  The replay path is a genuine length-`s` root-to-leaf
branch, so the tree is at least that deep.  This rigorously ties the count's path length `s` to the
tree depth.

**The honest open core (upper bound).**  The *converse* — `depth ≤ s` for a *good* restriction `ρ`,
i.e. the genuine Håstad quantitative bound `Pr_ρ[depth ≥ s] ≤ (cw)^s` — is **not** a corollary of
this structural tie and is **not** discharged here.  `canonicalDT.depth` is the *max over all
branches*, while the `(2w)^s` count and `replayStep` follow the single canonical path; bounding the
*worst* branch requires the per-step active-term decoder under mid-completion, isolated as `hdec` in
`SwitchingCounting.replay_switching_count`.  That decoder is the remaining research core; it is **not**
faked.  What this file adds is the rigorous structural bridge and the lower-bound direction, showing
exactly where the two canonical objects coincide and where the irreducible content sits.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **One replay step is a canonical branch step.**  Falsifying the active literal `ℓ` fixes
`litVar ℓ` to its falsifying value — exactly one of `canonicalDT`'s two children. -/
theorem replayStep_eq_fixVar {cs : List (Clause n)} {σ : Fin n → Option Bool} {ℓ : Rung4Literal n}
    (h : SwitchingCounting.activeTermLit cs σ = some ℓ) :
    SwitchingCounting.replayStep cs σ = fixVar σ (litVar ℓ) (SwitchingCounting.falValue ℓ) := by
  simp only [SwitchingCounting.replayStep, h, SwitchingCounting.falFix, fixVar]

/-- **`canonicalDT` branches on the active literal.**  At a non-satisfied node with an active term,
the canonical tree queries the pivot `litVar ℓ` and recurses on both fixings. -/
theorem canonicalDT_branch {cs : List (Clause n)} {σ : Fin n → Option Bool} {ℓ : Rung4Literal n}
    {fuel : ℕ} (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hatl : SwitchingCounting.activeTermLit cs σ = some ℓ) :
    canonicalDT cs (fuel + 1) σ = BoolDecisionTree.query (litVar ℓ)
      (canonicalDT cs fuel (fixVar σ (litVar ℓ) false))
      (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)) := by
  rw [canonicalDT]
  simp only [hany, Bool.false_eq_true, if_false]
  unfold SwitchingCounting.activeTermLit at hatl
  cases hT : SwitchingCounting.activeTerm cs σ with
  | none => rw [hT] at hatl; simp at hatl
  | some T => rw [hT] at hatl; simp only [hatl]

/-- The replay path started one step in equals the original path shifted by one. -/
theorem replayPath_succ_left (cs : List (Clause n)) (σ : Fin n → Option Bool) (k : ℕ) :
    SwitchingCounting.replayPath cs (SwitchingCounting.replayStep cs σ) k
      = SwitchingCounting.replayPath cs σ (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [SwitchingCounting.replayPath, SwitchingCounting.replayPath, ih]

/-- **The lower-bound tie.**  If the canonical falsify-process runs `s` steps without early
satisfaction (no satisfied term, an active term present at each step), then the canonical decision
tree has depth at least `s`: the replay path is a genuine length-`s` branch.  This ties the count's
path length `s` to `canonicalDT`'s depth (the converse upper bound is the open Håstad core). -/
theorem canonicalDT_depth_ge_replay (cs : List (Clause n)) :
    ∀ (s : ℕ) (ρ : Fin n → Option Bool) (fuel : ℕ), s ≤ fuel →
      (∀ i, i < s → SwitchingCounting.anyTermSat cs (SwitchingCounting.replayPath cs ρ i) = false ∧
        SwitchingCounting.activeTermLit cs (SwitchingCounting.replayPath cs ρ i) ≠ none) →
      s ≤ (canonicalDT cs fuel ρ).depth := by
  intro s
  induction s with
  | zero => intro ρ fuel _ _; exact Nat.zero_le _
  | succ s ih =>
    intro ρ fuel hfuel hcond
    obtain ⟨hany0, hne0⟩ := hcond 0 (Nat.succ_pos s)
    rw [show SwitchingCounting.replayPath cs ρ 0 = ρ from rfl] at hany0 hne0
    cases hℓ : SwitchingCounting.activeTermLit cs ρ with
    | none => exact absurd hℓ hne0
    | some ℓ =>
      obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [canonicalDT_branch hany0 hℓ, BoolDecisionTree.depth]
      have hreplay : SwitchingCounting.replayStep cs ρ = fixVar ρ (litVar ℓ) (SwitchingCounting.falValue ℓ) :=
        replayStep_eq_fixVar hℓ
      have hcond' : ∀ i, i < s →
          SwitchingCounting.anyTermSat cs (SwitchingCounting.replayPath cs (SwitchingCounting.replayStep cs ρ) i) = false ∧
          SwitchingCounting.activeTermLit cs (SwitchingCounting.replayPath cs (SwitchingCounting.replayStep cs ρ) i) ≠ none := by
        intro i hi
        rw [replayPath_succ_left]
        exact hcond (i + 1) (by omega)
      have hih := ih (SwitchingCounting.replayStep cs ρ) fuel' (by omega) hcond'
      rw [hreplay] at hih
      cases hv : SwitchingCounting.falValue ℓ with
      | false =>
        rw [hv] at hih
        have hm : (canonicalDT cs fuel' (fixVar ρ (litVar ℓ) false)).depth ≤
            max (canonicalDT cs fuel' (fixVar ρ (litVar ℓ) false)).depth
                (canonicalDT cs fuel' (fixVar ρ (litVar ℓ) true)).depth := le_max_left _ _
        omega
      | true =>
        rw [hv] at hih
        have hm : (canonicalDT cs fuel' (fixVar ρ (litVar ℓ) true)).depth ≤
            max (canonicalDT cs fuel' (fixVar ρ (litVar ℓ) false)).depth
                (canonicalDT cs fuel' (fixVar ρ (litVar ℓ) true)).depth := le_max_right _ _
        omega

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.replayStep_eq_fixVar
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_branch
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_depth_ge_replay
