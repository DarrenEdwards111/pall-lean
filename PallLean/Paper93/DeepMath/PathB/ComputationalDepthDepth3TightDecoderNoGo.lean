import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverStreamSat

/-!
# The tight falsifying-ρ decoder: candidate, budget, one-step no-go (branch only)

A genuine attempt at the one open gate — recovering, for a *falsifying* `ρ`, the active-clause stream
from the public `(leaf, label)` **without** paying the live-sublist (`2^|cs|`) factor.  Following the
four-step plan:

**1. Candidate decoder.**  The forward simulation `recoverStream`: maintain a running state `τ`, at each
recorded position take `activeTerm cs τ`, read the literal there, set its variable to the leaf value,
recurse.  Started from the all-free state (`recoverStream_correct_sat`), this is the natural public
decoder.

**2. Label budget.**  The tight count needs the label in `PathLabel w s = Fin s → (Fin w × Bool)`,
i.e. **exactly `(position, bit)` per step** — `log(2w)` bits.  There is *no* room to record the active
clause's identity (that would cost `log|cs|` extra bits per step, blowing the base from `2w` to
`2w·|cs|`).  So the decoder must recover the active clause from `(leaf, position, bit)` alone.

**3. One-step soundness.**  `recoverStream_eq_sat` shows the simulation is sound *iff* the running state
agrees with the descent state on the falsification of every clause.  At **step 0** the running state is
all-free and the descent state is `ρ`, so agreement requires `ρ` to falsify nothing — exactly `hnf`.

**4. No-go for the candidate + the missing bit.**  We prove the all-free forward decoder *fails* at
step 0 for a falsifying `ρ`: `activeTerm cs (all-free) ≠ activeTerm cs ρ`.  The all-free state sees a
`ρ`-killed clause as live and picks it as the first active term, while the true descent skips it.  The
**missing bit** is `ρ`'s falsified-prefix: the leaf falsifies `ρ`-killed *and* path-killed clauses
(it cannot separate them), and the in-clause `position` carries no clause identity, so within the `2w`
per-step budget the first active clause is not determined by `(leaf, position, bit)` for falsifying `ρ`.

This is the precise wall: no *forward-simulation* decoder with an all-free (or any fixed `ρ`-independent)
base fixes step 0.  Håstad's tight lemma resolves it with a **different encoded restriction** — one that
falsifies the active terms in a pattern recoverable from the stars-data — which this `deepest-branch`
encoding does not provide.  Formalising that encoding is the remaining research.

Clean, no `sorry`, no `native_decide`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

/-- Decidable equality on clauses (single `List` field), for the concrete no-go. -/
local instance : DecidableEq (Clause 2) :=
  fun a b => decidable_of_iff (a.lits = b.lits) (by cases a; cases b; simp)

/-- The counterexample DNF: two single-literal terms `x₀` and `x₁`. -/
def cexCs : List (Clause 2) := [⟨[Rung4Literal.pos 0]⟩, ⟨[Rung4Literal.pos 1]⟩]

/-- The counterexample restriction: `x₀ ↦ false` (falsifying the first term), `x₁` free. -/
def cexRho : Fin 2 → Option Bool := ![some false, none]

/-- `cexRho` genuinely **falsifies** the first clause — it is a falsifying restriction. -/
theorem cex_falsifies :
    SwitchingCounting.termFalsified cexRho ⟨[Rung4Literal.pos 0]⟩ = true := by decide

/-- **One-step no-go for the all-free forward decoder.**  For the falsifying `cexRho`, the all-free
running state and the descent state `ρ` disagree on the first active clause: the all-free state picks
`x₀` (which it sees as live), but `ρ` has killed `x₀` and the descent picks `x₁`.  So any decoder that
computes the step-0 active clause as `activeTerm cs (all-free)` is unsound on falsifying `ρ`. -/
theorem allfree_step0_fails :
    SwitchingCounting.activeTerm cexCs (fun _ => none)
      ≠ SwitchingCounting.activeTerm cexCs cexRho := by decide

/-- The two active clauses are genuinely different (`x₀` vs `x₁`): the all-free decoder recovers `x₀`,
the truth is `x₁`. -/
theorem allfree_step0_values :
    SwitchingCounting.activeTerm cexCs (fun _ => none) = some ⟨[Rung4Literal.pos 0]⟩
    ∧ SwitchingCounting.activeTerm cexCs cexRho = some ⟨[Rung4Literal.pos 1]⟩ := by
  decide

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.allfree_step0_fails
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.allfree_step0_values
