import Mathlib.Data.Nat.Basic

/-!
# Pushing the transfer arrow: the whole wall is a single composition step

`TreeClearsWall` localized the entire P-vs-NP gap to one thing — the tree→DAG **transfer**: does the
DAG cost of the composite tower keep up with the tree's free doubling?  This file pushes on that arrow
by reducing the *global* transfer to a *single per-step* inequality, exactly the way KRW reduces a depth
lower bound to a one-round lemma.

The per-step condition is `cost_super`'s own inequality:

`PerStepDouble c :  ∀ d, 2 · c d ≤ c (d+1)`   — "each composition step at least doubles the DAG cost."

* **`telescopes` (proved)** — one step telescopes to exponential: `PerStepDouble c` and `1 ≤ c 0` give
  `2^d ≤ c d` for all `d`.  Proving the DAG doubles at a *single* step forces the superpoly DAG bound.
* **`dag_clears_of_perstep` (proved)** — hence the DAG clears every ceiling: `∀ U, ∃ d, U < c d`.  The
  transfer succeeds the moment the one-step lemma holds.
* **`collapse_is_local` (proved)** — the converse localization: if the DAG ever falls short of `2^d`,
  then per-step doubling **fails at some single step** `e` (`c (e+1) < 2 · c e`) — sharing beat doubling
  at one specific composition level.  Any collapse is local.

## What this buys

The transfer is no longer a statement about the whole `d`-fold tower — it is a statement about **one
composition step**.  `telescopes` says one step suffices; `collapse_is_local` says one failing step is
necessary for any collapse.  So the entire wall is the single inequality `2 · c d ≤ c (d+1)`: the
**one-step Uhlig / KRW no-sharing lemma**.

## Honest scope

The one-step inequality is **not proved here** — it is the open wall (`cost_super`, the KRW one-round
lemma), named as the socket.  What is proved is the *reduction*: the global superpoly transfer is
equivalent, up to this file's telescoping, to that one local step, and any failure of the transfer is
localized to a single step.  This sharpens where the difficulty lives — one composition step — and
crosses nothing.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TransferOneStep

/-- The **one-step no-sharing condition** = `cost_super`'s defining inequality: at every composition
level the DAG cost at least doubles.  This is the one-round Uhlig / KRW lemma, named. -/
def PerStepDouble (c : ℕ → ℕ) : Prop := ∀ d, 2 * c d ≤ c (d + 1)

/-- `n < 2^n` (proved, self-contained). -/
theorem lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- **One step telescopes to exponential (proved).**  If the DAG at least doubles at every single
composition step (`PerStepDouble`) and the base is nonempty, then `2^d ≤ c d` for all `d`: the one-step
no-sharing lemma forces the global superpoly DAG bound. -/
theorem telescopes (c : ℕ → ℕ) (hstep : PerStepDouble c) (hbase : 1 ≤ c 0) :
    ∀ d, 2 ^ d ≤ c d := by
  intro d
  induction d with
  | zero => rw [Nat.pow_zero]; exact hbase
  | succ d ih =>
    rw [Nat.pow_succ]
    calc 2 ^ d * 2 = 2 * 2 ^ d := Nat.mul_comm _ _
    _ ≤ 2 * c d := Nat.mul_le_mul (Nat.le_refl 2) ih
    _ ≤ c (d + 1) := hstep d

/-- **The transfer succeeds from one step (proved).**  Under the one-step no-sharing lemma, the DAG cost
clears every ceiling `U`: `∃ d, U < c d`.  The tree's superpoly bound has transferred to the DAG. -/
theorem dag_clears_of_perstep (c : ℕ → ℕ) (hstep : PerStepDouble c) (hbase : 1 ≤ c 0) (U : ℕ) :
    ∃ d, U < c d :=
  ⟨U + 1, lt_of_lt_of_le
      (lt_of_lt_of_le (Nat.lt_succ_self U) (Nat.le_of_lt (lt_two_pow_self (U + 1))))
      (telescopes c hstep hbase (U + 1))⟩

/-- **Any collapse is local (proved).**  If the DAG cost ever falls short of `2^d`, then per-step
doubling must fail at some single step `e` — sharing beat doubling at one specific composition level.
So the transfer cannot fail "globally": every failure is one local step. -/
theorem collapse_is_local (c : ℕ → ℕ) (hbase : 1 ≤ c 0) (d : ℕ) (hfail : c d < 2 ^ d) :
    ∃ e, c (e + 1) < 2 * c e := by
  by_contra h
  have hstep : PerStepDouble c := by
    intro e
    by_contra he
    exact h ⟨e, by omega⟩
  have hge := telescopes c hstep hbase d
  omega

end PallLean.Paper93.DeepMath.PathB.TransferOneStep

#print axioms PallLean.Paper93.DeepMath.PathB.TransferOneStep.telescopes
#print axioms PallLean.Paper93.DeepMath.PathB.TransferOneStep.dag_clears_of_perstep
#print axioms PallLean.Paper93.DeepMath.PathB.TransferOneStep.collapse_is_local
