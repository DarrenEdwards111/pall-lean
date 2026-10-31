import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# Rule-lookup, brick 15: seek left to a marker (`scanToTrueLeft`)

The counter-drives-pointer step of the lookup shuttles the head between two regions: decrement the state
counter (left), advance the table pointer (right), then **return** to the counter.  Brick 4's
`scanToTrue` seeks *right* to a marker; the return leg needs the mirror — seek *left* to a marker.  This
brick builds it: from the scanning state, step left over `false`s until the first `true`, halting on it.

To sidestep truncated `Nat` subtraction the invariant is parametrised by the marker position `m` and a
distance `n`: the head starts at `m + n` and walks down to `m`.

## What is proved

* **`scanToTrueLeft`** — a two-state machine (mirror of `scanToTrue`): `false` ⇒ step left, keep
  scanning; `true` ⇒ halt in place on the marker.  No writes.
* **`scanToTrueLeft_partial`** — for `i ≤ n`, after `i` steps the head is at `m + n - i`, still scanning.
* **`scanToTrueLeft_run`** — head starting at `m + n`, with the `n` cells above `m` `false` and cell `m`
  `true`, seeks left to the marker at `m` in `n + 1` steps, tape unchanged.

## Honest scope

The return-to-counter leg of the lookup shuttle.  What remains for `uStepOnTape`: couple this with the
counter loop (brick 14) and a right-advancing pointer into the counter-drives-pointer shuttle, then the
read symbol, the matched-rule write-back, and the reset-to-0 wrapper; then the lazy-delay diagonal.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineSeekLeft

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **The left marker-seek machine.**  Mirror of `scanToTrue`: in the scanning state, `false` ⇒ step
one cell left, keep scanning; `true` ⇒ halt in place on the marker.  No writes. -/
def scanToTrueLeft : Machine where
  State := Bool
  fin := inferInstance
  dec := inferInstance
  start := false
  halt := fun s => s
  δ := fun _ b => if b then (true, none, (2 : Move)) else (false, none, (0 : Move))
  accept := fun s => s

theorem scanToTrueLeft_step_false {c : Cfg scanToTrueLeft} (hs : c.st = false)
    (hb : c.tp.getD c.hd false = false) : step scanToTrueLeft c = ⟨false, c.hd - 1, c.tp⟩ := by
  have hstep : step scanToTrueLeft c
      = ⟨(scanToTrueLeft.δ c.st (c.tp.getD c.hd false)).1,
         moveHead c.hd (scanToTrueLeft.δ c.st (c.tp.getD c.hd false)).2.2,
         (match (scanToTrueLeft.δ c.st (c.tp.getD c.hd false)).2.1 with
           | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
    unfold step
    rw [show scanToTrueLeft.halt c.st = false from hs]
    rfl
  rw [hstep, hb]; rfl

theorem scanToTrueLeft_step_true {c : Cfg scanToTrueLeft} (hs : c.st = false)
    (hb : c.tp.getD c.hd false = true) : step scanToTrueLeft c = ⟨true, c.hd, c.tp⟩ := by
  have hstep : step scanToTrueLeft c
      = ⟨(scanToTrueLeft.δ c.st (c.tp.getD c.hd false)).1,
         moveHead c.hd (scanToTrueLeft.δ c.st (c.tp.getD c.hd false)).2.2,
         (match (scanToTrueLeft.δ c.st (c.tp.getD c.hd false)).2.1 with
           | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
    unfold step
    rw [show scanToTrueLeft.halt c.st = false from hs]
    rfl
  rw [hstep, hb]; rfl

/-- **The left-seek invariant (proved).**  For `i ≤ n`, after `i` steps the head is at `m + n - i`,
still scanning. -/
theorem scanToTrueLeft_partial (m n : ℕ) (c : Cfg scanToTrueLeft) (hstart : c.st = false)
    (hhd : c.hd = m + n) (hfalse : ∀ i, i < n → c.tp.getD (m + n - i) false = false) :
    ∀ i, i ≤ n → run scanToTrueLeft i c = ⟨false, m + n - i, c.tp⟩ := by
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨st, hd, tp⟩ := c
    subst hstart; subst hhd; rfl
  | succ i ih =>
    intro hle
    have hstep := scanToTrueLeft_step_false (c := ⟨false, m + n - i, c.tp⟩) rfl (hfalse i (by omega))
    rw [run_succ, ih (by omega), hstep]
    show (⟨false, m + n - i - 1, c.tp⟩ : Cfg scanToTrueLeft) = ⟨false, m + n - (i + 1), c.tp⟩
    rw [show m + n - i - 1 = m + n - (i + 1) from by omega]

/-- **The left seek is correct (proved).**  Head starting at `m + n`, with the `n` cells above `m`
`false` and cell `m` `true`, seeks left to the marker at `m` in `n + 1` steps, tape unchanged. -/
theorem scanToTrueLeft_run (m n : ℕ) (c : Cfg scanToTrueLeft) (hstart : c.st = false)
    (hhd : c.hd = m + n) (hfalse : ∀ i, i < n → c.tp.getD (m + n - i) false = false)
    (htrue : c.tp.getD m false = true) :
    run scanToTrueLeft (n + 1) c = ⟨true, m, c.tp⟩ := by
  rw [run_succ, scanToTrueLeft_partial m n c hstart hhd hfalse n (le_refl n),
    show m + n - n = m from by omega,
    scanToTrueLeft_step_true (c := ⟨false, m, c.tp⟩) rfl htrue]

end PallLean.Paper93.DeepMath.PathB.UniversalMachineSeekLeft

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSeekLeft.scanToTrueLeft_partial
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSeekLeft.scanToTrueLeft_run
