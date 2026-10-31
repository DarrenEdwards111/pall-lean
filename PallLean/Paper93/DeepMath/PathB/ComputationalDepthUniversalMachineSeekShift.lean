import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineSeek
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineMarkerShift

/-!
# Head-move construction, brick 7: the first composite — self-seeking simulated head-move

This is the payoff of bricks 4–6.  A simulated head-move to the right is: *seek to the marked head*
(`scanToTrue`, brick 4), then *shift the marker one cell* (`shiftRight`, brick 5).  Chaining them needs
the position-preserving sequencer `seq` (brick 6) — `comp`'s reset would send the shift back to cell 0.
This brick wires them together and proves the composite is correct end-to-end: `seq scanToTrue
shiftRight`, run on a tape whose head is marked at position `n`, moves the marker to `n + 1`.

The one new supporting fact: `seq_runs` needs `scanToTrue` to *not halt before* it finds the marker
(`scanToTrue_partial` / `scanToTrue_scanning_before`) — otherwise the switch time is wrong.

## What is proved

* **`scanToTrue_partial`** — before the marker, `scanToTrue` is a plain right-scan:
  `run scanToTrue s' c = ⟨false, c.hd + s', c.tp⟩` for `s' ≤ n`.
* **`seekThenShift`** (capstone) — on a tape `replicate n false ++ (true :: post)` (head marked at `n`),
  `seq scanToTrue shiftRight` runs to `⟨Shift.done, n + 1, writeAt (writeAt … n false) (n+1) true⟩`:
  seek finds the marker at `n`, the switch keeps the head there, and the shift moves the marker to
  `n + 1`.  The simulated head-move, self-seeking, assembled from proven primitives.

## Honest scope

This is the first end-to-end composite — evidence the marked-head kit + `seq` genuinely assemble a
simulated step.  What remains for full `uStepOnTape`: the read/rule-lookup phase between seek and shift
(also `seq`-chained), and the reset-to-0 wrapper so each step starts clean; then the lazy-delay
diagonal.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineSeekShift

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSeek
open PallLean.Paper93.DeepMath.PathB.UniversalMachineMarkerShift
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSeq

/-- **Before the marker, `scanToTrue` is a plain right-scan (proved).**  If the `n` cells ahead are
`false`, then for any `s' ≤ n` the machine is still scanning with the head advanced by `s'`. -/
theorem scanToTrue_partial (n : ℕ) (c : Cfg scanToTrue) (hs : c.st = false)
    (hfalse : ∀ i, i < n → c.tp.getD (c.hd + i) false = false) :
    ∀ (s' : ℕ), s' ≤ n → run scanToTrue s' c = ⟨false, c.hd + s', c.tp⟩ := by
  intro s'
  induction s' with
  | zero => intro _; obtain ⟨st, hd, tp⟩ := c; subst hs; rfl
  | succ s' ih =>
    intro hle
    have hstep := scanToTrue_step_false (c := ⟨false, c.hd + s', c.tp⟩) rfl (hfalse s' (by omega))
    rw [run_succ, ih (by omega), hstep, show c.hd + s' + 1 = c.hd + (s' + 1) from by omega]

/-- **The self-seeking simulated head-move (proved).**  On a tape marked at position `n`, `seq
scanToTrue shiftRight` seeks to the marker and shifts it to `n + 1` — seek, switch (head preserved),
shift — all from proven primitives. -/
theorem seekThenShift (n : ℕ) (post : List Bool) :
    run (seq scanToTrue shiftRight) (n + 1 + 1 + 2)
        (init (seq scanToTrue shiftRight) (List.replicate n false ++ (true :: post)))
      = seqEmbedR scanToTrue shiftRight
          ⟨Shift.done, n + 1,
            writeAt (writeAt (List.replicate n false ++ (true :: post)) n false) (n + 1) true⟩ := by
  set x := List.replicate n false ++ (true :: post) with hx
  -- reading inside the false-run gives false; at position n, the marker true
  have hx_false : ∀ i, i < n → x.getD i false = false := by
    intro i hi
    rw [hx, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [List.length_replicate]; exact hi),
      List.getElem?_replicate_of_lt hi]
    rfl
  have hx_true : x.getD n false = true := by
    rw [hx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
      List.length_replicate, Nat.sub_self]
    rfl
  -- scanToTrue seeks to the marker at n
  have hscan : run scanToTrue (n + 1) (init scanToTrue x) = ⟨true, n, x⟩ := by
    rw [scanToTrue_run n (init scanToTrue x) rfl
      (fun i hi => by show x.getD (0 + i) false = false; rw [Nat.zero_add]; exact hx_false i hi)
      (by show x.getD (0 + n) false = true; rw [Nat.zero_add]; exact hx_true)]
    show (⟨true, 0 + n, x⟩ : Cfg scanToTrue) = ⟨true, n, x⟩
    rw [Nat.zero_add]
  -- it does not halt before the marker
  have hmin : ∀ s' < n + 1, scanToTrue.halt (run scanToTrue s' (init scanToTrue x)).st = false := by
    intro s' hs'
    rw [scanToTrue_partial n (init scanToTrue x) rfl
      (fun i hi => by show x.getD (0 + i) false = false; rw [Nat.zero_add]; exact hx_false i hi)
      s' (by omega)]
    rfl
  have hhalt : scanToTrue.halt (run scanToTrue (n + 1) (init scanToTrue x)).st = true := by
    rw [hscan]; rfl
  rw [seq_runs scanToTrue shiftRight x (n + 1) 2 hmin hhalt, hscan]
  exact congrArg (seqEmbedR scanToTrue shiftRight) (shiftRight_run ⟨shiftRight.start, n, x⟩ rfl)

end PallLean.Paper93.DeepMath.PathB.UniversalMachineSeekShift

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSeekShift.scanToTrue_partial
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineSeekShift.seekThenShift
