import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineScanMarker
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUniversalMachineSeq

/-!
# Head-move construction, brick 10: reading the simulated symbol at the marked head

With the two-track layout (brick 9), the head cell's data bit sits at physical cell `2m`, one cell left
of where `scanMarker` halts (`2m + 1`).  So *reading the simulated symbol at the head* is: seek to the
marker (`scanMarker`), step one cell left, read the data.  This brick builds the read gadget
`readAtMarker` and composes it with `scanMarker` via `seq` (brick 6) into `readSimSymbol` — a single
machine that reads the head cell's data bit into its decision.

`seq` needs `scanMarker` to *not halt before* it finds the marker — across *both* phases of its
two-step cycle (`atData` at even steps, `atMarker` at odd).  `scanMarker_not_halted` proves this
parity-free (splitting on `s' % 2` and reusing `scanMarker_partial`).

## What is proved

* **`readAtMarker`** — from the marker: step left to the data cell, read it, halt storing the bit in the
  accept state.
* **`readAtMarker_run`** — `run readAtMarker 2 c = ⟨got (c.tp.getD (c.hd - 1) false), c.hd - 1, c.tp⟩`.
* **`scanMarker_not_halted`** — `scanMarker` does not halt at any `s' < 2m + 2`.
* **`readSimSymbol`** — the composite `seq scanMarker readAtMarker` on a two-track tape marked at `m`
  ends at `⟨got (data bit at 2m), 2m, …⟩`.
* **`readSimSymbol_accept`** — its decision equals the head cell's data bit: the machine *reads the
  simulated symbol at the head*.

## Honest scope

`readSimSymbol` is the read half of a simulated step, assembled from proven primitives via `seq`.  What
remains for `uStepOnTape`: the rule-lookup scan (state + read symbol ↦ new symbol/state/move) and the
reset-to-0 per-step wrapper; then the lazy-delay diagonal.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniversalMachineReadSymbol

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.UniversalMachineScanMarker
open PallLean.Paper93.DeepMath.PathB.UniversalMachineSeq

/-- Control states of `readAtMarker`: move left to the data cell, read it, or done holding the bit. -/
inductive RD where
  | mvL : RD
  | rd : RD
  | got : Bool → RD
  deriving DecidableEq

instance : Fintype RD := ⟨{RD.mvL, RD.rd, RD.got false, RD.got true}, fun x => by
  cases x with
  | mvL => decide
  | rd => decide
  | got b => cases b <;> decide⟩

/-- **The read gadget.**  Positioned ON the marker: state `mvL` moves one cell left (to the data cell);
state `rd` reads the data bit and halts, storing it in `got`. -/
def readAtMarker : Machine where
  State := RD
  fin := inferInstance
  dec := inferInstance
  start := RD.mvL
  halt := fun s => match s with | .got _ => true | _ => false
  δ := fun s b => match s with
    | .mvL => (RD.rd, none, (0 : Move))
    | .rd => (RD.got b, none, (2 : Move))
    | .got g => (RD.got g, none, (2 : Move))
  accept := fun s => match s with | .got b => b | _ => false

theorem readAtMarker_step_active {c : Cfg readAtMarker} (hne : readAtMarker.halt c.st = false) :
    step readAtMarker c = ⟨(readAtMarker.δ c.st (c.tp.getD c.hd false)).1,
                    moveHead c.hd (readAtMarker.δ c.st (c.tp.getD c.hd false)).2.2,
                    (match (readAtMarker.δ c.st (c.tp.getD c.hd false)).2.1 with
                      | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
  unfold step; rw [hne]; rfl

theorem readAtMarker_step_mvL {c : Cfg readAtMarker} (hs : c.st = RD.mvL) :
    step readAtMarker c = ⟨RD.rd, c.hd - 1, c.tp⟩ := by
  rw [readAtMarker_step_active (by rw [hs]; rfl), hs]; rfl

theorem readAtMarker_step_rd {c : Cfg readAtMarker} (hs : c.st = RD.rd) :
    step readAtMarker c = ⟨RD.got (c.tp.getD c.hd false), c.hd, c.tp⟩ := by
  rw [readAtMarker_step_active (by rw [hs]; rfl), hs]; rfl

/-- **The read is correct (proved).**  Two steps: move left to the data cell, then read it into the
accept state. -/
theorem readAtMarker_run (c : Cfg readAtMarker) (hs : c.st = RD.mvL) :
    run readAtMarker 2 c = ⟨RD.got (c.tp.getD (c.hd - 1) false), c.hd - 1, c.tp⟩ := by
  show step readAtMarker (step readAtMarker c) = _
  rw [readAtMarker_step_mvL hs, readAtMarker_step_rd rfl]

/-- **`scanMarker` does not halt before finding the marker (proved).**  For any `s' < 2m + 2`, whether
`s'` is even (state `atData`) or odd (state `atMarker`), the machine has not reached `found`. -/
theorem scanMarker_not_halted (m : ℕ) (c : Cfg scanMarker) (hstart : c.st = Mark2.atData)
    (hfalse : ∀ k, k < m → c.tp.getD (c.hd + 2 * k + 1) false = false) :
    ∀ s', s' < 2 * m + 2 → scanMarker.halt (run scanMarker s' c).st = false := by
  intro s' hs'
  rcases Nat.mod_two_eq_zero_or_one s' with h2 | h2
  · have hs2 : s' = 2 * (s' / 2) := by omega
    have hkm : s' / 2 ≤ m := by omega
    rw [hs2, scanMarker_partial m c hstart hfalse (s' / 2) hkm]; rfl
  · have hs2 : s' = 2 * (s' / 2) + 1 := by omega
    have hkm : s' / 2 ≤ m := by omega
    rw [hs2, run_succ, scanMarker_partial m c hstart hfalse (s' / 2) hkm,
      scanMarker_step_data (c := ⟨Mark2.atData, c.hd + 2 * (s' / 2), c.tp⟩) rfl]
    rfl

/-- **The read composite (proved).**  On a two-track tape marked at cell `m` (head `0`), `seq
scanMarker readAtMarker` seeks to the marker and reads the head cell's data bit at `2m`. -/
theorem readSimSymbol (m : ℕ) (post : List Bool) :
    run (seq scanMarker readAtMarker) (2 * m + 2 + 1 + 2)
        (init (seq scanMarker readAtMarker) (List.replicate (2 * m + 1) false ++ (true :: post)))
      = seqEmbedR scanMarker readAtMarker
          ⟨RD.got ((List.replicate (2 * m + 1) false ++ (true :: post)).getD (2 * m) false), 2 * m,
            List.replicate (2 * m + 1) false ++ (true :: post)⟩ := by
  set x := List.replicate (2 * m + 1) false ++ (true :: post) with hx
  have hfalse_x : ∀ k, k < m → x.getD (0 + 2 * k + 1) false = false := by
    intro k hk
    rw [hx, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [List.length_replicate]; omega),
      List.getElem?_replicate_of_lt (by omega)]
    rfl
  have htrue_x : x.getD (0 + 2 * m + 1) false = true := by
    rw [hx, Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
      List.length_replicate, Nat.sub_self]
    rfl
  have hscan : run scanMarker (2 * m + 2) (init scanMarker x) = ⟨Mark2.found, 2 * m + 1, x⟩ := by
    rw [scanMarker_run m (init scanMarker x) rfl (fun k hk => hfalse_x k hk) htrue_x]
    show (⟨Mark2.found, 0 + 2 * m + 1, x⟩ : Cfg scanMarker) = ⟨Mark2.found, 2 * m + 1, x⟩
    rw [Nat.zero_add]
  have hmin : ∀ s' < 2 * m + 2, scanMarker.halt (run scanMarker s' (init scanMarker x)).st = false :=
    fun s' hs' => scanMarker_not_halted m (init scanMarker x) rfl (fun k hk => hfalse_x k hk) s' hs'
  have hhalt : scanMarker.halt (run scanMarker (2 * m + 2) (init scanMarker x)).st = true := by
    rw [hscan]; rfl
  rw [seq_runs scanMarker readAtMarker x (2 * m + 2) 2 hmin hhalt, hscan]
  exact congrArg (seqEmbedR scanMarker readAtMarker)
    (readAtMarker_run ⟨readAtMarker.start, 2 * m + 1, x⟩ rfl)

/-- **The composite reads the head symbol (proved).**  Its decision equals the head cell's data bit. -/
theorem readSimSymbol_accept (m : ℕ) (post : List Bool) :
    (seq scanMarker readAtMarker).accept
        (run (seq scanMarker readAtMarker) (2 * m + 2 + 1 + 2)
          (init (seq scanMarker readAtMarker)
            (List.replicate (2 * m + 1) false ++ (true :: post)))).st
      = (List.replicate (2 * m + 1) false ++ (true :: post)).getD (2 * m) false := by
  rw [readSimSymbol]; rfl

end PallLean.Paper93.DeepMath.PathB.UniversalMachineReadSymbol

#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineReadSymbol.readSimSymbol
#print axioms PallLean.Paper93.DeepMath.PathB.UniversalMachineReadSymbol.readSimSymbol_accept
