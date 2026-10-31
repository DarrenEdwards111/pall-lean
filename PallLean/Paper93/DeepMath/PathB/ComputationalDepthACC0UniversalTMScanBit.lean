import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMFieldCompose

/-!
# Entry 349 — universal-TM-table build: the one-bit scanner `scanBit` (proved)

The `encodeTransBits` layout (entry 338) interleaves *single symbol bits* between the nat fields:
`nat, sym, nat, sym, nat`.  The relocatable nat scanner `scanNatFrom` (entry 346) handles the nat fields; this brick
adds the missing piece — a **one-bit scanner** `scanBit s s'` that advances the head past exactly one cell *regardless
of its value* (`true` or `false`), transitioning from entry state `s` to exit state `s'`, writing back the symbol it
read so the tape is preserved.

Unlike `scanNatFrom` (which loops in state `s` until the separator), `scanBit` is a *single step* — it consumes one
cell and exits — so its "run" is one step.  This is exactly the primitive the symbol fields need.

## What is proved (clean axioms, no `sorry`)

* **`scanBit s s'`** — the machine `[((s,true),(s',true,→)), ((s,false),(s',false,→))]`: in state `s`, on either symbol
  go to `s'`, write the symbol back, and move right.
* **`scanBit_step`** (PROVED) — the single-step behaviour at an arbitrary head, *uniformly in the read symbol*:
  `concreteStep (scanBit s s') (s, j, tp) (s', j+1, writeAt tp j (tp.getD j false))`.
* **`scanBit_run_pres`** (PROVED) — `∃ tp', reachIn (toNTM (scanBit s s')) 1 (s, h, tp) (s', h+1, tp') ∧
  ∀ q, tp'.getD q false = tp.getD q false`: the one-step run consuming one symbol bit, preserving the tape (the
  write-back is non-destructive via `writeAt_getD_self`, entry 344) — the composable unit for the symbol fields.

## Honest scope

This builds the **one-bit scanner** for the symbol fields, with a preservation-tracking one-step run matching the shape
of `scanNatFrom_run_pres` (entry 348) so the two compose under `reachIn_seq`.  It does **not** yet assemble the full
five-field `encodeTransBits` scan (the next fragment chains `scanNatFrom`/`scanBit` runs across `nat, sym, nat, sym,
nat`), nor the rule-table scan-and-match, nor the apply.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine Move concreteStep readSym applyTrans moveHead writeAt toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat (writeAt_getD_self)

/-- **The one-bit scanner.**  Entry state `s`: on either symbol, exit to `s'`, write the symbol back, move right.
A single step — it consumes exactly one cell. -/
def scanBit (s s' : ℕ) : TMachine :=
  [((s, true), (s', true, (1 : Move))), ((s, false), (s', false, (1 : Move)))]

/-- **`scanBit` consumes one cell (PROVED), uniformly in the read symbol.**  At `(s, j, tp)`, whatever the symbol
`tp.getD j false`, it steps to `(s', j+1, writeAt tp j (tp.getD j false))` — exit state `s'`, head advanced, symbol
written back. -/
theorem scanBit_step (s s' j : ℕ) (tp : List Bool) :
    concreteStep (scanBit s s') (s, j, tp) (s', j + 1, writeAt tp j (tp.getD j false)) := by
  cases h : tp.getD j false with
  | false =>
      refine ⟨((s, false), (s', false, (1 : Move))), ?_, ?_, ?_⟩
      · simp [scanBit]
      · show (s, false) = ((s, j, tp).1, readSym (s, j, tp))
        simp only [readSym, h]
      · simp [applyTrans, moveHead]
  | true =>
      refine ⟨((s, true), (s', true, (1 : Move))), ?_, ?_, ?_⟩
      · simp [scanBit]
      · show (s, true) = ((s, j, tp).1, readSym (s, j, tp))
        simp only [readSym, h]
      · simp [applyTrans, moveHead]

/-- **The one-step `scanBit` run, preserving the tape (PROVED).**  Consuming one symbol bit at offset `h`, the machine
goes from `(s, h, tp)` to `(s', h+1, tp')` in one step, with `tp'` agreeing with `tp` on every cell (the write-back is
non-destructive). -/
theorem scanBit_run_pres (s s' h : ℕ) (tp : List Bool) :
    ∃ tp', reachIn (toNTM (scanBit s s')) 1 (s, h, tp) (s', h + 1, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  refine ⟨writeAt tp h (tp.getD h false), ⟨_, scanBit_step s s' h tp, rfl⟩, ?_⟩
  intro q
  exact writeAt_getD_self tp h q

/-!
**The one-bit scanner, proved.**  `scanBit` consumes one symbol cell uniformly in its value, and `scanBit_run_pres` is
the preservation-tracking one-step run matching `scanNatFrom_run_pres` (entry 348) — so nat and bit scans compose under
`reachIn_seq`.  Next: chain `scanNatFrom`/`scanBit` runs across the whole `encodeTransBits` layout (`nat, sym, nat, sym,
nat`) in one machine, then the rule-table scan-and-match and the apply — fragment by verified fragment, not faked.  Not
a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit.scanBit_step
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit.scanBit_run_pres
