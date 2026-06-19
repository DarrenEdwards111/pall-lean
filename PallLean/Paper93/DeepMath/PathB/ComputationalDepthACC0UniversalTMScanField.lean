import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanNatRun

/-!
# Entry 346 — universal-TM-table build: the relocatable field scanner `scanNatFrom` (proved)

Entry 345 proved the full run of `scanNat`, the fixed `0 → 1`, head-`0` scanner over one encoded nat.  To traverse a
whole transition — whose `encodeTransBits` layout is the five fields `nat, sym, nat, sym, nat` (entry 338) — we need to
chain scans, each picking up where the last stopped.  That requires a **relocatable** scanner: one parameterised by an
entry state `s`, an exit state `s'`, and an arbitrary starting head `h`.  This brick builds `scanNatFrom s s'` and proves
its full run from an *abstract content hypothesis* (the cells `h .. h+n-1` read `true`, cell `h+n` reads `false`), so
each chained field supplies only its own local content and the scanner is reused verbatim.

`scanNat` (entry 344) is the special case `scanNatFrom 0 1` started at head `0`; `scanNatFrom` is the general primitive
the field/rule scans are built from.

## What is proved (clean axioms, no `sorry`)

* **`scanNatFrom`** — the machine `[((s,true),(s,true,→)), ((s,false),(s',false,→))]`: in state `s`, on `true` stay in
  `s` and move right; on the `false` separator go to `s'` and move right past it.
* **`scanNatFrom_step_true` / `scanNatFrom_step_false`** (PROVED) — its single-step behaviours at an arbitrary head.
* **`scanNatFrom_scan`** (PROVED) — the relocatable tape-invariant: from `(s, h, tp)`, given the cells `h .. h+n-1`
  read `true`, after `j ≤ n` steps the machine is in state `s` at head `h+j`, tape contents preserved.
* **`scanNatFrom_run`** (PROVED) — `∃ tp', reachIn (toNTM (scanNatFrom s s')) (n+1) (s, h, tp) (s', h+n+1, tp')`: given
  the cells `h .. h+n-1` read `true` and cell `h+n` reads `false`, the scanner consumes one encoded nat at offset `h` in
  `n+1` steps and exits in state `s'` at head `h+n+1`.

## Honest scope

This is the **reusable field-scan primitive** of the universal-TM transition table — a relocatable scanner verified over
the concrete `CConfig`/`TMTrans` model from an abstract content hypothesis, so chained copies (disjoint state pairs) can
skip the five fields of a transition.  It does **not** yet wire those copies into one machine, nor scan-and-match the
rule table, nor apply — those are the next verified fragments.  Building them fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine Move concreteStep readSym applyTrans moveHead writeAt toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat (writeAt_getD_self)

/-- **The relocatable scan-one-nat machine.**  Entry state `s` = scanning: on `true` stay in `s` and move right; on the
`false` separator go to exit state `s'` and move right past it.  `scanNat` (entry 344) is `scanNatFrom 0 1`. -/
def scanNatFrom (s s' : ℕ) : TMachine :=
  [((s, true), (s, true, (1 : Move))), ((s, false), (s', false, (1 : Move)))]

/-- **`scanNatFrom` advances over a `true` cell (PROVED).**  At `(s, j, tp)` reading `true`, it steps to
`(s, j+1, …)`, staying in the scanning state `s`. -/
theorem scanNatFrom_step_true (s s' j : ℕ) (tp : List Bool) (h : tp.getD j false = true) :
    concreteStep (scanNatFrom s s') (s, j, tp) (s, j + 1, writeAt tp j true) := by
  refine ⟨((s, true), (s, true, (1 : Move))), ?_, ?_, ?_⟩
  · simp [scanNatFrom]
  · show (s, true) = ((s, j, tp).1, readSym (s, j, tp))
    simp only [readSym, h]
  · simp [applyTrans, moveHead]

/-- **`scanNatFrom` exits at the `false` separator (PROVED).**  At `(s, j, tp)` reading `false`, it steps to
`(s', j+1, …)` — exit state `s'`, head advanced past the separator. -/
theorem scanNatFrom_step_false (s s' j : ℕ) (tp : List Bool) (h : tp.getD j false = false) :
    concreteStep (scanNatFrom s s') (s, j, tp) (s', j + 1, writeAt tp j false) := by
  refine ⟨((s, false), (s', false, (1 : Move))), ?_, ?_, ?_⟩
  · simp [scanNatFrom]
  · show (s, false) = ((s, j, tp).1, readSym (s, j, tp))
    simp only [readSym, h]
  · simp [applyTrans, moveHead]

/-- **The relocatable scan tape-invariant (PROVED).**  From `(s, h, tp)`, given the cells `h .. h+n-1` read `true`,
after `j ≤ n` steps `scanNatFrom s s'` is in state `s` at head `h+j`, with the tape contents preserved. -/
theorem scanNatFrom_scan (s s' n h : ℕ) (tp : List Bool)
    (htrue : ∀ i, i < n → tp.getD (h + i) false = true) : ∀ j, j ≤ n →
    ∃ tp', reachIn (toNTM (scanNatFrom s s')) j (s, h, tp) (s, h + j, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  intro j
  induction j with
  | zero => intro _; exact ⟨tp, rfl, fun _ => rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨tp', hr, hpres⟩ := ih (by omega)
      have htrue' : tp'.getD (h + j) false = true := by
        rw [hpres (h + j), htrue j (by omega)]
      have hstep := scanNatFrom_step_true s s' (h + j) tp' htrue'
      refine ⟨writeAt tp' (h + j) true, ?_, ?_⟩
      · exact (reachIn_add (toNTM (scanNatFrom s s')) j 1 _ _).mpr ⟨(s, h + j, tp'), hr, ⟨_, hstep, rfl⟩⟩
      · intro q
        have hwb : (writeAt tp' (h + j) true).getD q false
            = (writeAt tp' (h + j) (tp'.getD (h + j) false)).getD q false := by rw [htrue']
        rw [hwb, writeAt_getD_self, hpres q]

/-- **The full relocatable field scan (PROVED).**  From `(s, h, tp)`, given the cells `h .. h+n-1` read `true` and cell
`h+n` reads `false`, `scanNatFrom s s'` runs `n+1` steps to state `s'` at head `h+n+1` — consuming exactly one encoded
nat at offset `h`. -/
theorem scanNatFrom_run (s s' n h : ℕ) (tp : List Bool)
    (htrue : ∀ i, i < n → tp.getD (h + i) false = true)
    (hfalse : tp.getD (h + n) false = false) :
    ∃ tp', reachIn (toNTM (scanNatFrom s s')) (n + 1) (s, h, tp) (s', h + n + 1, tp') := by
  obtain ⟨tp', hr, hpres⟩ := scanNatFrom_scan s s' n h tp htrue n (le_refl n)
  have hfalse' : tp'.getD (h + n) false = false := by rw [hpres (h + n), hfalse]
  have hstep := scanNatFrom_step_false s s' (h + n) tp' hfalse'
  exact ⟨writeAt tp' (h + n) false,
    (reachIn_add (toNTM (scanNatFrom s s')) n 1 _ _).mpr ⟨(s, h + n, tp'), hr, ⟨_, hstep, rfl⟩⟩⟩

/-!
**The relocatable field scanner, proved.**  `scanNatFrom_run` consumes one encoded nat at an arbitrary offset `h`,
between arbitrary entry/exit states `s → s'`, from a local content hypothesis — the reusable primitive for skipping the
five fields of a transition.  Next: wire disjoint-state copies into one machine that scans a whole `encodeTransBits`
layout, then scan-and-match the rule table, then the apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField.scanNatFrom_step_true
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField.scanNatFrom_step_false
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField.scanNatFrom_run
