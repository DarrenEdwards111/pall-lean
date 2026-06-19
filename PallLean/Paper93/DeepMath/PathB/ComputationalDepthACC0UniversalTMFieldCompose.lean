import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCompose

/-!
# Entry 348 — universal-TM-table build: preservation-tracking field run + two-field composition (proved)

Entry 346 gave the relocatable scanner `scanNatFrom` and entry 347 the wiring law `reachIn_seq` (chain sub-table runs
inside the union machine, no disjointness needed).  The remaining obstacle to scanning *consecutive* fields is the
**tape-preservation threading**: `scanNatFrom_run` (346) returns `∃ tp'` but hides that `tp'` agrees with the input tape,
yet the *next* field's content hypothesis is stated about that post-scan tape.  This brick closes the gap.

* **`scanNatFrom_run_pres`** strengthens `scanNatFrom_run` to also expose that the resulting tape *preserves every cell*
  of the input (the scan is non-destructive: `true` cells write back `true`, the separator writes back `false`).
* **`scanTwoNats`** then chains two consecutive nat fields: scan field 1 (states `0 → 1`), use its preservation to
  discharge field 2's content hypothesis on the post-field-1 tape, scan field 2 (states `1 → 2`), and compose the two
  runs inside the union machine `scanNatFrom 0 1 ++ scanNatFrom 1 2` via `reachIn_seq`.  This is the first genuine
  multi-field scan — the threading mechanism the full `encodeTransBits` traversal is built from.

## What is proved (clean axioms, no `sorry`)

* **`scanNatFrom_run_pres`** (PROVED) — `∃ tp', reachIn (toNTM (scanNatFrom s s')) (n+1) (s, h, tp) (s', h+n+1, tp') ∧
  ∀ q, tp'.getD q false = tp.getD q false`: the full relocatable field run, now also preserving the tape.
* **`scanTwoNats`** (PROVED) — from `(0, h, tp)`, given two consecutive encoded nats at offsets `h` and `h+n₁+1`, the
  union machine `scanNatFrom 0 1 ++ scanNatFrom 1 2` runs `(n₁+1)+(n₂+1)` steps to state `2` at head `h+n₁+1+n₂+1`.

## Honest scope

This proves the **tape-preservation threading and the first two-field composition** — exactly the mechanism that lets
consecutive fields be scanned in one machine.  It does **not** yet handle the *single symbol bit* fields interleaved in
`encodeTransBits` (`nat, sym, nat, sym, nat`) — that needs a one-bit scanner fragment — nor the rule-table
scan-and-match, nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFieldCompose

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM writeAt)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat (writeAt_getD_self)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField
  (scanNatFrom scanNatFrom_scan scanNatFrom_step_false scanNatFrom_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The full relocatable field run, preserving the tape (PROVED).**  Like `scanNatFrom_run`, but additionally the
resulting tape agrees with the input on every cell (the scan is non-destructive). -/
theorem scanNatFrom_run_pres (s s' n h : ℕ) (tp : List Bool)
    (htrue : ∀ i, i < n → tp.getD (h + i) false = true)
    (hfalse : tp.getD (h + n) false = false) :
    ∃ tp', reachIn (toNTM (scanNatFrom s s')) (n + 1) (s, h, tp) (s', h + n + 1, tp') ∧
      ∀ q, tp'.getD q false = tp.getD q false := by
  obtain ⟨tp', hr, hpres⟩ := scanNatFrom_scan s s' n h tp htrue n (le_refl n)
  have hfalse' : tp'.getD (h + n) false = false := by rw [hpres (h + n), hfalse]
  have hstep := scanNatFrom_step_false s s' (h + n) tp' hfalse'
  refine ⟨writeAt tp' (h + n) false, ?_, ?_⟩
  · exact (reachIn_add (toNTM (scanNatFrom s s')) n 1 _ _).mpr ⟨(s, h + n, tp'), hr, ⟨_, hstep, rfl⟩⟩
  · intro q
    have hwb : (writeAt tp' (h + n) false).getD q false
        = (writeAt tp' (h + n) (tp'.getD (h + n) false)).getD q false := by rw [hfalse']
    rw [hwb, writeAt_getD_self, hpres q]

/-- **Two consecutive nat fields scanned in one machine (PROVED).**  Given encoded nats of lengths `n₁`, `n₂` at offsets
`h` and `h+n₁+1` (each `nᵢ` `true`s then a `false` separator), the union machine `scanNatFrom 0 1 ++ scanNatFrom 1 2`
runs `(n₁+1)+(n₂+1)` steps from `(0, h, tp)` to state `2` at head `h+n₁+1+n₂+1`.  Field 2's content hypothesis is
discharged on the post-field-1 tape via field 1's preservation. -/
theorem scanTwoNats (n₁ n₂ h : ℕ) (tp : List Bool)
    (ht1 : ∀ i, i < n₁ → tp.getD (h + i) false = true)
    (hf1 : tp.getD (h + n₁) false = false)
    (ht2 : ∀ i, i < n₂ → tp.getD (h + n₁ + 1 + i) false = true)
    (hf2 : tp.getD (h + n₁ + 1 + n₂) false = false) :
    ∃ tp', reachIn (toNTM (scanNatFrom 0 1 ++ scanNatFrom 1 2)) ((n₁ + 1) + (n₂ + 1))
      (0, h, tp) (2, h + n₁ + 1 + n₂ + 1, tp') := by
  obtain ⟨tp1, hr1, hpres1⟩ := scanNatFrom_run_pres 0 1 n₁ h tp ht1 hf1
  have ht2' : ∀ i, i < n₂ → tp1.getD (h + n₁ + 1 + i) false = true := by
    intro i hi; rw [hpres1 _, ht2 i hi]
  have hf2' : tp1.getD (h + n₁ + 1 + n₂) false = false := by rw [hpres1 _, hf2]
  obtain ⟨tp2, hr2⟩ := scanNatFrom_run 1 2 n₂ (h + n₁ + 1) tp1 ht2' hf2'
  exact ⟨tp2, reachIn_seq (scanNatFrom 0 1) (scanNatFrom 1 2) (n₁ + 1) (n₂ + 1) _ _ _ hr1 hr2⟩

/-!
**Tape-preservation threading and the first two-field scan, proved.**  `scanNatFrom_run_pres` exposes that a field scan
is non-destructive, and `scanTwoNats` chains two consecutive nat fields in one union machine — discharging the second
field's content hypothesis on the post-scan tape.  Next: a one-bit scanner for the interleaved symbol fields, then the
whole `encodeTransBits` (`nat, sym, nat, sym, nat`) in one machine, then the rule-table scan-and-match and the apply —
fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFieldCompose

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFieldCompose.scanNatFrom_run_pres
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFieldCompose.scanTwoNats
