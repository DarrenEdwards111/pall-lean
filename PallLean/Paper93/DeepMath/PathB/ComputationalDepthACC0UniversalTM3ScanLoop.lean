import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3AdvanceRecord
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3FullLayout

/-!
# Entry 471 — generic scan loop: the record-walk skeleton `skipRecordsToEnd` (proved)

The **architectural heart** of the fixed-size generic rule-table scan loop (the construction a fixed universal `U` needs —
entry 467).  A single fixed machine walks the whole rule table to the end marker: at each record start it branches on the
marker (`branchMark3`), exiting if it is the table terminator `M`, otherwise advancing to the next record (`advanceRecord3`,
entry 469) and looping back via a back-edge.  Correctness is by induction on the **record count** (data), the machine fixed.

`skipRecordsToEnd s done advE m1 m2 cont := branchMark3 s done advE ++ advanceRecord3 advE m1 m2 s cont`.

This is the scan loop *without* the per-record key comparison: it establishes that the fixed-state loop drives over an
arbitrary list of records — the structural backbone into which the comparison branch will later be inserted.

## What is proved (clean axioms, no `sorry`)

* **`skipRecordsToEnd s done advE m1 m2 cont`** — the record-walk machine.
* **`skipRecordsToEnd_run`** (PROVED) — for any `recs : List (ℕ × Bool)` and prefix `pre`, on the tape `pre ++ recordsTape3
  recs ++ M :: tail`: `∃ N, reachIn N (s, pre.length, tp) (done, (pre ++ recordsTape3 recs).length, tp)` — the head walks
  from the first record start to the terminator, tape identical — by induction on `recs`, machine fixed.

## Honest scope

This is the scan-loop **skeleton** (record-walk + end-detection).  It does **not** yet build the per-record key comparison
(the hard 3-symbol relative shuttle), the match-or-advance branch, the generic apply, nor a fixed `U` /
`EmitsEncodedStepEx3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanLoop

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 readSym3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config (configEncode3 configEncode3_content)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (branchMark3 branchMark3_run_mark branchMark3_run_notmark)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordsLayout (recordBlock recordsTape3 configEncode3_eq_recordBlock)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullLayout (configEncode3_absorb_tail)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3AdvanceRecord (advanceRecord3 advanceRecord3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3_length)

/-- **The record-walk machine.**  At a record start: on `M` exit to `done`; else advance to the next record and loop. -/
def skipRecordsToEnd (s done advE m1 m2 cont : ℕ) : TMachine3 :=
  branchMark3 s done advE ++ advanceRecord3 advE m1 m2 s cont

private theorem recordBlock_length (b : ℕ) (rs : Bool) : (recordBlock (b, rs)).length = b + 2 := by
  simp [recordBlock, encodeNatBits3_length]

/-- **The record-walk reaches the terminator (PROVED).** -/
theorem skipRecordsToEnd_run (s done advE m1 m2 cont : ℕ) (tp tail : List Sym3) :
    ∀ (recs : List (ℕ × Bool)) (pre : List Sym3),
      tp = pre ++ recordsTape3 recs ++ Sym3.M :: tail →
      ∃ N, reachIn (toNTM3 (skipRecordsToEnd s done advE m1 m2 cont)) N
        (s, pre.length, tp) (done, (pre ++ recordsTape3 recs).length, tp) := by
  intro recs
  induction recs with
  | nil =>
      intro pre htp
      refine ⟨1, ?_⟩
      have hM : tp.getD pre.length Sym3.O = Sym3.M := by
        rw [htp]; simp only [recordsTape3, List.append_nil]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl pre.length), Nat.sub_self]; rfl
      have hb : pre.length < tp.length := by
        have := congrArg List.length htp; simp [recordsTape3] at this; omega
      have hmark := branchMark3_run_mark s done advE pre.length tp
        (by show tp.getD pre.length Sym3.O = Sym3.M; exact hM) hb
      have lifted := reachIn_append_left3 (branchMark3 s done advE) (advanceRecord3 advE m1 m2 s cont) 1 _ _ hmark
      rw [show (pre ++ recordsTape3 ([] : List (ℕ × Bool))).length = pre.length from by simp [recordsTape3]]
      exact lifted
  | cons r rest ih =>
      intro pre htp
      obtain ⟨b, rs⟩ := r
      have htp_rec : tp = pre ++ configEncode3 b rs (recordsTape3 rest ++ Sym3.M :: tail) := by
        rw [htp, show recordsTape3 ((b, rs) :: rest) = configEncode3 b rs (recordsTape3 rest) from rfl,
          List.append_assoc, configEncode3_absorb_tail]
      have htp_pre' : tp = (pre ++ recordBlock (b, rs)) ++ recordsTape3 rest ++ Sym3.M :: tail := by
        rw [htp, show recordsTape3 ((b, rs) :: rest) = recordBlock (b, rs) ++ recordsTape3 rest from
          configEncode3_eq_recordBlock b rs (recordsTape3 rest)]
        simp [List.append_assoc]
      have content := configEncode3_content pre (recordsTape3 rest ++ Sym3.M :: tail) b rs
      rw [← htp_rec] at content
      have hrtlen : (recordsTape3 ((b, rs) :: rest)).length = (b + 2) + (recordsTape3 rest).length := by
        rw [show recordsTape3 ((b, rs) :: rest) = recordBlock (b, rs) ++ recordsTape3 rest from
          configEncode3_eq_recordBlock b rs (recordsTape3 rest), List.length_append, recordBlock_length]
      have hlen : tp.length = pre.length + (recordsTape3 ((b, rs) :: rest)).length + 1 + tail.length := by
        have := congrArg List.length htp; simp [List.length_append] at this; omega
      have hcell : tp.getD pre.length Sym3.O = Sym3.O ∨ tp.getD pre.length Sym3.O = Sym3.I := by
        rcases Nat.eq_zero_or_pos b with hb | hb
        · left; have h0 := content.2.1; rwa [hb, Nat.add_zero] at h0
        · right; have h0 := content.1 0 hb; rwa [Nat.add_zero] at h0
      have hne : readSym3 (s, pre.length, tp) ≠ Sym3.M := by
        show tp.getD pre.length Sym3.O ≠ Sym3.M
        rcases hcell with h | h <;> rw [h] <;> decide
      have step1 := reachIn_append_left3 (branchMark3 s done advE) (advanceRecord3 advE m1 m2 s cont) 1 _ _
        (branchMark3_run_notmark s done advE pre.length tp hne (by omega))
      obtain ⟨Na, hAdv⟩ := advanceRecord3_run advE m1 m2 s cont tp b pre.length content.1 content.2.1 (by omega)
      have step2 := reachIn_append_right3 (branchMark3 s done advE) (advanceRecord3 advE m1 m2 s cont) Na _ _ hAdv
      obtain ⟨Nrec, hRec⟩ := ih (pre ++ recordBlock (b, rs)) htp_pre'
      have hpos : (pre ++ recordBlock (b, rs)).length = pre.length + b + 2 := by
        rw [List.length_append, recordBlock_length]; omega
      rw [hpos] at hRec
      have hend : ((pre ++ recordBlock (b, rs)) ++ recordsTape3 rest).length
          = (pre ++ recordsTape3 ((b, rs) :: rest)).length := by
        rw [show recordsTape3 ((b, rs) :: rest) = recordBlock (b, rs) ++ recordsTape3 rest from
          configEncode3_eq_recordBlock b rs (recordsTape3 rest)]
        simp [List.append_assoc]
      rw [hend] at hRec
      refine ⟨1 + Na + Nrec, ?_⟩
      have c12 := (reachIn_add (toNTM3 (skipRecordsToEnd s done advE m1 m2 cont)) 1 Na _ _).mpr
        ⟨(advE, pre.length, tp), step1, step2⟩
      exact (reachIn_add (toNTM3 (skipRecordsToEnd s done advE m1 m2 cont)) (1 + Na) Nrec _ _).mpr
        ⟨(s, pre.length + b + 2, tp), c12, hRec⟩

/-!
**The record-walk skeleton, proved.**  `skipRecordsToEnd` drives a fixed machine over an arbitrary list of records to the
terminator, by induction on the record count — the structural backbone of the generic scan loop.  Next: the per-record key
comparison (3-symbol relative shuttle) and the match-or-advance branch, then the full loop, the generic apply, and a fixed
`U` toward `EmitsEncodedStepEx3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanLoop

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanLoop.skipRecordsToEnd_run
