import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCheckBit

/-!
# Entry 353 — universal-TM-table build: the fixed-pattern matcher `matchPattern` (proved)

Entry 352 built `checkBit b` — verify one expected bit, advance, branch.  This brick **chains a list of checkers** into
a machine that verifies a whole fixed bit pattern: `matchPattern pat s F` checks the tape, cell by cell, against the
constant pattern `pat`, with every failing checker routed to the common fail-state `F`; it reaches the success state
`s + pat.length` (head advanced past the pattern) iff every bit matched.

This is the first *composite* control-flow machine of the matching half — a `reachIn_seq` fold of `checkBit`s — and the
direct model of matching a fixed key against the tape.

## What is proved (clean axioms, no `sorry`)

* **`matchPattern pat s F`** — recursively, `[]` ↦ the empty machine and `b :: bs` ↦
  `checkBit b s (s+1) F ++ matchPattern bs (s+1) F`: state `s+i` checks pattern bit `i`, continuing to `s+i+1` or
  failing to `F`.
* **`matchPattern_run_match`** (PROVED) — if the tape from offset `h` matches `pat`
  (`∀ i < pat.length, tp.getD (h+i) false = pat.getD i false`), then
  `∃ tp', reachIn (toNTM (matchPattern pat s F)) pat.length (s, h, tp) (s + pat.length, h + pat.length, tp') ∧
  ∀ q, tp'.getD q false = tp.getD q false`: the matcher runs `pat.length` steps to the success state with the head past
  the pattern, preserving the tape.

## Honest scope

This is the **fixed-pattern matcher** — verifying the tape against a constant pattern by chaining checkers.  It does
**not** yet compare two *tape* regions (the two-pointer key match, where both operands are read from the tape rather
than baked into the machine), nor the rule-table scan-and-match loop over the transition list, nor the apply.  Building
those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMatchPattern

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCheckBit (checkBit checkBit_run_match)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The fixed-pattern matcher.**  Chains one `checkBit` per pattern bit, every failure routed to the common
fail-state `F`; reaches `s + pat.length` iff every bit matched. -/
def matchPattern : List Bool → ℕ → ℕ → TMachine
  | [], _, _ => []
  | b :: bs, s, F => checkBit b s (s + 1) F ++ matchPattern bs (s + 1) F

/-- **The fixed-pattern matcher succeeds on a matching tape (PROVED).**  If the tape from offset `h` agrees with `pat`,
`matchPattern pat s F` runs `pat.length` steps to state `s + pat.length` at head `h + pat.length`, preserving the tape. -/
theorem matchPattern_run_match (pat : List Bool) (s F h : ℕ) (tp : List Bool)
    (hmatch : ∀ i, i < pat.length → tp.getD (h + i) false = pat.getD i false) :
    ∃ tp', reachIn (toNTM (matchPattern pat s F)) pat.length (s, h, tp)
      (s + pat.length, h + pat.length, tp') ∧ ∀ q, tp'.getD q false = tp.getD q false := by
  induction pat generalizing s h tp with
  | nil => exact ⟨tp, rfl, fun _ => rfl⟩
  | cons b bs ih =>
      have hb : tp.getD h false = b := by
        have h0 := hmatch 0 (by simp)
        rw [Nat.add_zero, List.getD_cons_zero] at h0
        exact h0
      obtain ⟨tp1, run1, hpres1⟩ := checkBit_run_match b s (s + 1) F h tp hb
      have hcont : ∀ i, i < bs.length → tp1.getD ((h + 1) + i) false = bs.getD i false := by
        intro i hi
        rw [hpres1 ((h + 1) + i)]
        have hidx : (h + 1) + i = h + (i + 1) := by omega
        rw [hidx]
        have hj := hmatch (i + 1) (by simp only [List.length_cons]; omega)
        rwa [List.getD_cons_succ] at hj
      obtain ⟨tp2, run2, hpres2⟩ := ih (s + 1) (h + 1) tp1 hcont
      refine ⟨tp2, ?_, fun q => (hpres2 q).trans (hpres1 q)⟩
      have comp := reachIn_seq _ _ _ _ _ _ _ run1 run2
      convert comp using 1
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; rw [Prod.mk.injEq, Prod.mk.injEq]
        exact ⟨by omega, by omega, rfl⟩

/-!
**The fixed-pattern matcher, proved.**  `matchPattern pat s F` chains `checkBit`s (failures to a common `F`) and
reaches the success state iff the tape matches the constant pattern `pat` — the first composite control-flow machine of
the matching half.  Next: the two-pointer comparison of two tape regions (both operands read from tape), the rule-table
scan-and-match loop, and the apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMatchPattern

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMMatchPattern.matchPattern_run_match
