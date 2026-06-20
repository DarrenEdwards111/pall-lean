import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ProbeTail

/-!
# Entry 403 — universal-TM-table build: the single-bit compare-after-mark `probe3` (proved)

This is the heart of the marker route: a **distance-independent single-bit comparison**.  Given that the anchor marker
`M` already sits at the config-key cell `p` (laid by `markCarry3`, which simultaneously carried the original bit `b` into
the control state), `probe3` walks right `d` cells to the rule-key cell `p+d`, tests it against the carried constant `b`,
walks back to the anchor (distance-independently, via `seekMarkLeft`), and restores the anchor to `b`.  It routes to `sEq`
if the rule-key cell equalled `b`, else `sNe`.

The construction is a *branch*: `testBit3` routes to one of two tails (`probeTail3`), only one of which executes on any
run.  The machine statically contains both; each run traverses one.  We lift each sub-machine's run to the union with the
monotonicity lemmas (`reachIn_append_left3`/`reachIn_append_right3`) and chain with `reachIn_add`.

## What is proved (clean axioms, no `sorry`)

* **`probe3 s sEq sNe d b`** — `moveRightN3 s d ++ testBit3 (s+d) (s+d+1) (s+d+2) b ++ probeTail3 (s+d+1) (s+d+3) (s+d+4)
  sEq b ++ probeTail3 (s+d+2) (s+d+5) (s+d+6) sNe b`.
* **`probe3_run`** (PROVED) — with the anchor at `p` (`tp.getD p O = M`), no marker in `(p, p+d]`, and `p+d` in bounds:
  `∃ N, reachIn (toNTM3 (probe3 …)) N (s, p, tp) ((if tp.getD (p+d) O = b then sEq else sNe), p, writeAt3 tp p b)` —
  the head returns to the anchor `p`, restores it to `b`, and the control routes on whether the distant cell equalled `b`.

## Honest scope

This is the **single-bit compare** — the genuine crux of the marker route's data-vs-data comparison.  It does **not** yet
prepend the `markCarry3` that lays the anchor and carries `b`, nor loop over a whole key, nor the rule-table match.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Probe

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 readSym3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MoveN (moveRightN3 moveRightN3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3TestBit (testBit3 testBit3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ProbeTail (probeTail3 probeTail3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The single-bit compare-after-mark.**  Walk out `d`, test against `b`, return to the anchor and restore it. -/
def probe3 (s sEq sNe d : ℕ) (b : Sym3) : TMachine3 :=
  moveRightN3 s d ++ testBit3 (s + d) (s + d + 1) (s + d + 2) b ++
    probeTail3 (s + d + 1) (s + d + 3) (s + d + 4) sEq b ++
    probeTail3 (s + d + 2) (s + d + 5) (s + d + 6) sNe b

/-- **The single-bit compare run (PROVED).**  Returns to the anchor `p` restoring it to `b`, routed on `tp[p+d] = b`. -/
theorem probe3_run (s sEq sNe p d : ℕ) (b : Sym3) (tp : List Sym3)
    (hmark : tp.getD p Sym3.O = Sym3.M) (hno : ∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O ≠ Sym3.M)
    (hbound : p + d < tp.length) :
    ∃ N, reachIn (toNTM3 (probe3 s sEq sNe d b)) N (s, p, tp)
      ((if tp.getD (p + d) Sym3.O = b then sEq else sNe), p, writeAt3 tp p b) := by
  -- the four sub-machines, in the left-associated nesting of `probe3`
  set A := moveRightN3 s d with hA
  set B := testBit3 (s + d) (s + d + 1) (s + d + 2) b with hB
  set C := probeTail3 (s + d + 1) (s + d + 3) (s + d + 4) sEq b with hC
  set D := probeTail3 (s + d + 2) (s + d + 5) (s + d + 6) sNe b with hD
  -- outbound move, lifted to the union
  have rA := moveRightN3_run s d p tp (by omega)
  have rA1 := reachIn_append_left3 A B d _ _ rA
  have rA2 := reachIn_append_left3 (A ++ B) C d _ _ rA1
  have rA3 := reachIn_append_left3 (A ++ B ++ C) D d _ _ rA2
  -- the test, lifted to the union
  have rB := testBit3_run (s + d) (s + d + 1) (s + d + 2) (p + d) tp b (by omega)
  rw [show readSym3 (s + d, p + d, tp) = tp.getD (p + d) Sym3.O from rfl] at rB
  have rB1 := reachIn_append_right3 A B 1 _ _ rB
  have rB2 := reachIn_append_left3 (A ++ B) C 1 _ _ rB1
  have rB3 := reachIn_append_left3 (A ++ B ++ C) D 1 _ _ rB2
  by_cases hcond : tp.getD (p + d) Sym3.O = b
  · -- equal: the eq-tail executes
    rw [if_pos hcond] at rB3 ⊢
    obtain ⟨Nc, hc⟩ := probeTail3_run (s + d + 1) (s + d + 3) (s + d + 4) sEq p d b tp hmark hno hbound
    have hc1 := reachIn_append_right3 (A ++ B) C Nc _ _ hc
    have hc2 := reachIn_append_left3 (A ++ B ++ C) D Nc _ _ hc1
    have step1 := (reachIn_add (toNTM3 (A ++ B ++ C ++ D)) d 1 _ _).mpr ⟨_, rA3, rB3⟩
    exact ⟨d + 1 + Nc, (reachIn_add (toNTM3 (A ++ B ++ C ++ D)) (d + 1) Nc _ _).mpr ⟨_, step1, hc2⟩⟩
  · -- unequal: the ne-tail executes
    rw [if_neg hcond] at rB3 ⊢
    obtain ⟨Nd, hd⟩ := probeTail3_run (s + d + 2) (s + d + 5) (s + d + 6) sNe p d b tp hmark hno hbound
    have hd1 := reachIn_append_right3 (A ++ B ++ C) D Nd _ _ hd
    have step1 := (reachIn_add (toNTM3 (A ++ B ++ C ++ D)) d 1 _ _).mpr ⟨_, rA3, rB3⟩
    exact ⟨d + 1 + Nd, (reachIn_add (toNTM3 (A ++ B ++ C ++ D)) (d + 1) Nd _ _).mpr ⟨_, step1, hd1⟩⟩

/-!
**The single-bit compare, proved.**  `probe3` realises the marker route's distance-independent data-vs-data comparison:
the anchor makes the return trip free of any step count.  Next: prepend `markCarry3` (lay the anchor, carry `b`) to get a
self-contained bit compare, then loop it over a whole key field — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Probe

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Probe.probe3_run
