import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Probe
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MarkCarry
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteWrite

/-!
# Entry 404 — universal-TM-table build: the self-contained single-bit compare `bitCompareAtDist3` (proved)

`probe3` (entry 403) compares the config-key bit at `p` with the rule-key bit at `p+d`, but *assumes* the anchor `M` is
already at `p` and the original bit `b` carried in the control state.  This brick prepends the `markCarry3` that
establishes both: it reads the config-key bit at `p` into the control-state lineage (`O`- vs `I`-lineage), lays the anchor
`M`, and feeds each lineage into the matching `probe3` (testing against `O` resp. `I`).  The result is a self-contained
single-bit comparison `tp[p]` vs `tp[p+d]` that lays and clears its own anchor and **restores the tape exactly**.

## What is proved (clean axioms, no `sorry`)

* **`bitCompareAtDist3 s sEq sNe d`** — `markCarry3 s (s+1) (s+d+8) 0 ++ probe3 (s+1) sEq sNe d O ++ probe3 (s+d+8) sEq
  sNe d I`.
* **`bitCompareAtDist3_run`** (PROVED) — for a config-key bit cell (`tp.getD p O ∈ {O, I}`), with `d ≥ 1`, no marker in
  `(p, p+d]`, and `p+d` in bounds: `∃ N, reachIn (toNTM3 (bitCompareAtDist3 …)) N (s, p, tp) ((if tp.getD (p+d) O =
  tp.getD p O then sEq else sNe), p, tp)` — routes to `sEq` iff the two bits agree, tape fully restored.

## Honest scope

This is the **self-contained single-bit compare** — `probe3` with its own anchor management.  It does **not** yet loop
over a whole key field, nor the rule-table match, nor the apply.  Building those fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3BitCompare

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 readSym3 toNTM3 writeAt3 writeAt3_id_of_lt writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkCarry (markCarry3 markCarry3_run_O markCarry3_run_I)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Probe (probe3 probe3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteWrite (writeAt3_writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The self-contained single-bit compare.**  Mark and carry the config bit, then probe the rule bit in the matching
lineage. -/
def bitCompareAtDist3 (s sEq sNe d : ℕ) : TMachine3 :=
  markCarry3 s (s + 1) (s + d + 8) 0 ++ probe3 (s + 1) sEq sNe d Sym3.O ++ probe3 (s + d + 8) sEq sNe d Sym3.I

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **The self-contained single-bit compare run (PROVED).**  Routes to `sEq` iff `tp[p] = tp[p+d]`, tape restored. -/
theorem bitCompareAtDist3_run (s sEq sNe p d : ℕ) (tp : List Sym3)
    (hbit : tp.getD p Sym3.O = Sym3.O ∨ tp.getD p Sym3.O = Sym3.I) (hd : 1 ≤ d)
    (hno : ∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O ≠ Sym3.M) (hp : p < tp.length) (hbound : p + d < tp.length) :
    ∃ N, reachIn (toNTM3 (bitCompareAtDist3 s sEq sNe d)) N (s, p, tp)
      ((if tp.getD (p + d) Sym3.O = tp.getD p Sym3.O then sEq else sNe), p, tp) := by
  set MC := markCarry3 s (s + 1) (s + d + 8) 0 with hMC
  set PO := probe3 (s + 1) sEq sNe d Sym3.O with hPO
  set PI := probe3 (s + d + 8) sEq sNe d Sym3.I with hPI
  -- abbreviations for the marked tape and the facts probe3 needs about it
  set tp' := writeAt3 tp p Sym3.M with htp'
  have hlen' : tp'.length = tp.length := writeAt3_length_eq tp p Sym3.M hp
  have hmark : tp'.getD p Sym3.O = Sym3.M := by rw [htp', writeAt3_getD]; simp
  have hno' : ∀ k, 0 < k → k ≤ d → tp'.getD (p + k) Sym3.O ≠ Sym3.M := by
    intro k hk0 hkd
    rw [htp', writeAt3_getD, if_neg (by omega)]; exact hno k hk0 hkd
  have hbound' : p + d < tp'.length := by rw [hlen']; exact hbound
  have hpd : tp'.getD (p + d) Sym3.O = tp.getD (p + d) Sym3.O := by
    rw [htp', writeAt3_getD, if_neg (by omega)]
  -- in either lineage, probe3 restores `tp'` at `p` to the original bit, collapsing the double write back to `tp`
  rcases hbit with hb | hb
  · -- config bit is O: the O-lineage probe runs against the constant O
    have hmc := markCarry3_run_O s (s + 1) (s + d + 8) 0 p tp (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb])
    have hmc1 := reachIn_append_left3 MC PO 1 _ _ hmc
    have hmc2 := reachIn_append_left3 (MC ++ PO) PI 1 _ _ hmc1
    obtain ⟨N, hpr⟩ := probe3_run (s + 1) sEq sNe p d Sym3.O tp' hmark hno' hbound'
    -- collapse the result tape: writeAt3 tp' p O = writeAt3 tp p O = tp
    rw [htp', writeAt3_writeAt3, show writeAt3 tp p Sym3.O = tp from by rw [← hb]; exact writeAt3_id_of_lt tp p hp] at hpr
    rw [hpd] at hpr
    have hpr1 := reachIn_append_right3 MC PO N _ _ hpr
    have hpr2 := reachIn_append_left3 (MC ++ PO) PI N _ _ hpr1
    refine ⟨1 + N, ?_⟩
    rw [hb]
    exact (reachIn_add (toNTM3 (MC ++ PO ++ PI)) 1 N _ _).mpr ⟨_, hmc2, hpr2⟩
  · -- config bit is I: the I-lineage probe runs against the constant I
    have hmc := markCarry3_run_I s (s + 1) (s + d + 8) 0 p tp (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb])
    have hmc1 := reachIn_append_left3 MC PO 1 _ _ hmc
    have hmc2 := reachIn_append_left3 (MC ++ PO) PI 1 _ _ hmc1
    obtain ⟨N, hpr⟩ := probe3_run (s + d + 8) sEq sNe p d Sym3.I tp' hmark hno' hbound'
    rw [htp', writeAt3_writeAt3, show writeAt3 tp p Sym3.I = tp from by rw [← hb]; exact writeAt3_id_of_lt tp p hp] at hpr
    rw [hpd] at hpr
    have hpr1 := reachIn_append_right3 (MC ++ PO) PI N _ _ hpr
    refine ⟨1 + N, ?_⟩
    rw [hb]
    exact (reachIn_add (toNTM3 (MC ++ PO ++ PI)) 1 N _ _).mpr ⟨_, hmc2, hpr1⟩

/-!
**The self-contained single-bit compare, proved.**  `bitCompareAtDist3` lays its own anchor (`markCarry3`), routes the
carried bit into the matching `probe3` lineage, and restores the tape — a clean two-input bit comparison at an arbitrary
distance.  Next: loop it over a whole unary key field, comparing the config key against a rule key bit by bit — fragment
by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3BitCompare

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3BitCompare.bitCompareAtDist3_run
