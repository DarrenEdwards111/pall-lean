import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3BitCompare

/-!
# Entry 405 — universal-TM-table build: the three-way field-loop body `fieldStep3` (proved)

`bitCompareAtDist3` (entry 404) compares the config-key bit at `p` with the rule-key bit at `p+d` and routes to a single
`sEq`/`sNe` pair — it tells you *whether the two bits agree*, but it collapses the two *agreeing* cases (`O,O` and `I,I`)
into one target.  For a field-compare loop that is not enough: when both bits are `O` the two unary fields have **ended
together** (a match — terminate success), whereas when both are `I` the fields **continue** (recurse to the next cell).
These need different control targets.

This brick is that refinement.  It reads the config bit (anchoring it via `markCarry3`, exactly as entry 404), then in
the `O`-lineage probes the rule bit against `O` and in the `I`-lineage probes it against `I`, but routes the two lineages
to *distinct* targets:

* config `O` (separator): rule `O` ⇒ `sMatch` (both fields ended), rule `I` ⇒ `sFail` (config shorter);
* config `I` (a one):     rule `I` ⇒ `sCont` (both continue), rule `O` ⇒ `sFail` (rule shorter).

So `fieldStep3` is the genuine **loop body**: one cell-pair of a field compare, deciding continue / match / fail, with
the tape restored exactly and the head left at the anchor `p` ready for the advance.  (`bitCompareAtDist3` is the special
case `sCont = sMatch = sEq`, `sFail = sNe`.)

## What is proved (clean axioms, no `sorry`)

* **`fieldStep3 s sCont sMatch sFail d`** — `markCarry3 s (s+1) (s+d+8) 0 ++ probe3 (s+1) sMatch sFail d O ++ probe3
  (s+d+8) sCont sFail d I`.
* **`fieldStep3_run`** (PROVED) — for a config-key bit cell (`tp.getD p O ∈ {O, I}`), `d ≥ 1`, no marker in `(p, p+d]`,
  `p`/`p+d` in bounds: routes to `sMatch`/`sCont`/`sFail` by the three-way rule above, head back at `p`, tape restored.

## Honest scope

This is the **field-loop body** — one verified cell-pair step with the continue/match/fail routing the loop needs.  It
does **not** yet advance the pointer, nor induct over the whole field, nor the rule-table match, nor the apply.  Building
those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldStep

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 readSym3 toNTM3 writeAt3 writeAt3_id_of_lt writeAt3_getD)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MarkCarry (markCarry3 markCarry3_run_O markCarry3_run_I)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Probe (probe3 probe3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteWrite (writeAt3_writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_append_right3)

/-- **The three-way field-loop body.**  Mark and carry the config bit, then probe the rule bit in the matching lineage,
routing config-`O` (separator) to `sMatch`/`sFail` and config-`I` (a one) to `sCont`/`sFail`. -/
def fieldStep3 (s sCont sMatch sFail d : ℕ) : TMachine3 :=
  markCarry3 s (s + 1) (s + d + 8) 0 ++ probe3 (s + 1) sMatch sFail d Sym3.O ++ probe3 (s + d + 8) sCont sFail d Sym3.I

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **The three-way field-loop body run (PROVED).**  Routes config-`O` to `sMatch` (rule `O`) / `sFail` (rule `I`) and
config-`I` to `sCont` (rule `I`) / `sFail` (rule `O`); head returns to `p`, tape restored. -/
theorem fieldStep3_run (s sCont sMatch sFail p d : ℕ) (tp : List Sym3)
    (hbit : tp.getD p Sym3.O = Sym3.O ∨ tp.getD p Sym3.O = Sym3.I) (hd : 1 ≤ d)
    (hno : ∀ k, 0 < k → k ≤ d → tp.getD (p + k) Sym3.O ≠ Sym3.M) (hp : p < tp.length) (hbound : p + d < tp.length) :
    ∃ N, reachIn (toNTM3 (fieldStep3 s sCont sMatch sFail d)) N (s, p, tp)
      ((if tp.getD p Sym3.O = Sym3.O
          then (if tp.getD (p + d) Sym3.O = Sym3.O then sMatch else sFail)
          else (if tp.getD (p + d) Sym3.O = Sym3.I then sCont else sFail)), p, tp) := by
  set MC := markCarry3 s (s + 1) (s + d + 8) 0 with hMC
  set PO := probe3 (s + 1) sMatch sFail d Sym3.O with hPO
  set PI := probe3 (s + d + 8) sCont sFail d Sym3.I with hPI
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
  rcases hbit with hb | hb
  · -- config bit is O: the O-lineage probe runs against the constant O, routing to sMatch / sFail
    rw [hb, if_pos rfl]
    have hmc := markCarry3_run_O s (s + 1) (s + d + 8) 0 p tp (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb])
    have hmc1 := reachIn_append_left3 MC PO 1 _ _ hmc
    have hmc2 := reachIn_append_left3 (MC ++ PO) PI 1 _ _ hmc1
    obtain ⟨N, hpr⟩ := probe3_run (s + 1) sMatch sFail p d Sym3.O tp' hmark hno' hbound'
    -- collapse the result tape: writeAt3 tp' p O = writeAt3 tp p O = tp
    rw [htp', writeAt3_writeAt3, show writeAt3 tp p Sym3.O = tp from by rw [← hb]; exact writeAt3_id_of_lt tp p hp] at hpr
    rw [hpd] at hpr
    have hpr1 := reachIn_append_right3 MC PO N _ _ hpr
    have hpr2 := reachIn_append_left3 (MC ++ PO) PI N _ _ hpr1
    refine ⟨1 + N, ?_⟩
    exact (reachIn_add (toNTM3 (MC ++ PO ++ PI)) 1 N _ _).mpr ⟨_, hmc2, hpr2⟩
  · -- config bit is I: the I-lineage probe runs against the constant I, routing to sCont / sFail
    rw [hb, if_neg (by decide)]
    have hmc := markCarry3_run_I s (s + 1) (s + d + 8) 0 p tp (by rw [show readSym3 (s, p, tp) = tp.getD p Sym3.O from rfl, hb])
    have hmc1 := reachIn_append_left3 MC PO 1 _ _ hmc
    have hmc2 := reachIn_append_left3 (MC ++ PO) PI 1 _ _ hmc1
    obtain ⟨N, hpr⟩ := probe3_run (s + d + 8) sCont sFail p d Sym3.I tp' hmark hno' hbound'
    rw [htp', writeAt3_writeAt3, show writeAt3 tp p Sym3.I = tp from by rw [← hb]; exact writeAt3_id_of_lt tp p hp] at hpr
    rw [hpd] at hpr
    have hpr1 := reachIn_append_right3 (MC ++ PO) PI N _ _ hpr
    refine ⟨1 + N, ?_⟩
    exact (reachIn_add (toNTM3 (MC ++ PO ++ PI)) 1 N _ _).mpr ⟨_, hmc2, hpr1⟩

/-!
**The three-way field-loop body, proved.**  `fieldStep3` decides one cell-pair of a unary field compare — continue
(`I,I`) / match (`O,O`) / fail (mismatch) — laying and clearing its own anchor and restoring the tape, head left at `p`.
Next: advance the head to `p+1` on the `sCont` path and induct over the field length to get the full `fieldCompare3`
loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldStep

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldStep.fieldStep3_run
