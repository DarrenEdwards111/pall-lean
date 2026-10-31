import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3FullLayout

/-!
# Entry 463 — universal-TM-table build: the config+rule region is marker-free `fullTape3_matcher_clean` (proved)

The matcher's **windowed cleanliness** on the stitched tape: every cell of the config region and the rule table (everything
after the home marker, before the simulated tape) is a bit (`O`/`I`), never the marker `M`.  So `matchTable3` (re-proved
windowed, à la entry 448) can walk the config+rules with a head marker `M` living *beyond* — in the simulated tape.

The region is bit-only because it is built entirely from `encodeNatBits3` (ones then `O`) and `boolToSym3` (`O`/`I`).

## What is proved (clean axioms, no `sorry`)

* **`allBits_getD_ne_M`** (PROVED) — an all-`O`/`I` list never reads `M`.
* **`encodeNatBits3_allBits`** / **`recordsTape3_allBits`** (PROVED) — the encodings are bit-only.
* **`configRules_clean`** (PROVED) — `0 < j → (cfgHead a cs ++ recordsTape3 rules).getD j O ≠ M`.
* **`fullTape3_matcher_clean`** (PROVED) — `0 < j → j < (cfgHead a cs ++ recordsTape3 rules).length → (fullTape3 a cs
  rules simtape).getD j O ≠ M` (the matcher's window on the full tape is marker-free, allowing the head marker beyond).

## Honest scope

This is the matcher's **windowed cleanliness** on the full tape.  It does **not** yet re-prove `matchTable3` windowed, nor
define the bit-decoding `φ` / `U` / `EmitsEncodedStepEx3` (the large but obstruction-free remaining assembly, per entry
456).  Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RegionClean

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config (configEncode3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordsLayout (recordsTape3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullLayout (cfgHead fullTape3 fullTape3_eq_cfgHead)

/-- **An all-bit list never reads the marker (PROVED).** -/
theorem allBits_getD_ne_M (l : List Sym3) (hl : ∀ x ∈ l, x = Sym3.O ∨ x = Sym3.I) (j : ℕ) :
    l.getD j Sym3.O ≠ Sym3.M := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[j]? with _ | x
  · decide
  · rcases hl x (List.mem_of_getElem? h) with hx | hx <;> rw [hx] <;> decide

/-- **`encodeNatBits3` is bit-only (PROVED).** -/
theorem encodeNatBits3_allBits (n : ℕ) : ∀ x ∈ encodeNatBits3 n, x = Sym3.O ∨ x = Sym3.I := by
  intro x hx
  rw [encodeNatBits3, List.mem_append] at hx
  rcases hx with hx | hx
  · right; exact List.eq_of_mem_replicate hx
  · left; simpa using hx

/-- **The rule table is bit-only (PROVED).** -/
theorem recordsTape3_allBits : ∀ (rules : List (ℕ × Bool)) (x : Sym3), x ∈ recordsTape3 rules → x = Sym3.O ∨ x = Sym3.I := by
  intro rules
  induction rules with
  | nil => intro x hx; simp [recordsTape3] at hx
  | cons r rest ih =>
      intro x hx
      rw [show recordsTape3 (r :: rest) = configEncode3 r.1 r.2 (recordsTape3 rest) from rfl, configEncode3,
        List.mem_append, List.mem_cons] at hx
      rcases hx with hx | hx | hx
      · exact encodeNatBits3_allBits r.1 x hx
      · subst hx; cases r.2 <;> simp [boolToSym3]
      · exact ih x hx

/-- **`configEncode3` preserves bit-only-ness (PROVED).** -/
theorem configEncode3_allBits (a : ℕ) (cs : Bool) (X : List Sym3) (hX : ∀ x ∈ X, x = Sym3.O ∨ x = Sym3.I) :
    ∀ x ∈ configEncode3 a cs X, x = Sym3.O ∨ x = Sym3.I := by
  intro x hx
  rw [configEncode3, List.mem_append, List.mem_cons] at hx
  rcases hx with hx | hx | hx
  · exact encodeNatBits3_allBits a x hx
  · subst hx; cases cs <;> simp [boolToSym3]
  · exact hX x hx

/-- **The config + rule region is marker-free after the home marker (PROVED).** -/
theorem configRules_clean (a : ℕ) (cs : Bool) (rules : List (ℕ × Bool)) (j : ℕ) (hj : 0 < j) :
    (cfgHead a cs ++ recordsTape3 rules).getD j Sym3.O ≠ Sym3.M := by
  have heq : cfgHead a cs ++ recordsTape3 rules = Sym3.M :: configEncode3 a cs (recordsTape3 rules) := by
    rw [cfgHead, configEncode3]; simp [List.append_assoc]
  rw [heq, show j = (j - 1) + 1 from by omega, List.getD_cons_succ]
  exact allBits_getD_ne_M _ (configEncode3_allBits a cs (recordsTape3 rules) (recordsTape3_allBits rules)) (j - 1)

/-- **The matcher's window on the full tape is marker-free (PROVED).** -/
theorem fullTape3_matcher_clean (a : ℕ) (cs : Bool) (rules : List (ℕ × Bool)) (simtape : List Sym3) (j : ℕ)
    (hj0 : 0 < j) (hj : j < (cfgHead a cs ++ recordsTape3 rules).length) :
    (fullTape3 a cs rules simtape).getD j Sym3.O ≠ Sym3.M := by
  rw [fullTape3_eq_cfgHead, ← List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left hj,
    ← List.getD_eq_getElem?_getD]
  exact configRules_clean a cs rules j hj0

/-!
**The config+rule region is marker-free, proved.**  The matcher's window on the stitched tape contains no marker (the head
marker lives beyond, in the simulated tape) — exactly the windowed cleanliness the matcher needs.  Next: re-prove
`matchTable3` windowed, define the bit-decoding `φ`, and assemble `U` toward `EmitsEncodedStepEx3` — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RegionClean

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RegionClean.fullTape3_matcher_clean
