import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEncode

/-!
# Kleene interpreter project — step 5 (data layer): tag/subcode extraction as Codes (PROVED)

The dispatch (step 5) splits into a **data layer** (extract the constructor tag and subcode encodings from
an encoded code) and a **control layer** (the 8-way branch + double recursion).  This file builds the data
layer: the extractions are realized as concrete `Code`s and proved correct against the tagged encoding
`UCode.enc`.

  `tagCode := Code.left` — `tagCode.eval u.enc = (unpair u.enc).1` = the constructor tag.
  `fstSubCode := Code.comp Code.left Code.right` — recovers the first subcode's encoding.
  `sndSubCode := Code.comp Code.right Code.right` — recovers the second subcode's encoding.

So the interpreter's "read the constructor, recover the subcodes" is concrete `Code` arithmetic
(`left`/`right`/`comp`), proved against `UCode.enc` — and each has a fuel bound from `ACC0EffSimCodeFuel`
(`left`/`right` are `≤ n+1`; `comp` via `runtimeOf_comp_le`).

## What is proved (clean axioms, no `sorry`)

* `tagCode`/`fstSubCode`/`sndSubCode` + their `eval`-correctness on `UCode.enc` (tag; subcodes for
  `pair`/`comp`/`prec`).

## Honest scope

The dispatch **data layer** (extraction as Codes).  The **control layer** — the 8-way branch on the tag
and the double recursion (`prec`-on-fuel + structural-on-code) realized as one `Code` — is the indivisible
hard core (step 5 proper), not built here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- The tag-extraction code (`= Code.left`): reads the constructor tag. -/
def tagCode : Code := Code.left

/-- The first-subcode extraction code. -/
def fstSubCode : Code := Code.comp Code.left Code.right

/-- The second-subcode extraction code. -/
def sndSubCode : Code := Code.comp Code.right Code.right

/-- **Tag extraction (proved): `tagCode.eval u.enc = (unpair u.enc).1`.** -/
theorem eval_tagCode (u : UCode) : tagCode.eval u.enc = Part.some (Nat.unpair u.enc).1 := by
  simp [tagCode, Code.eval]

/-- **First-subcode extraction for `pair` (proved).** -/
theorem eval_fstSub_pair (a b : UCode) :
    fstSubCode.eval (UCode.pair a b).enc = Part.some a.enc := by
  simp [fstSubCode, Code.eval, UCode.enc, Nat.unpair_pair]

/-- **Second-subcode extraction for `pair` (proved).** -/
theorem eval_sndSub_pair (a b : UCode) :
    sndSubCode.eval (UCode.pair a b).enc = Part.some b.enc := by
  simp [sndSubCode, Code.eval, UCode.enc, Nat.unpair_pair]

/-- **First-subcode extraction for `comp` (proved).** -/
theorem eval_fstSub_comp (a b : UCode) :
    fstSubCode.eval (UCode.comp a b).enc = Part.some a.enc := by
  simp [fstSubCode, Code.eval, UCode.enc, Nat.unpair_pair]

/-- **Second-subcode extraction for `comp` (proved).** -/
theorem eval_sndSub_comp (a b : UCode) :
    sndSubCode.eval (UCode.comp a b).enc = Part.some b.enc := by
  simp [sndSubCode, Code.eval, UCode.enc, Nat.unpair_pair]

/-- **First-subcode extraction for `prec` (proved).** -/
theorem eval_fstSub_prec (a b : UCode) :
    fstSubCode.eval (UCode.prec a b).enc = Part.some a.enc := by
  simp [fstSubCode, Code.eval, UCode.enc, Nat.unpair_pair]

/-- **Second-subcode extraction for `prec` (proved).** -/
theorem eval_sndSub_prec (a b : UCode) :
    sndSubCode.eval (UCode.prec a b).enc = Part.some b.enc := by
  simp [sndSubCode, Code.eval, UCode.enc, Nat.unpair_pair]

/-!
**Step 5 data layer proved.**  The dispatch's tag and subcode extractions are concrete `Code`s
(`left`/`right`/`comp`) proved correct against `UCode.enc`, each with a fuel bound from the EffSim
primitives.  The control layer (8-way branch + double recursion as one `Code`) is the indivisible hard core
that remains.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_tagCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_fstSub_prec
