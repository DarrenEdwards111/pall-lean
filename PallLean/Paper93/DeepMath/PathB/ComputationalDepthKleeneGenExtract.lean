import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispatch
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDecodeU

/-!
# Kleene interpreter project — general subcode extraction + bounds (PROVED)

The handler lemmas were keyed on *valid* codes (`ec = enc u`).  For `hbody` we need them for *any* `ec`
(the table includes malformed configs).  These lemmas extract subcodes from an arbitrary number and bound
them `< ec` (whenever the tag is positive), exactly what the generic readers (`reader_correct`, etc.) need in
place of `eval_fstSub_pair` + `enc_lt_*`.

  `eval_fstSub_gen`/`eval_sndSub_gen` — `fstSubCode/sndSubCode ec = (unpair (unpair ec).2).1/.2` (any `ec`).
  `fstSub_lt`/`sndSub_lt`/`rfindSub_lt` — those subcodes (and `(unpair ec).2`) are `< ec` when `1 ≤ tag`.

## What is proved (clean axioms, no `sorry`)

* `eval_fstSub_gen`, `eval_sndSub_gen`, `fstSub_lt`, `sndSub_lt`, `rfindSub_lt`.

## Honest scope

General extraction/bounds.  The generic handlers, `hbody`, the interpreter, and the runtime remain.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

theorem eval_fstSub_gen (ec : ℕ) : fstSubCode.eval ec = Part.some (Nat.unpair (Nat.unpair ec).2).1 := by
  show (Code.comp Code.left Code.right).eval ec = _; simp [Code.eval]

theorem eval_sndSub_gen (ec : ℕ) : sndSubCode.eval ec = Part.some (Nat.unpair (Nat.unpair ec).2).2 := by
  show (Code.comp Code.right Code.right).eval ec = _; simp [Code.eval]

theorem fstSub_lt (ec : ℕ) (h : 1 ≤ (Nat.unpair ec).1) : (Nat.unpair (Nat.unpair ec).2).1 < ec := by
  have hp := unpair_right_lt_of_fst ec h; have := Nat.unpair_left_le (Nat.unpair ec).2; omega

theorem sndSub_lt (ec : ℕ) (h : 1 ≤ (Nat.unpair ec).1) : (Nat.unpair (Nat.unpair ec).2).2 < ec := by
  have hp := unpair_right_lt_of_fst ec h; have := Nat.unpair_right_le (Nat.unpair ec).2; omega

theorem rfindSub_lt (ec : ℕ) (h : 1 ≤ (Nat.unpair ec).1) : (Nat.unpair ec).2 < ec :=
  unpair_right_lt_of_fst ec h

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_fstSub_gen
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.fstSub_lt
