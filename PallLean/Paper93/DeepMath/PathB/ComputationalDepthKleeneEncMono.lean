import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEncode

/-!
# Kleene interpreter project — `UCode.enc` subcode monotonicity (PROVED)

For a handler's sub-config to rank below the current one (`cfgRank_lt_code` needs `subcode-enc < code-enc`),
the tagged encoding must shrink on subcodes — the analogue of Mathlib's `encode_lt_*` for `UCode.enc`.

  `lt_pair_of_pos` — `Z < Nat.pair s Z` for `s ≥ 1` (the tag is `≥ 1` for every recursive constructor's
    payload-pairing... actually all tags `4..7 ≥ 1`).
  `enc_lt_pair_left/right`, `enc_lt_comp_left/right`, `enc_lt_prec_left/right`, `enc_lt_rfind'` — each subcode
    has strictly smaller `enc` than the parent.

## What is proved (clean axioms, no `sorry`)

* `lt_pair_of_pos` and the seven subcode-monotonicity lemmas.

## Honest scope

Subcode encoding monotonicity (so handler sub-configs rank lower).  The recursive handler Codes, the body,
the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

/-- `Z < Nat.pair s Z` for `s ≥ 1` (the pairing with a positive tag strictly grows). -/
theorem lt_pair_of_pos (s Z : ℕ) (hs : 1 ≤ s) : Z < Nat.pair s Z := by
  rw [Nat.pair]; split <;> nlinarith

theorem enc_lt_pair_left (a b : UCode) : a.enc < (UCode.pair a b).enc :=
  lt_of_le_of_lt (Nat.left_le_pair _ _) (lt_pair_of_pos 4 _ (by norm_num))
theorem enc_lt_pair_right (a b : UCode) : b.enc < (UCode.pair a b).enc :=
  lt_of_le_of_lt (Nat.right_le_pair _ _) (lt_pair_of_pos 4 _ (by norm_num))
theorem enc_lt_comp_left (a b : UCode) : a.enc < (UCode.comp a b).enc :=
  lt_of_le_of_lt (Nat.left_le_pair _ _) (lt_pair_of_pos 5 _ (by norm_num))
theorem enc_lt_comp_right (a b : UCode) : b.enc < (UCode.comp a b).enc :=
  lt_of_le_of_lt (Nat.right_le_pair _ _) (lt_pair_of_pos 5 _ (by norm_num))
theorem enc_lt_prec_left (a b : UCode) : a.enc < (UCode.prec a b).enc :=
  lt_of_le_of_lt (Nat.left_le_pair _ _) (lt_pair_of_pos 6 _ (by norm_num))
theorem enc_lt_prec_right (a b : UCode) : b.enc < (UCode.prec a b).enc :=
  lt_of_le_of_lt (Nat.right_le_pair _ _) (lt_pair_of_pos 6 _ (by norm_num))
theorem enc_lt_rfind' (a : UCode) : a.enc < (UCode.rfind' a).enc :=
  lt_pair_of_pos 7 _ (by norm_num)

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.enc_lt_pair_left
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.enc_lt_rfind'
