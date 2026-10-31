import Mathlib

/-!
# Interpreter grind, value-bound (code component): subcodes are encoding-bounded (PROVED)

The value-bound for a universal interpreter has three components: the **fuel** stays `≤ s`, the **input**
`< fuel` (both from `Nat.Partrec.Code.evaln_bound`), and the **code** the interpreter visits is a *subcode*
of the input — encoding-bounded.  This file proves the code component as a clean standalone fact.

`IsSubcode c' c` is the reflexive/transitive "structural subterm" relation on `Code`.  Mathlib's
per-constructor bounds (`encode_lt_comp/pair/prec/rfind'`) lift to:

  `encode_le_of_isSubcode` — `IsSubcode c' c → Encodable.encode c' ≤ Encodable.encode c`.

So as a universal interpreter recurses into the subterms of an input code `c₀`, every code it handles has
encoding `≤ encode c₀` — the code component of every config it manipulates is bounded by the input.  With
`evaln_bound` (fuel/input components), this is the full value-bound's data; combining them into a config
size bound is part of the interpreter construction.

## What is proved (clean axioms, no `sorry`)

* `IsSubcode` — the structural subterm relation on `Code`.
* `IsSubcode.trans` — transitivity.
* `encode_le_of_isSubcode` — subcodes are encoding-bounded by the parent.

## Honest scope

The **code component** of the value-bound (subcodes bounded).  The fuel/input components are Mathlib's
`evaln_bound`; assembling all three into the interpreter's config-size bound is part of the interpreter
construction (the remaining grind).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimSubcodeBound

open Nat.Partrec Nat.Partrec.Code

/-- The reflexive/transitive structural-subterm relation on `Code`. -/
inductive IsSubcode : Code → Code → Prop
  | refl (c : Code) : IsSubcode c c
  | comp_left {c cf cg : Code} : IsSubcode c cf → IsSubcode c (Code.comp cf cg)
  | comp_right {c cf cg : Code} : IsSubcode c cg → IsSubcode c (Code.comp cf cg)
  | pair_left {c cf cg : Code} : IsSubcode c cf → IsSubcode c (Code.pair cf cg)
  | pair_right {c cf cg : Code} : IsSubcode c cg → IsSubcode c (Code.pair cf cg)
  | prec_left {c cf cg : Code} : IsSubcode c cf → IsSubcode c (Code.prec cf cg)
  | prec_right {c cf cg : Code} : IsSubcode c cg → IsSubcode c (Code.prec cf cg)
  | rfind {c cf : Code} : IsSubcode c cf → IsSubcode c (Code.rfind' cf)

/-- **Subcodes are encoding-bounded by the parent (proved).** -/
theorem encode_le_of_isSubcode {c' c : Code} (h : IsSubcode c' c) :
    Encodable.encode c' ≤ Encodable.encode c := by
  induction h with
  | refl => exact le_refl _
  | comp_left _ ih => exact le_trans ih (le_of_lt (encode_lt_comp _ _).1)
  | comp_right _ ih => exact le_trans ih (le_of_lt (encode_lt_comp _ _).2)
  | pair_left _ ih => exact le_trans ih (le_of_lt (encode_lt_pair _ _).1)
  | pair_right _ ih => exact le_trans ih (le_of_lt (encode_lt_pair _ _).2)
  | prec_left _ ih => exact le_trans ih (le_of_lt (encode_lt_prec _ _).1)
  | prec_right _ ih => exact le_trans ih (le_of_lt (encode_lt_prec _ _).2)
  | rfind _ ih => exact le_trans ih (le_of_lt (encode_lt_rfind' _))

/-- **Transitivity of `IsSubcode` (proved).** -/
theorem IsSubcode.trans {a b c : Code} (hab : IsSubcode a b) (hbc : IsSubcode b c) : IsSubcode a c := by
  induction hbc with
  | refl => exact hab
  | comp_left _ ih => exact IsSubcode.comp_left ih
  | comp_right _ ih => exact IsSubcode.comp_right ih
  | pair_left _ ih => exact IsSubcode.pair_left ih
  | pair_right _ ih => exact IsSubcode.pair_right ih
  | prec_left _ ih => exact IsSubcode.prec_left ih
  | prec_right _ ih => exact IsSubcode.prec_right ih
  | rfind _ ih => exact IsSubcode.rfind ih

/-!
**Value-bound code component proved.**  Every subcode of `c₀` is encoding-bounded by `c₀`, so a universal
interpreter recursing into `c₀`'s subterms only handles codes `≤ encode c₀`.  With `evaln_bound` (fuel ≤ s,
input < fuel) this is the value-bound's data; the config-size bound combining them is part of the
interpreter construction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimSubcodeBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimSubcodeBound.encode_le_of_isSubcode
