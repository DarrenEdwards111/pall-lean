import Mathlib

/-!
# Kleene universal interpreter project — phase 1: the mirror code `UCode` (PROVED)

Dedicated project (per the roadmap): build a concrete `Nat.Partrec.Code` program `U` with
`U.eval (encConfig k c n) = Code.evaln k c n` and an exposed polynomial runtime bound (via the EffSim
machinery already built).

**Phase 1 (this file): a mirror encoding.**  Rather than destruct Mathlib's `encodeCode` (a `brecOn`
recursion), introduce a clean inductive `UCode` mirroring `Code`'s eight constructors, with a faithful
bridge `UCode ≃ Code`.  The dispatch (later phases) will operate on `UCode`'s clean recursive structure;
the bridge transfers everything to/from Mathlib `Code`.

  `UCode` — the mirror inductive (`zero/succ/left/right/pair/comp/prec/rfind'`).
  `UCode.toCode` / `UCode.ofCode` — the bridge to/from Mathlib `Code`.
  `toCode_ofCode` / `ofCode_toCode` — round-trips, so `UCode ≃ Code` (faithful representation).
  `UCode.equivCode` — the packaged equivalence.

## Project plan (roadmap)

1. **Mirror code + bridge** (this file).
2. Arithmetic/code primitive library (fst/snd, ifz, tag/subcode extraction) — extends `ACC0EffSimCodeFuel`.
3. One-step evaluator `stepConfig` as a pure function, proved to match one `evaln` unfolding.
4. `stepConfig` as a `Code` (the dispatch brick).
5. Wrap with `prec` on fuel ⇒ the universal `Code`; runtime via `runtimeOf_prec_le_linear`.
6. Value bound via `config_encode_le` ⇒ polynomial step body ⇒ `DiagRuntimePolyBounded`.

## What is proved (clean axioms, no `sorry`)

* `UCode`, `toCode`, `ofCode`, `toCode_ofCode`, `ofCode_toCode`, `equivCode` — the faithful mirror.

## Honest scope

Phase 1 only: the mirror encoding `UCode ≃ Code`.  The interpreter itself (phases 2–6) is the construction
ahead.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Mirror of `Nat.Partrec.Code`: a clean inductive over the eight constructors, for building the
interpreter's dispatch without fighting `encodeCode`. -/
inductive UCode where
  | zero : UCode
  | succ : UCode
  | left : UCode
  | right : UCode
  | pair : UCode → UCode → UCode
  | comp : UCode → UCode → UCode
  | prec : UCode → UCode → UCode
  | rfind' : UCode → UCode
  deriving DecidableEq, Inhabited

/-- Bridge to Mathlib `Code`. -/
def UCode.toCode : UCode → Code
  | .zero => Code.zero
  | .succ => Code.succ
  | .left => Code.left
  | .right => Code.right
  | .pair a b => Code.pair a.toCode b.toCode
  | .comp a b => Code.comp a.toCode b.toCode
  | .prec a b => Code.prec a.toCode b.toCode
  | .rfind' a => Code.rfind' a.toCode

/-- Bridge from Mathlib `Code`. -/
def UCode.ofCode : Code → UCode
  | Code.zero => .zero
  | Code.succ => .succ
  | Code.left => .left
  | Code.right => .right
  | Code.pair a b => .pair (UCode.ofCode a) (UCode.ofCode b)
  | Code.comp a b => .comp (UCode.ofCode a) (UCode.ofCode b)
  | Code.prec a b => .prec (UCode.ofCode a) (UCode.ofCode b)
  | Code.rfind' a => .rfind' (UCode.ofCode a)

/-- **Round-trip `Code → UCode → Code` (proved).** -/
theorem toCode_ofCode (c : Code) : (UCode.ofCode c).toCode = c := by
  induction c with
  | pair a b iha ihb => simp [UCode.ofCode, UCode.toCode, iha, ihb]
  | comp a b iha ihb => simp [UCode.ofCode, UCode.toCode, iha, ihb]
  | prec a b iha ihb => simp [UCode.ofCode, UCode.toCode, iha, ihb]
  | rfind' a iha => simp [UCode.ofCode, UCode.toCode, iha]
  | _ => rfl

/-- **Round-trip `UCode → Code → UCode` (proved).** -/
theorem ofCode_toCode (u : UCode) : UCode.ofCode u.toCode = u := by
  induction u with
  | pair a b iha ihb => simp [UCode.toCode, UCode.ofCode, iha, ihb]
  | comp a b iha ihb => simp [UCode.toCode, UCode.ofCode, iha, ihb]
  | prec a b iha ihb => simp [UCode.toCode, UCode.ofCode, iha, ihb]
  | rfind' a iha => simp [UCode.toCode, UCode.ofCode, iha]
  | _ => rfl

/-- **`UCode ≃ Code` (proved): the mirror faithfully represents every code.** -/
def UCode.equivCode : UCode ≃ Code where
  toFun := UCode.toCode
  invFun := UCode.ofCode
  left_inv := ofCode_toCode
  right_inv := toCode_ofCode

/-!
**Phase 1 proved.**  `UCode ≃ Code` — a clean mirror inductive faithfully representing every code, the base
for the interpreter's dispatch (phases 2–6).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.toCode_ofCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.ofCode_toCode
