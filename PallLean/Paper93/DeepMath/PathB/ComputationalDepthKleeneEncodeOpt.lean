import Mathlib

/-!
# Kleene interpreter project — the Option encoding + pair identity (PROVED)

The table cells hold `evaln`'s `Option ℕ` results encoded as `ℕ` (`encodeOpt`: `none = 0`, `some v = v+1`).
The handlers' branch-free multiplicative form is justified by pure `Option`↔arithmetic identities; this file
proves the `pair` one (the others — `guard`-only base, `comp`, `prec`/`rfind'` — follow the same pattern).

  `encodeOpt` — `none ↦ 0`, `some v ↦ v+1`.
  `encode_pair_step` — `encodeOpt (if n ≤ k then (Nat.pair <$> oa <*> ob) else none) = [n≤k] · isPos(encodeOpt
    oa) · isPos(encodeOpt ob) · (Nat.pair (encodeOpt oa - 1) (encodeOpt ob - 1) + 1)` — exactly the `pair`
    handler's multiplicative computation, matching `evalnStep`'s `pair` case (encoded).

So once the handler's `Code` computes that multiplicative form (with `ea = encodeOpt (evaln a)` read via
`lookupSubCode`), its value is `encodeOpt (evalnStep … (pair a b) n)` — i.e. `spec N`.

## What is proved (clean axioms, no `sorry`)

* `encodeOpt`, `encode_pair_step`.

## Honest scope

The Option encoding + the `pair` identity.  The `pair` handler `Code` (computing this), the other identities,
the handlers, the body, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

/-- Option-as-ℕ encoding: `none = 0`, `some v = v + 1`. -/
def encodeOpt : Option ℕ → ℕ
  | none => 0
  | some v => v + 1

/-- **`pair` handler identity (proved): encoded `evalnStep` pair-result = the multiplicative form.** -/
theorem encode_pair_step (k n : ℕ) (oa ob : Option ℕ) :
    encodeOpt (if n ≤ k then (Nat.pair <$> oa <*> ob) else none)
      = (if n ≤ k then 1 else 0) * ((if encodeOpt oa = 0 then 0 else 1)
          * ((if encodeOpt ob = 0 then 0 else 1)
              * (Nat.pair (encodeOpt oa - 1) (encodeOpt ob - 1) + 1))) := by
  by_cases h : n ≤ k
  · rw [if_pos h, if_pos h, one_mul]
    cases oa <;> cases ob <;> simp [encodeOpt, Seq.seq, Functor.map, Nat.add_sub_cancel]
  · rw [if_neg h, if_neg h, zero_mul, encodeOpt]

/-!
**Option encoding + pair identity proved.**  The `pair` handler's multiplicative form equals the encoded
`evalnStep` pair-result.  The handler `Code`, the other identities, the body, the interpreter, and the
runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.encode_pair_step
